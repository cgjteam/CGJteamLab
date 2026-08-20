import CGJteamLab.Proposition35
import CGJteamLab.MidsegmentParallel

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

theorem i37_nondegenerate_triangles
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C) :
    And
      (Not (Collinear Geo A B C))
      (And
        (Not (Collinear Geo D B C))
        (Not (Collinear Geo B A D))) := by

  have hBC : Not (B = C) :=
    hAD_BC.2.1

  have hAD : Not (A = D) :=
    hAD_BC.1

  --------------------------------------------------------------------
  -- A and D are off the base line BC.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo A D B C hAD_BC
    with
    ⟨base, hBbase, hCbase, hADsame⟩

  have hBCA :
      Not (Collinear Geo B C A) :=
    hilbert_not_collinear_of_off_line
      Geo B C A base hBC
      hBbase hCbase hADsame.1

  have hBCD :
      Not (Collinear Geo B C D) :=
    hilbert_not_collinear_of_off_line
      Geo B C D base hBC
      hBbase hCbase hADsame.2.1

  have hABC :
      Not (Collinear Geo A B C) := by
    intro h
    exact
      hBCA
        (PrimCollinearCycle
          Geo A B C h)

  have hDBC :
      Not (Collinear Geo D B C) := by
    intro h
    exact
      hBCD
        (PrimCollinearCycle
          Geo D B C h)

  --------------------------------------------------------------------
  -- B is off the upper line AD.
  --------------------------------------------------------------------

  have hBC_AD :
      Geo.Parallel B C A D :=
    ParallelSymmetry
      Geo A D B C hAD_BC

  rcases
      parallel_endpoints_sameSide
        Geo B C A D hBC_AD
    with
    ⟨top, hAtop, hDtop, hBCsame⟩

  have hADB :
      Not (Collinear Geo A D B) :=
    hilbert_not_collinear_of_off_line
      Geo A D B top hAD
      hAtop hDtop hBCsame.1

  have hBAD :
      Not (Collinear Geo B A D) := by
    intro h
    exact
      hADB
        (PrimCollinearCycle
          Geo B A D h)

  exact
    And.intro
      hABC
      (And.intro hDBC hBAD)

theorem i37_half_parallelograms
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C) :
    exists M N P Q F G : Geo.Point,
      HilbertIsMidpoint Geo M B A /\
      HilbertIsMidpoint Geo N C A /\
      HilbertIsMidpoint Geo P B D /\
      HilbertIsMidpoint Geo Q C D /\
      IsParallelogram Geo B C F M /\
      IsParallelogram Geo B C G P /\
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C A)
        (hilbertParallelogramTerm Geo B C F M) /\
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C D)
        (hilbertParallelogramTerm Geo B C G P) /\
      Geo.Parallel M P A D := by

  --------------------------------------------------------------------
  -- Nondegenerate triangles.
  --------------------------------------------------------------------

  rcases
      i37_nondegenerate_triangles
        Geo A B C D hAD_BC
    with
    ⟨hABC, hDBC, hBAD⟩

  --------------------------------------------------------------------
  -- Endpoint distinctness.
  --------------------------------------------------------------------

  have hAB : Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC : Not (A = C) :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate
            Geo A C B h))

  have hDB : Not (D = B) :=
    hilbert_noncollinear_ne_first
      Geo D B C hDBC

  have hDC : Not (D = C) :=
    hilbert_noncollinear_ne_first
      Geo D C B
      (fun h =>
        hDBC
          (PrimCollinearRotate
            Geo D C B h))

  have hBA : Not (B = A) := by
    intro h
    exact hAB h.symm

  have hCA : Not (C = A) := by
    intro h
    exact hAC h.symm

  have hBD : Not (B = D) := by
    intro h
    exact hDB h.symm

  have hCD : Not (C = D) := by
    intro h
    exact hDC h.symm

  --------------------------------------------------------------------
  -- Four midpoints.
  --
  -- M midpoint BA
  -- N midpoint CA
  -- P midpoint BD
  -- Q midpoint CD
  --------------------------------------------------------------------

  rcases
      HilbertMidpointExists
        Geo B A hBA
    with
    ⟨M, hM⟩

  rcases
      HilbertMidpointExists
        Geo C A hCA
    with
    ⟨N, hN⟩

  rcases
      HilbertMidpointExists
        Geo B D hBD
    with
    ⟨P, hP⟩

  rcases
      HilbertMidpointExists
        Geo C D hCD
    with
    ⟨Q, hQ⟩

  --------------------------------------------------------------------
  -- Triangle BCA.
  --
  -- For the noncollinearity condition of Hilbert 45 we regard
  -- M,N as the midpoints of AB,AC.
  --------------------------------------------------------------------

  have hMAB :
      HilbertIsMidpoint Geo M A B :=
    MidpointSymmetry
      Geo M B A hM

  have hNAC :
      HilbertIsMidpoint Geo N A C :=
    MidpointSymmetry
      Geo N C A hN

  have hNMA :
      Not (Collinear Geo N M A) :=
    hilbert_midpoints_noncollinear
      Geo A B C M N
      hMAB
      hNAC
      hABC

  rcases
      hilbert_triangle_to_parallelogram
        Geo
        B C A M N
        hM hN hNMA
    with
    ⟨F, hBCFM, hScA⟩

  --------------------------------------------------------------------
  -- Triangle BCD.
  --------------------------------------------------------------------

  have hPDB :
      HilbertIsMidpoint Geo P D B :=
    MidpointSymmetry
      Geo P B D hP

  have hQDC :
      HilbertIsMidpoint Geo Q D C :=
    MidpointSymmetry
      Geo Q C D hQ

  have hQPD :
      Not (Collinear Geo Q P D) :=
    hilbert_midpoints_noncollinear
      Geo D B C P Q
      hPDB
      hQDC
      hDBC

  rcases
      hilbert_triangle_to_parallelogram
        Geo
        B C D P Q
        hP hQ hQPD
    with
    ⟨G, hBCGP, hScD⟩

  --------------------------------------------------------------------
  -- M and P are corresponding midpoints in triangle BAD.
  --
  -- Therefore MP is parallel to AD.
  --------------------------------------------------------------------

  have hPMB :
      Not (Collinear Geo P M B) :=
    hilbert_midpoints_noncollinear
      Geo B A D M P
      hM
      hP
      hBAD

  have hMP_AD :
      Geo.Parallel M P A D :=
    MidsegmentTheorem
      Geo
      B A D M P
      hM
      hP
      hPMB

  exact
    ⟨M, N, P, Q, F, G,
      hM, hN, hP, hQ,
      hBCFM, hBCGP,
      hScA, hScD,
      hMP_AD⟩

theorem i37_upper_line
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hM : HilbertIsMidpoint Geo M B A)
    (hBCFM : IsParallelogram Geo B C F M)
    (hBCGP : IsParallelogram Geo B C G P)
    (hMP_AD : Geo.Parallel M P A D) :
    Geo.Parallel M P B C /\
    Collinear Geo M F P /\
    Collinear Geo M P G := by

  --------------------------------------------------------------------
  -- M does not lie on BC.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo A D B C hAD_BC
    with
    ⟨base, hBbase, hCbase, hADsame⟩

  have hBM :
      Not (B = M) :=
    (HilbertOrder.between_incidence
      B M A hM.left).1

  have hBMA :
      Collinear Geo B M A :=
    (HilbertOrder.between_incidence
      B M A hM.left).2.2.2.1

  have hMoff :
      Not (HilbertIncidence.OnLine M base) := by

    intro hMbase

    have hAbase :
        HilbertIncidence.OnLine A base :=
      hilbert_collinear_on_line
        Geo B M A base
        hBM
        hBbase
        hMbase
        hBMA

    exact hADsame.1 hAbase

  --------------------------------------------------------------------
  -- MP and BC are distinct point-lines.
  --------------------------------------------------------------------

  have hMP_ne_BC :
      Geo.PointLine M P ≠ Geo.PointLine B C := by

    intro hEq

    have hM_MP :
        M ∈ Geo.PointLine M P := by
      change Geometry.Geo.LineCollinear Geo M P M
      exact Or.inr (Or.inl rfl)

    rw [hEq] at hM_MP

    have hMbase :
        HilbertIncidence.OnLine M base :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C M base
        hAD_BC.2.1
        hBbase
        hCbase).mp hM_MP

    exact hMoff hMbase

  --------------------------------------------------------------------
  -- MP || BC because MP || AD and BC || AD.
  --------------------------------------------------------------------

  have hBC_AD :
      Geo.Parallel B C A D :=
    ParallelSymmetry
      Geo A D B C hAD_BC

  have hMP_ne_BC :
      Not (Geo.PointLine M P = Geo.PointLine B C) := by

    intro hEq

    have hM_MP :
        M ∈ Geo.PointLine M P := by
      change Geometry.Geo.LineCollinear Geo M P M
      exact Or.inr (Or.inl rfl)

    rw [hEq] at hM_MP

    have hMbase :
        HilbertIncidence.OnLine M base :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C M base
        hAD_BC.2.1
        hBbase
        hCbase).mp hM_MP

    exact hMoff hMbase

  have hMP_BC :
      Geo.Parallel M P B C :=
    hilbert_parallel_transitive_distinct
      Geo
      M P
      B C
      A D
      hMP_AD
      hBC_AD
      hMP_ne_BC

  --------------------------------------------------------------------
  -- FM || BC and GP || BC from the two parallelograms.
  --------------------------------------------------------------------

  have hFM_BC :
      Geo.Parallel F M B C :=
    ParallelSymmetry
      Geo B C F M hBCFM.1

  have hGP_BC :
      Geo.Parallel G P B C :=
    ParallelSymmetry
      Geo B C G P hBCGP.1

  --------------------------------------------------------------------
  -- FM and MP are the same line.
  --
  -- If they were distinct, transitivity of parallels would make
  -- them parallel to each other, impossible because they share M.
  --------------------------------------------------------------------

  have hFM_eq_MP :
      Geo.PointLine F M =
      Geo.PointLine M P := by

    by_contra hNe

    have hFM_MP :
        Geo.Parallel F M M P :=
      hilbert_parallel_transitive_distinct
        Geo
        F M
        M P
        B C
        hFM_BC
        hMP_BC
        hNe

    have hM_FM :
        M ∈ Geo.PointLine F M := by
      change Geometry.Geo.LineCollinear Geo F M M
      exact Or.inr (Or.inr (Or.inl rfl))

    have hM_MP :
        M ∈ Geo.PointLine M P := by
      change Geometry.Geo.LineCollinear Geo M P M
      exact Or.inr (Or.inl rfl)

    exact
      Set.disjoint_left.mp
        hFM_MP.2.2
        hM_FM
        hM_MP

  --------------------------------------------------------------------
  -- Hence M,F,P are collinear.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        M P hMP_BC.1
    with
    ⟨midline, hMmid, hPmid⟩

  have hF_FM :
      F ∈ Geo.PointLine F M := by
    change Geometry.Geo.LineCollinear Geo F M F
    exact Or.inr (Or.inl rfl)

  rw [hFM_eq_MP] at hF_FM

  have hFmid :
      HilbertIncidence.OnLine F midline :=
    (hilbert_mem_pointLine_iff_onLine
      Geo M P F midline
      hMP_BC.1
      hMmid
      hPmid).mp hF_FM

  have hMFP :
      Collinear Geo M F P :=
    ⟨midline, hMmid, hFmid, hPmid⟩

  --------------------------------------------------------------------
  -- GP and MP are likewise the same line.
  --------------------------------------------------------------------

  have hGP_eq_MP :
      Geo.PointLine G P =
      Geo.PointLine M P := by

    by_contra hNe

    have hGP_MP :
        Geo.Parallel G P M P :=
      hilbert_parallel_transitive_distinct
        Geo
        G P
        M P
        B C
        hGP_BC
        hMP_BC
        hNe

    have hP_GP :
        P ∈ Geo.PointLine G P := by
      change Geometry.Geo.LineCollinear Geo G P P
      exact Or.inr (Or.inr (Or.inl rfl))

    have hP_MP :
        P ∈ Geo.PointLine M P := by
      change Geometry.Geo.LineCollinear Geo M P P
      exact Or.inr (Or.inr (Or.inl rfl))

    exact
      Set.disjoint_left.mp
        hGP_MP.2.2
        hP_GP
        hP_MP

  --------------------------------------------------------------------
  -- Hence M,P,G are collinear.
  --------------------------------------------------------------------

  have hG_GP :
      G ∈ Geo.PointLine G P := by
    change Geometry.Geo.LineCollinear Geo G P G
    exact Or.inr (Or.inl rfl)

  rw [hGP_eq_MP] at hG_GP

  have hGmid :
      HilbertIncidence.OnLine G midline :=
    (hilbert_mem_pointLine_iff_onLine
      Geo M P G midline
      hMP_BC.1
      hMmid
      hPmid).mp hG_GP

  have hMPG :
      Collinear Geo M P G :=
    ⟨midline, hMmid, hPmid, hGmid⟩

  exact
    ⟨hMP_BC, hMFP, hMPG⟩

theorem i37_upper_sides_congruent
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C M P F G : Geo.Point)
    (hBCFM : IsParallelogram Geo B C F M)
    (hBCGP : IsParallelogram Geo B C G P) :
    Geo.Congruent M F P G := by

  have hSides1 :=
    ParallelogramOppositeSidesCongruent
      Geo B C F M hBCFM

  have hSides2 :=
    ParallelogramOppositeSidesCongruent
      Geo B C G P hBCGP

  have hMF_BC :
      Geo.Congruent M F B C := by
    exact
      CongruentReverseFirst
        Geo F M B C
        (CongruentSymmetry
          Geo B C F M hSides1.1)

  have hBC_PG :
      Geo.Congruent B C P G :=
    CongruentSwapSecond
      Geo B C G P hSides2.1

  exact
    hilbert_congruent_transitivity
      Geo M F B C P G
      hMF_BC
      hBC_PG

theorem i37_parallelogram_reduction
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C) :
    exists M P F G : Geo.Point,
      IsParallelogram Geo M B C F /\
      IsParallelogram Geo P B C G /\
      Geo.Parallel M P B C /\
      Collinear Geo M F P /\
      Collinear Geo M P G /\
      Geo.Congruent M F P G /\
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F) /\
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G) := by

  rcases
      i37_half_parallelograms
        Geo A B C D hAD_BC
    with
    ⟨M, N, P, Q, F, G,
      hM, hN, hP, hQ,
      hBCFM, hBCGP,
      hScA, hScD,
      hMP_AD⟩

  --------------------------------------------------------------------
  -- Rotate the two parallelograms so that BC is the common base
  -- in the exact orientation expected by Proposition I.35.
  --------------------------------------------------------------------

  have hMBCF :
      IsParallelogram Geo M B C F :=
    ParallelogramRotateOne
      Geo B C F M hBCFM

  have hPBCG :
      IsParallelogram Geo P B C G :=
    ParallelogramRotateOne
      Geo B C G P hBCGP

  --------------------------------------------------------------------
  -- Common upper line.
  --------------------------------------------------------------------

  rcases
      i37_upper_line
        Geo
        A B C D
        M P F G
        hAD_BC
        hM
        hBCFM
        hBCGP
        hMP_AD
    with
    ⟨hMP_BC, hMFP, hMPG⟩

  --------------------------------------------------------------------
  -- The two upper sides are congruent.
  --------------------------------------------------------------------

  have hMF_PG :
      Geo.Congruent M F P G :=
    i37_upper_sides_congruent
      Geo B C M P F G
      hBCFM hBCGP

  --------------------------------------------------------------------
  -- Rotate the formal parallelogram terms.
  --------------------------------------------------------------------

  have hRotA :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C F M)
        (hilbertParallelogramTerm Geo M B C F) :=
    parallelogram_term_rotateOne
      Geo B C F M hBCFM

  have hRotD :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C G P)
        (hilbertParallelogramTerm Geo P B C G) :=
    parallelogram_term_rotateOne
      Geo B C G P hBCGP

  --------------------------------------------------------------------
  -- Triangle ABC -> MBCF.
  --------------------------------------------------------------------

  have hScArot :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C A)
        (hilbertParallelogramTerm Geo M B C F) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hScA
      hRotA

  have hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F) := by
    rw [scissors_triangle_cycle Geo A B C]
    exact hScArot

  --------------------------------------------------------------------
  -- Triangle DBC -> PBCG.
  --------------------------------------------------------------------

  have hScDrot :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C D)
        (hilbertParallelogramTerm Geo P B C G) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hScD
      hRotD

  have hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G) := by
    rw [scissors_triangle_cycle Geo D B C]
    exact hScDrot

  exact
    ⟨M, P, F, G,
      hMBCF,
      hPBCG,
      hMP_BC,
      hMFP,
      hMPG,
      hMF_PG,
      hABC,
      hDBC⟩

theorem i37_finish_from_right_cases
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F))
    (hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G))
    (hCases : I35RightCases Geo M F P G) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  have hParallelograms :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo P B C G) :=
    i35_from_three_cases
      Geo
      M B C F P G
      hMBCF
      hPBCG
      hCases

  exact
    equicomplementable_transport
      Geo
      hABC
      hDBC
      hParallelograms

theorem i37_finish_same_left_vertex
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F))
    (hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G))
    (hMP : M = P) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  subst P

  have hFG :
      F = G :=
    ParallelogramFourthVertexUnique
      Geo
      M B C F G
      hMBCF
      hPBCG

  subst G

  have hPar :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo M B C F) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo M B C F)

  exact
    equicomplementable_transport
      Geo
      hABC
      hDBC
      hPar

theorem i37_finish_common_upper_endpoint
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F))
    (hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G))
    (hFP : F = P) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  subst P

  have hPar :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo F B C G) :=
    i35_common_endpoint
      Geo
      M B C F G
      hMBCF
      hPBCG

  exact
    equicomplementable_transport
      Geo
      hABC
      hDBC
      hPar

theorem i37_upper_trichotomy
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C M P F : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hMFP : Collinear Geo M F P)
    (hMP : Not (M = P))
    (hFP : Not (F = P)) :
    Geo.Between M F P \/
    Geo.Between F M P \/
    Geo.Between M P F := by

  have hFM :
      Not (F = M) :=
    hMBCF.2.2.1

  have hMF :
      Not (M = F) := by
    intro h
    exact hFM h.symm

  exact
    hilbert_between_trichotomy
      Geo
      M F P
      hMF
      hFP
      hMP
      hMFP

theorem i37_finish_order_FMP
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hMPG : Collinear Geo M P G)
    (hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F))
    (hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G))
    (hFMP : Geo.Between F M P) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  --------------------------------------------------------------------
  -- Recover the common upper-line collinearity F-G-P.
  --------------------------------------------------------------------

  have hFMPData :=
    HilbertOrder.between_incidence
      F M P hFMP

  have hMP :
      Not (M = P) :=
    hFMPData.2.1

  have hPM :
      Not (P = M) := by
    intro h
    exact hMP h.symm

  have hFMPcol :
      Collinear Geo F M P :=
    hFMPData.2.2.2.1

  have hFPM :
      Collinear Geo F P M :=
    PrimCollinearRotate
      Geo F M P hFMPcol

  have hPMG :
      Collinear Geo P M G :=
    PrimCollinearSwap
      Geo M P G hMPG

  have hFPG :
      Collinear Geo F P G :=
    hilbert_primCollinear_trans
      Geo
      F P M G
      hPM
      hFPM
      hPMG

  have hFGP :
      Collinear Geo F G P :=
    PrimCollinearRotate
      Geo F P G hFPG

  --------------------------------------------------------------------
  -- Reverse both parallelograms:
  --
  --   M-B-C-F  ->  F-C-B-M
  --   P-B-C-G  ->  G-C-B-P
  --
  -- They now have common base CB, and F-M-P is exactly the
  -- order hypothesis required by Proposition I.35.
  --------------------------------------------------------------------

  have hBMFCrev :
      IsParallelogram Geo B M F C :=
    ParallelogramReverse
      Geo M B C F hMBCF

  have hCBMF :
      IsParallelogram Geo C B M F :=
    ParallelogramRotateOne
      Geo B M F C hBMFCrev

  have hFCBM :
      IsParallelogram Geo F C B M :=
    ParallelogramRotateOne
      Geo C B M F hCBMF

  have hBPGCrev :
      IsParallelogram Geo B P G C :=
    ParallelogramReverse
      Geo P B C G hPBCG

  have hCBPG :
      IsParallelogram Geo C B P G :=
    ParallelogramRotateOne
      Geo B P G C hBPGCrev

  have hGCBP :
      IsParallelogram Geo G C B P :=
    ParallelogramRotateOne
      Geo C B P G hCBPG

  --------------------------------------------------------------------
  -- The corresponding scissors terms differ only by representation.
  --------------------------------------------------------------------

  have hRevM :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo B M F C) :=
    parallelogram_term_reverse
      Geo M B C F hMBCF

  have hRotM :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B M F C)
        (hilbertParallelogramTerm Geo F C B M) :=
    parallelogram_term_rotateTwo
      Geo B M F C

  have hTermM :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo F C B M) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRevM
      hRotM

  have hRevP :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo P B C G)
        (hilbertParallelogramTerm Geo B P G C) :=
    parallelogram_term_reverse
      Geo P B C G hPBCG

  have hRotP :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B P G C)
        (hilbertParallelogramTerm Geo G C B P) :=
    parallelogram_term_rotateTwo
      Geo B P G C

  have hTermP :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo P B C G)
        (hilbertParallelogramTerm Geo G C B P) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRevP
      hRotP

  --------------------------------------------------------------------
  -- Euclid I.35 on the reversed configuration.
  --------------------------------------------------------------------

  have hI35 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F C B M)
        (hilbertParallelogramTerm Geo G C B P) :=
    euclid_proposition_35
      Geo
      F C B M G P
      hFCBM
      hGCBP
      hFMP
      hFGP

  --------------------------------------------------------------------
  -- Return first to the original parallelograms, then to the triangles.
  --------------------------------------------------------------------

  have hPar :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo P B C G) :=
    equicomplementable_transport
      Geo
      hTermM
      hTermP
      hI35

  exact
    equicomplementable_transport
      Geo
      hABC
      hDBC
      hPar

theorem i37_finish_order_MFP
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hMPG : Collinear Geo M P G)
    (hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F))
    (hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G))
    (hMFP : Geo.Between M F P)
    (hFPG : Geo.Between F P G) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  have hOrder :=
    hilbert_between_outer_trans
      Geo
      M F P G
      hMFP
      hFPG

  have hMFG :
      Geo.Between M F G :=
    hOrder.2

  have hPar :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo P B C G) :=
    euclid_proposition_35
      Geo
      M B C F P G
      hMBCF
      hPBCG
      hMFG
      hMPG

  exact
    equicomplementable_transport
      Geo
      hABC
      hDBC
      hPar

theorem i37_order_MFP_implies_FPG
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hMPG : Collinear Geo M P G)
    (hMFP : Geo.Between M F P) :
    Geo.Between F P G := by

  have hMFPData :=
    HilbertOrder.between_incidence
      M F P hMFP

  have hMF : M ≠ F :=
    hMFPData.1

  have hFP : F ≠ P :=
    hMFPData.2.1

  have hMP : M ≠ P :=
    hMFPData.2.2.1

  have hPM : P ≠ M :=
    hMP.symm

  have hPF : P ≠ F :=
    hFP.symm

  have hMFPcol :
      Collinear Geo M F P :=
    hMFPData.2.2.2.1

  have hPFM :
      Geo.Between P F M :=
    hMFPData.2.2.2.2

  --------------------------------------------------------------------
  -- The upper line MF and the base BC.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo B C F M hMBCF.2
    with
    ⟨lineFM, hFfm, hMfm, hBCsame⟩

  have hBoffFM :
      ¬ HilbertIncidence.OnLine B lineFM :=
    hBCsame.1

  have hFMPcol :
      Collinear Geo F M P :=
    PrimCollinearSwap
      Geo M F P hMFPcol

  have hFPMcol :
      Collinear Geo F P M :=
    PrimCollinearRotate
      Geo F M P hFMPcol

  have hPfm :
      HilbertIncidence.OnLine P lineFM :=
    hilbert_collinear_on_line
      Geo F M P lineFM
      hMF.symm
      hFfm hMfm
      hFMPcol

  have hPMB :
      ¬ Collinear Geo P M B :=
    hilbert_not_collinear_of_off_line
      Geo P M B lineFM
      hPM
      hPfm hMfm
      hBoffFM

  --------------------------------------------------------------------
  -- The side CF.  It cuts PM at F.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo M B C F hMBCF.1
    with
    ⟨lineCF, hCcf, hFcf, hMBsame⟩

  have hMoffCF :
      ¬ HilbertIncidence.OnLine M lineCF :=
    hMBsame.1

  have hBoffCF :
      ¬ HilbertIncidence.OnLine B lineCF :=
    hMBsame.2.1

  have hPoffCF :
      ¬ HilbertIncidence.OnLine P lineCF := by
    intro hPcf

    have hLineEq :
        lineFM = lineCF :=
      HilbertPlaneIncidence.line_unique
        F P hFP
        lineFM lineCF
        hFfm hPfm
        hFcf hPcf

    have hMcf :
        HilbertIncidence.OnLine M lineCF := by
      rw [← hLineEq]
      exact hMfm

    exact hMoffCF hMcf

  have hMeetsPM :
      HilbertSegmentMeetsLine Geo P M lineCF :=
    ⟨F, hPFM, hFcf⟩

  --------------------------------------------------------------------
  -- Pasch in triangle P-M-B.
  --
  -- line CF enters through PM at F.  It cannot leave through MB,
  -- because MB || CF.  Hence it meets PB.
  --------------------------------------------------------------------

  have hMB :
      M ≠ B :=
    hMBCF.1.1

  have hCF :
      C ≠ F :=
    hMBCF.1.2.1

  rcases
      HilbertPlaneIncidence.line_through
        M B hMB
    with
    ⟨lineMB, hMmb, hBmb⟩

  have hLinesMB_CF :
      HilbertLinesDisjoint Geo lineMB lineCF := by
    rintro ⟨X, hXmb, hXcf⟩

    have hXMB :
        X ∈ Geo.PointLine M B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo M B X lineMB
        hMB hMmb hBmb).mpr hXmb

    have hXCF :
        X ∈ Geo.PointLine C F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C F X lineCF
        hCF hCcf hFcf).mpr hXcf

    exact
      Set.disjoint_left.mp
        hMBCF.1.2.2
        hXMB
        hXCF

  have hNotMeetsMB :
      ¬ HilbertSegmentMeetsLine Geo M B lineCF := by
    rintro ⟨X, hMXB, hXcf⟩

    have hXmb :
        HilbertIncidence.OnLine X lineMB :=
      hilbert_between_on_line
        Geo M X B lineMB
        hMmb hBmb hMXB

    exact
      hLinesMB_CF
        ⟨X, hXmb, hXcf⟩

  have hPasch :=
    HilbertOrder.pasch
      (Geo := Geo)
      P M B
      hPMB
      lineCF
      hPoffCF
      hMoffCF
      hBoffCF
      hMeetsPM

  have hMeetsPB :
      HilbertSegmentMeetsLine Geo P B lineCF := by
    rcases hPasch with hPB | hMBmeet
    · exact hPB
    · exact False.elim (hNotMeetsMB hMBmeet)

  rcases hMeetsPB with
    ⟨Q, hPQB, hQcf⟩

  --------------------------------------------------------------------
  -- Q actually lies between F and C.
  --
  -- PF || CB and Q lies on both PB and FC.
  --------------------------------------------------------------------

  have hFM_BC :
      Geo.Parallel F M B C :=
    ParallelSymmetry
      Geo B C F M hMBCF.2

  have hMF_BC :
      Geo.Parallel M F B C :=
    ParallelSwapFirstLine
      Geo F M B C hFM_BC

  have hPMF :
      Collinear Geo P M F :=
    PrimCollinearRotate
      Geo P F M
      (PrimCollinearSymm
        Geo M F P hMFPcol)

  have hPF_BC :
      Geo.Parallel P F B C :=
    ParallelCollinearLeft
      Geo M F P B C
      hPF
      hMF_BC
      hPMF

  have hPF_CB :
      Geo.Parallel P F C B :=
    ParallelSwapSecondLine
      Geo P F B C hPF_BC

  have hFCQ :
      Collinear Geo F C Q :=
    ⟨lineCF, hFcf, hCcf, hQcf⟩

  have hFQC :
      Geo.Between F Q C :=
    hilbert_collinear_between_of_parallel
      Geo
      P F C B Q
      hPF_CB
      hPQB
      hFCQ

  --------------------------------------------------------------------
  -- In the second parallelogram C and G lie on the same side of PB.
  --------------------------------------------------------------------

  have hCG_PB :
      Geo.Parallel C G P B :=
    ParallelSymmetry
      Geo P B C G hPBCG.1

  rcases
      parallel_endpoints_sameSide
        Geo C G P B hCG_PB
    with
    ⟨linePB, hPpb, hBpb, hCGsame⟩

  have hQpb :
      HilbertIncidence.OnLine Q linePB :=
    hilbert_between_on_line
      Geo P Q B linePB
      hPpb hBpb hPQB

  have hCoffPB :
      ¬ HilbertIncidence.OnLine C linePB :=
    hCGsame.1

  have hFQCData :=
    HilbertOrder.between_incidence
      F Q C hFQC

  have hFQ :
      F ≠ Q :=
    hFQCData.1

  have hFQCcol :
      Collinear Geo F Q C :=
    hFQCData.2.2.2.1

  have hFoffPB :
      ¬ HilbertIncidence.OnLine F linePB := by
    intro hFpb

    have hCpb :
        HilbertIncidence.OnLine C linePB :=
      hilbert_collinear_on_line
        Geo F Q C linePB
        hFQ
        hFpb hQpb
        hFQCcol

    exact hCoffPB hCpb

  have hOppFC :
      HilbertOppositeSide Geo F C linePB :=
    ⟨hFoffPB,
     hCoffPB,
     ⟨Q, hFQC, hQpb⟩⟩

  have hOppFG :
      HilbertOppositeSide Geo F G linePB :=
    hilbert_oppositeSide_transport_right
      Geo
      F C G linePB
      hOppFC
      hCGsame

  --------------------------------------------------------------------
  -- Therefore segment FG crosses PB.
  -- Since P is already the common point of the two lines,
  -- the crossing point must be P.
  --------------------------------------------------------------------

  rcases hOppFG.2.2 with
    ⟨X, hFXG, hXpb⟩

  have hPMG' :
      Collinear Geo P M G :=
    PrimCollinearSwap
      Geo M P G hMPG

  have hFPG :
      Collinear Geo F P G :=
    hilbert_primCollinear_trans
      Geo
      F P M G
      hPM
      hFPMcol
      hPMG'

  have hFXGData :=
    HilbertOrder.between_incidence
      F X G hFXG

  have hFG :
      F ≠ G :=
    hFXGData.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        F G hFG
    with
    ⟨lineFG, hFfg, hGfg⟩

  have hFGP :
      Collinear Geo F G P :=
    PrimCollinearRotate
      Geo F P G hFPG

  have hPfg :
      HilbertIncidence.OnLine P lineFG :=
    hilbert_collinear_on_line
      Geo F G P lineFG
      hFG
      hFfg hGfg
      hFGP

  have hXfg :
      HilbertIncidence.OnLine X lineFG :=
    hilbert_between_on_line
      Geo F X G lineFG
      hFfg hGfg hFXG

  have hLines :
      lineFG ≠ linePB := by
    intro hEq
    have hFpb :
        HilbertIncidence.OnLine F linePB := by
      rw [← hEq]
      exact hFfg
    exact hFoffPB hFpb

  have hPX :
      P = X := by
    exact
      (hilbert_common_point_unique
        Geo
        lineFG linePB
        hLines
        P X
        hPfg hPpb
        hXfg hXpb).symm

  subst X

  exact hFXG

theorem i37_order_MPF_implies_PFG
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hMPG : Collinear Geo M P G)
    (hMPF : Geo.Between M P F) :
    Geo.Between P F G := by

  have hMPFData :=
    HilbertOrder.between_incidence
      M P F hMPF

  have hMP : M ≠ P :=
    hMPFData.1

  have hPF : P ≠ F :=
    hMPFData.2.1

  have hMF : M ≠ F :=
    hMPFData.2.2.1

  have hPM : P ≠ M :=
    hMP.symm

  have hFP : F ≠ P :=
    hPF.symm

  have hMPFcol :
      Collinear Geo M P F :=
    hMPFData.2.2.2.1

  have hFPM :
      Geo.Between F P M :=
    hMPFData.2.2.2.2

  --------------------------------------------------------------------
  -- All four upper points lie on the same line.
  --------------------------------------------------------------------

  have hFPMcol :
      Collinear Geo F P M :=
    PrimCollinearSymm
      Geo M P F hMPFcol

  have hPMG :
      Collinear Geo P M G :=
    PrimCollinearSwap
      Geo M P G hMPG

  have hFPGcol :
      Collinear Geo F P G :=
    hilbert_primCollinear_trans
      Geo
      F P M G
      hPM
      hFPMcol
      hPMG

  have hPFGcol :
      Collinear Geo P F G :=
    PrimCollinearSwap
      Geo F P G hFPGcol

  --------------------------------------------------------------------
  -- MF and PG are congruent opposite sides.
  --------------------------------------------------------------------

  have hBCFM :
      IsParallelogram Geo B C F M := by
    have h1 :
        IsParallelogram Geo F M B C :=
      ParallelogramRotateOne
        Geo M B C F hMBCF

    have h2 :
        IsParallelogram Geo C F M B :=
      ParallelogramRotateOne
        Geo F M B C h1

    exact
      ParallelogramRotateOne
        Geo C F M B h2

  have hBCGP :
      IsParallelogram Geo B C G P := by
    have h1 :
        IsParallelogram Geo G P B C :=
      ParallelogramRotateOne
        Geo P B C G hPBCG

    have h2 :
        IsParallelogram Geo C G P B :=
      ParallelogramRotateOne
        Geo G P B C h1

    exact
      ParallelogramRotateOne
        Geo C G P B h2

  have hMF_PG :
      Geo.Congruent M F P G :=
    i37_upper_sides_congruent
      Geo B C M P F G
      hBCFM hBCGP

  --------------------------------------------------------------------
  -- F and G are distinct.
  --
  -- Otherwise PF would be congruent to the whole FM, although
  -- F-P-M makes PF a proper part of FM.
  --------------------------------------------------------------------

  have hFG :
      F ≠ G := by
    intro h
    subst G

    have hFP_lt_FM :
        HilbertSegmentLess Geo F P F M :=
      hilbert_segmentLess_of_between
        Geo F P M hFPM

    have hFM_PF :
        Geo.Congruent F M P F :=
      CongruentReverseFirst
        Geo M F P F hMF_PG

    have hPF_FM :
        Geo.Congruent P F F M :=
      hilbert_congruent_symmetry
        Geo F M P F hFM_PF

    have hFP_FM :
        Geo.Congruent F P F M :=
      CongruentReverseFirst
        Geo P F F M hPF_FM

    exact
      (hilbert_segmentLess_not_congruent
        Geo F P F M hFP_lt_FM)
        hFP_FM

  have hGP :
      G ≠ P :=
    hPBCG.2.2.1

  have hPG :
      P ≠ G :=
    hGP.symm

  --------------------------------------------------------------------
  -- Trichotomy on P,F,G.
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        P F G
        hPF
        hFG
        hPG
        hPFGcol
    with
    hPFG | hFPG | hPGF

  --------------------------------------------------------------------
  -- Desired case.
  --------------------------------------------------------------------

  · exact hPFG

  --------------------------------------------------------------------
  -- Impossible case: F-P-G.
  --
  -- Reverse both parallelograms:
  --
  --   MBCF -> FCBM
  --   PBCG -> GCBP
  --
  -- Then G-P-F is precisely the M-F-P configuration already
  -- handled by i37_order_MFP_implies_FPG.
  --------------------------------------------------------------------

  · have hBMFC :
        IsParallelogram Geo B M F C :=
      ParallelogramReverse
        Geo M B C F hMBCF

    have hCBMF :
        IsParallelogram Geo C B M F :=
      ParallelogramRotateOne
        Geo B M F C hBMFC

    have hFCBM :
        IsParallelogram Geo F C B M :=
      ParallelogramRotateOne
        Geo C B M F hCBMF

    have hBPGC :
        IsParallelogram Geo B P G C :=
      ParallelogramReverse
        Geo P B C G hPBCG

    have hCBPG :
        IsParallelogram Geo C B P G :=
      ParallelogramRotateOne
        Geo B P G C hBPGC

    have hGCBP :
        IsParallelogram Geo G C B P :=
      ParallelogramRotateOne
        Geo C B P G hCBPG

    have hGPF :
        Geo.Between G P F :=
      (HilbertOrder.between_incidence
        F P G hFPG).2.2.2.2

    have hGFP :
        Collinear Geo G F P :=
      PrimCollinearSymm
        Geo P F G hPFGcol

    have hGFM :
        Collinear Geo G F M :=
      hilbert_primCollinear_trans
        Geo
        G F P M
        hFP
        hGFP
        hFPMcol

    have hPFM :
        Geo.Between P F M :=
      i37_order_MFP_implies_FPG
        Geo
        C B
        G F P M
        hGCBP
        hFCBM
        hGFM
        hGPF

    have hMFP :
        Geo.Between M F P :=
      (HilbertOrder.between_incidence
        P F M hPFM).2.2.2.2

    exact
      False.elim
        ((HilbertOrder.between_unique
          M P F
          hMPFcol
          hMPF).2 hMFP)

  --------------------------------------------------------------------
  -- Impossible case: P-G-F.
  --
  -- F-P-M gives PF < FM.
  -- But FM ~= PG, hence PF < PG.
  -- P-G-F gives PG < PF: contradiction.
  --------------------------------------------------------------------

  · have hFP_lt_FM :
        HilbertSegmentLess Geo F P F M :=
      hilbert_segmentLess_of_between
        Geo F P M hFPM

    have hFM_PG :
        Geo.Congruent F M P G :=
      CongruentReverseFirst
        Geo M F P G hMF_PG

    have hFP_lt_PG :
        HilbertSegmentLess Geo F P P G :=
      hilbert_segmentLess_congruent_right
        Geo
        F P
        F M
        P G
        hFP_lt_FM
        hFM_PG

    have hPF_FP :
        Geo.Congruent P F F P :=
      CongruentSwapSecond
        Geo P F P F
        (hilbert_congruent_reflexive
          Geo P F)

    have hPF_lt_PG :
        HilbertSegmentLess Geo P F P G :=
      hilbert_segmentLess_congruent_left
        Geo
        F P
        P F
        P G
        hFP_lt_PG
        hPF_FP

    have hPG_lt_PF :
        HilbertSegmentLess Geo P G P F :=
      hilbert_segmentLess_of_between
        Geo P G F hPGF

    exact
      False.elim
        ((hilbert_segmentLess_asymm
          Geo P F P G hPF_lt_PG)
          hPG_lt_PF)

theorem i37_finish_order_MPF
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M P F G : Geo.Point)
    (hMBCF : IsParallelogram Geo M B C F)
    (hPBCG : IsParallelogram Geo P B C G)
    (hMPG : Collinear Geo M P G)
    (hABC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo M B C F))
    (hDBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertParallelogramTerm Geo P B C G))
    (hMPF : Geo.Between M P F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  have hPFG :
      Geo.Between P F G :=
    i37_order_MPF_implies_PFG
      Geo
      B C M P F G
      hMBCF
      hPBCG
      hMPG
      hMPF

  have hOrder :=
    hilbert_between_outer_trans
      Geo
      M P F G
      hMPF
      hPFG

  have hMFG :
      Geo.Between M F G :=
    hOrder.1

  have hPar :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M B C F)
        (hilbertParallelogramTerm Geo P B C G) :=
    euclid_proposition_35
      Geo
      M B C F P G
      hMBCF
      hPBCG
      hMFG
      hMPG

  exact
    equicomplementable_transport
      Geo
      hABC
      hDBC
      hPar

/--
Euclid I.37.

Triangles on the same base and between the same parallels are
equicomplementable.
-/
theorem euclid_proposition_37
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D B C) := by

  --------------------------------------------------------------------
  -- Hilbert 45 reduces both triangles to parallelograms on base BC.
  --------------------------------------------------------------------

  rcases
      i37_parallelogram_reduction
        Geo A B C D hAD_BC
    with
    ⟨M, P, F, G,
      hMBCF,
      hPBCG,
      hMP_BC,
      hMFP,
      hMPG,
      hMF_PG,
      hABC,
      hDBC⟩

  --------------------------------------------------------------------
  -- Degenerate case: the two left upper vertices coincide.
  --------------------------------------------------------------------

  by_cases hMP : M = P

  · exact
      i37_finish_same_left_vertex
        Geo
        A B C D M P F G
        hMBCF
        hPBCG
        hABC
        hDBC
        hMP

  --------------------------------------------------------------------
  -- Second boundary case: F is the second left upper vertex.
  --------------------------------------------------------------------

  by_cases hFP : F = P

  · exact
      i37_finish_common_upper_endpoint
        Geo
        A B C D M P F G
        hMBCF
        hPBCG
        hABC
        hDBC
        hFP

  --------------------------------------------------------------------
  -- The remaining three strict orders of M,F,P.
  --------------------------------------------------------------------

  rcases
      i37_upper_trichotomy
        Geo
        B C M P F
        hMBCF
        hMFP
        hMP
        hFP
    with
    hMFPorder | hFMPorder | hMPForder

  --------------------------------------------------------------------
  -- Case 1: M-F-P.
  --------------------------------------------------------------------

  · have hFPG :
        Geo.Between F P G :=
      i37_order_MFP_implies_FPG
        Geo
        B C M P F G
        hMBCF
        hPBCG
        hMPG
        hMFPorder

    exact
      i37_finish_order_MFP
        Geo
        A B C D M P F G
        hMBCF
        hPBCG
        hMPG
        hABC
        hDBC
        hMFPorder
        hFPG

  --------------------------------------------------------------------
  -- Case 2: F-M-P.
  --------------------------------------------------------------------

  · exact
      i37_finish_order_FMP
        Geo
        A B C D M P F G
        hMBCF
        hPBCG
        hMPG
        hABC
        hDBC
        hFMPorder

  --------------------------------------------------------------------
  -- Case 3: M-P-F.
  --------------------------------------------------------------------

  · exact
      i37_finish_order_MPF
        Geo
        A B C D M P F G
        hMBCF
        hPBCG
        hMPG
        hABC
        hDBC
        hMPForder

end Geometry

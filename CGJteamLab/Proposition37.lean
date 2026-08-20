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



end Geometry

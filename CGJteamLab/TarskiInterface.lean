import CGJteamLab.TarskiAxioms

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)

/-!
# TarskiBase

Basic notions and derived theorems in Tarski's primitive language.

This module is independent of the Hilbert incidence interface.
-/

------------------------------------------------------------
-- Definicje podstawowe i aksjomaty
------------------------------------------------------------

def TarskiCollinear (A B C : Geo.Point) : Prop :=
  Geo.Between A B C ∨
  Geo.Between B C A ∨
  Geo.Between C A B

def TarskiIsMidpoint (M A B : Geo.Point) : Prop :=
  Geo.Between A M B ∧
  Geo.Congruent A M M B

def TarskiParallelogram
    (A B C D : Geo.Point) : Prop :=
  (A ≠ C ∨ B ≠ D) ∧
  ∃ M : Geo.Point,
    TarskiIsMidpoint Geo M A C ∧
    TarskiIsMidpoint Geo M B D

def TarskiParallelStrict
    (A B C D : Geo.Point) : Prop :=
  A ≠ B ∧
  C ≠ D ∧
  ¬ ∃ X : Geo.Point,
      TarskiCollinear Geo X A B ∧
      TarskiCollinear Geo X C D

axiom gupta_sst_5_1_connectivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (hABC : Geo.Between A B C)
    (hABD : Geo.Between A B D) :
    Geo.Between A C D ∨ Geo.Between A D C

axiom tarski_central_symmetry_parallel
    [TarskiNeutral Geo]
    (M A B A' B' : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B M))
    (hA : TarskiIsMidpoint Geo M A A')
    (hB : TarskiIsMidpoint Geo M B B') :
    TarskiParallelStrict Geo A B A' B'

axiom tarski_parallel_congruent_parallelogram_cases
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hPar : TarskiParallelStrict Geo A B C D)
    (hCong : Geo.Congruent A B C D) :
    TarskiParallelogram Geo A B C D ∨
    TarskiParallelogram Geo A B D C


axiom tarski_midpoint_unique
    [TarskiNeutral Geo]
    (M N A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B)
    (hN : TarskiIsMidpoint Geo N A B) :
    M = N

axiom tarski_parallelogram_of_two_parallel_pairs
    [TarskiEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hABCD : TarskiParallelStrict Geo A B C D)
    (hBCAD : TarskiParallelStrict Geo B C A D) :
    TarskiParallelogram Geo A B C D

------------------------------------------------------------
-- Teoria relacji pomiędzy i współliniowości
------------------------------------------------------------

theorem tarski_collinear_rotate
    (A B C : Geo.Point) :
    TarskiCollinear Geo A B C →
    TarskiCollinear Geo B C A := by
  intro h
  rcases h with hABC | hBCA | hCAB
  · exact Or.inr (Or.inr hABC)
  · exact Or.inl hBCA
  · exact Or.inr (Or.inl hCAB)

theorem tarski_collinear_cycle
    (A B C : Geo.Point) :
    TarskiCollinear Geo A B C ↔
    TarskiCollinear Geo B C A := by
  constructor
  · exact tarski_collinear_rotate Geo A B C
  · intro h
    exact
      tarski_collinear_rotate Geo C A B
        (tarski_collinear_rotate Geo B C A h)

theorem tarski_midpoint_collinear
    (M A B : Geo.Point) :
    TarskiIsMidpoint Geo M A B →
    TarskiCollinear Geo A M B := by
  intro h
  exact Or.inl h.left

theorem tarski_between_reflexivity
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    Geo.Between A B B := by
  obtain ⟨X, hBetween, hCong⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo) A B B B
  have hBX : B = X :=
    TarskiNeutral.congruent_identity
      (Geo := Geo) B X B hCong
  simpa [hBX] using hBetween

theorem tarski_between_symmetry
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    Geo.Between C B A := by
  have hBCC : Geo.Between B C C :=
    tarski_between_reflexivity (Geo := Geo) B C
  obtain ⟨X, hBXB, hCXA⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      A B C B C
      hABC hBCC
  have hBX : B = X :=
    TarskiNeutral.between_identity
      (Geo := Geo) B X hBXB
  simpa [← hBX] using hCXA

theorem tarski_collinear_symmetry
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (h : TarskiCollinear Geo A B C) :
    TarskiCollinear Geo A C B := by
  rcases h with hABC | hBCA | hCAB
  · right
    left
    exact tarski_between_symmetry
      (Geo := Geo) A B C hABC
  · left
    exact tarski_between_symmetry
      (Geo := Geo) B C A hBCA
  · right
    right
    exact tarski_between_symmetry
      (Geo := Geo) C A B hCAB

theorem tarski_between_inner_transitivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hBCD : Geo.Between B C D) :
    Geo.Between A B C := by
  obtain ⟨X, hBXB, hCXA⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      A B D B C
      hABD hBCD
  have hBX : B = X :=
    TarskiNeutral.between_identity
      (Geo := Geo) B X hBXB
  have hCBA : Geo.Between C B A := by
    simpa [← hBX] using hCXA
  exact tarski_between_symmetry
    (Geo := Geo) C B A hCBA

theorem tarski_between_exchange3
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hACD : Geo.Between A C D) :
    Geo.Between B C D := by
  have hCBA : Geo.Between C B A :=
    tarski_between_symmetry (Geo := Geo) A B C hABC
  have hDCA : Geo.Between D C A :=
    tarski_between_symmetry (Geo := Geo) A C D hACD
  obtain ⟨X, hCXC, hBXD⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      D C A C B
      hDCA hCBA
  have hCX : C = X :=
    TarskiNeutral.between_identity
      (Geo := Geo) C X hCXC
  simpa [← hCX] using hBXD

theorem tarski_congruent_reflexivity
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    Geo.Congruent A B A B := by
  have hBAAB : Geo.Congruent B A A B :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo) B A
  exact TarskiNeutral.congruent_transitivity
    (Geo := Geo)
    B A A B A B
    hBAAB hBAAB

theorem tarski_congruent_symmetry
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by
  have hABAB : Geo.Congruent A B A B :=
    tarski_congruent_reflexivity (Geo := Geo) A B
  exact TarskiNeutral.congruent_transitivity
    (Geo := Geo)
    A B C D A B
    hABCD hABAB

theorem tarski_congruent_reverse_both
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent B A D C := by
  exact
    (Geometry.Tarski.Geo.congruent_reverse_second Geo B A C D).mp
      ((Geometry.Tarski.Geo.congruent_reverse_first Geo A B C D).mp hABCD)

theorem tarski_congruent_zero
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    Geo.Congruent A A B B := by
  obtain ⟨X, _hAAX, hAXBB⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo) A A B B
  have hAX : A = X :=
    TarskiNeutral.congruent_identity
      (Geo := Geo) A X B hAXBB
  simpa [← hAX] using hAXBB

theorem tarski_l2_11_nondegenerate
    [TarskiNeutral Geo]
    (A B C A' B' C' : Geo.Point)
    (hABC : Geo.Between A B C)
    (hA'B'C' : Geo.Between A' B' C')
    (hAB : A ≠ B)
    (hCongAB : Geo.Congruent A B A' B')
    (hCongBC : Geo.Congruent B C B' C') :
    Geo.Congruent A C A' C' := by
  have hZero : Geo.Congruent A A A' A' :=
    tarski_congruent_zero (Geo := Geo) A A'
  have hReverseAB : Geo.Congruent B A B' A' :=
    tarski_congruent_reverse_both
      (Geo := Geo) A B A' B' hCongAB
  have hCA : Geo.Congruent C A C' A' :=
    TarskiNeutral.five_segment
      (Geo := Geo)
      A A' B B' C C' A A'
      hAB
      hABC
      hA'B'C'
      hCongAB
      hCongBC
      hZero
      hReverseAB
  exact tarski_congruent_reverse_both
    (Geo := Geo) C A C' A' hCA

theorem tarski_construction_uniqueness
    [TarskiNeutral Geo]
    (Q A X Y B C : Geo.Point)
    (hQA : Q ≠ A)
    (hQAX : Geo.Between Q A X)
    (hQAY : Geo.Between Q A Y)
    (hAXBC : Geo.Congruent A X B C)
    (hAYBC : Geo.Congruent A Y B C) :
    X = Y := by
  have hBCAY : Geo.Congruent B C A Y :=
    tarski_congruent_symmetry
      (Geo := Geo) A Y B C hAYBC
  have hAXAY : Geo.Congruent A X A Y :=
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      B C A X A Y
      (tarski_congruent_symmetry
        (Geo := Geo) A X B C hAXBC)
      hBCAY
  have hQAQA : Geo.Congruent Q A Q A :=
    tarski_congruent_reflexivity
      (Geo := Geo) Q A
  have hQXQY : Geo.Congruent Q X Q Y :=
    tarski_l2_11_nondegenerate
      (Geo := Geo)
      Q A X Q A Y
      hQAX
      hQAY
      hQA
      hQAQA
      hAXAY
  have hQYQX : Geo.Congruent Q Y Q X :=
    tarski_congruent_symmetry
      (Geo := Geo) Q X Q Y hQXQY
  have hAYAX : Geo.Congruent A Y A X :=
    tarski_congruent_symmetry
      (Geo := Geo) A X A Y hAXAY
  have hAXAX : Geo.Congruent A X A X :=
    tarski_congruent_reflexivity
      (Geo := Geo) A X
  have hXYXX : Geo.Congruent X Y X X :=
    TarskiNeutral.five_segment
      (Geo := Geo)
      Q Q A A X X Y X
      hQA
      hQAX
      hQAX
      hQAQA
      hAXAX
      hQYQX
      hAYAX
  exact TarskiNeutral.congruent_identity
    (Geo := Geo) X Y X hXYXX

theorem tarski_between_outer_transitivity2
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D)
    (hBC : B ≠ C) :
    Geo.Between A C D := by
  obtain ⟨X, hACX, hCXCD⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo) A C C D
  have hBCX : Geo.Between B C X :=
    tarski_between_exchange3
      (Geo := Geo) A B C X hABC hACX
  have hCDCD : Geo.Congruent C D C D :=
    tarski_congruent_reflexivity
      (Geo := Geo) C D
  have hXD : X = D :=
    tarski_construction_uniqueness
      (Geo := Geo)
      B C X D C D
      hBC
      hBCX
      hBCD
      hCXCD
      hCDCD
  simpa [hXD] using hACX

theorem tarski_between_outer_transitivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D)
    (hBC : B ≠ C) :
    Geo.Between A B D := by
  have hDCB : Geo.Between D C B :=
    tarski_between_symmetry
      (Geo := Geo) B C D hBCD
  have hCBA : Geo.Between C B A :=
    tarski_between_symmetry
      (Geo := Geo) A B C hABC
  have hDBA : Geo.Between D B A :=
    tarski_between_outer_transitivity2
      (Geo := Geo)
      D C B A
      hDCB
      hCBA
      hBC.symm
  exact tarski_between_symmetry
    (Geo := Geo) D B A hDBA

theorem gupta_sst_5_1_connectivity2
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (hABC : Geo.Between A B C)
    (hABD : Geo.Between A B D) :
    Geo.Between B C D ∨ Geo.Between B D C := by
  rcases gupta_sst_5_1_connectivity
      (Geo := Geo) A B C D hAB hABC hABD with hACD | hADC
  · left
    exact tarski_between_exchange3
      (Geo := Geo) A B C D hABC hACD
  · right
    exact tarski_between_exchange3
      (Geo := Geo) A B D C hABD hADC

theorem tarski_between_inner_connectivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hACD : Geo.Between A C D) :
    Geo.Between A B C ∨ Geo.Between A C B := by
  by_cases hAD : A = D
  · subst D
    have hAB : A = B :=
      TarskiNeutral.between_identity
        (Geo := Geo) A B hABD
    subst B
    left
    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity
        (Geo := Geo) C A
    exact tarski_between_symmetry
      (Geo := Geo) C A A hCAA
  · obtain ⟨P, hDAP, hAPDA⟩ :=
      TarskiNeutral.segment_construction
        (Geo := Geo) D A D A
    have hPA : P ≠ A := by
      intro hPA
      subst P
      have hDAAA : Geo.Congruent D A A A :=
        tarski_congruent_symmetry
          (Geo := Geo) A A D A hAPDA
      have hDA : D = A :=
        TarskiNeutral.congruent_identity
          (Geo := Geo) D A A hDAAA
      exact hAD hDA.symm
    have hPAD : Geo.Between P A D :=
      tarski_between_symmetry
        (Geo := Geo) D A P hDAP
    have hPAB : Geo.Between P A B :=
      tarski_between_inner_transitivity
        (Geo := Geo) P A B D hPAD hABD
    have hPAC : Geo.Between P A C :=
      tarski_between_inner_transitivity
        (Geo := Geo) P A C D hPAD hACD
    exact gupta_sst_5_1_connectivity2
      (Geo := Geo)
      P A B C
      hPA
      hPAB
      hPAC

theorem tarski_collinear_trans
    [TarskiNeutral Geo]
    (A G P D : Geo.Point)
    (hGP : G ≠ P)
    (hAGP : TarskiCollinear Geo A G P)
    (hGPD : TarskiCollinear Geo G P D) :
    TarskiCollinear Geo A G D := by
  rcases hAGP with hAGP | hGPA | hPAG
  · rcases hGPD with hGPD | hPDG | hDGP
    · left
      exact tarski_between_outer_transitivity
        (Geo := Geo) A G P D hAGP hGPD hGP
    · have hGDP : Geo.Between G D P :=
        tarski_between_symmetry (Geo := Geo) P D G hPDG
      left
      exact tarski_between_inner_transitivity
        (Geo := Geo) A G D P hAGP hGDP
    · have hPGA : Geo.Between P G A :=
        tarski_between_symmetry (Geo := Geo) A G P hAGP
      have hPGD : Geo.Between P G D :=
        tarski_between_symmetry (Geo := Geo) D G P hDGP
      rcases gupta_sst_5_1_connectivity
          (Geo := Geo) P G A D hGP.symm hPGA hPGD with hPAD | hPDA
      · have hGAD : Geo.Between G A D :=
          tarski_between_exchange3 (Geo := Geo) P G A D hPGA hPAD
        right
        right
        exact tarski_between_symmetry (Geo := Geo) G A D hGAD
      · right
        left
        exact tarski_between_exchange3 (Geo := Geo) P G D A hPGD hPDA
  · rcases hGPD with hGPD | hPDG | hDGP
    · rcases gupta_sst_5_1_connectivity
          (Geo := Geo) G P A D hGP hGPA hGPD with hGAD | hGDA
      · right
        right
        exact tarski_between_symmetry (Geo := Geo) G A D hGAD
      · right
        left
        exact hGDA
    · have hGDP : Geo.Between G D P :=
        tarski_between_symmetry (Geo := Geo) P D G hPDG
      by_cases hDP : D = P
      · subst D
        right
        left
        exact hGPA
      · have hDPA : Geo.Between D P A :=
          tarski_between_exchange3 (Geo := Geo) G D P A hGDP hGPA
        right
        left
        exact tarski_between_outer_transitivity (Geo := Geo) G D P A hGDP hDPA hDP
    · have hDGA : Geo.Between D G A :=
        tarski_between_outer_transitivity (Geo := Geo) D G P A hDGP hGPA hGP
      left
      exact tarski_between_symmetry (Geo := Geo) D G A hDGA
  · rcases hGPD with hGPD | hPDG | hDGP
    · have hDPG : Geo.Between D P G :=
        tarski_between_symmetry (Geo := Geo) G P D hGPD
      by_cases hPA : P = A
      · subst P
        right
        right
        exact hDPG
      · have hDPA : Geo.Between D P A :=
          tarski_between_inner_transitivity (Geo := Geo) D P A G hDPG hPAG
        right
        right
        exact tarski_between_outer_transitivity2 (Geo := Geo) D P A G hDPA hPAG hPA
    · rcases tarski_between_inner_connectivity
          (Geo := Geo) P A D G hPAG hPDG with hPAD | hPDA
      · have hADG : Geo.Between A D G :=
          tarski_between_exchange3 (Geo := Geo) P A D G hPAD hPDG
        right
        left
        exact tarski_between_symmetry (Geo := Geo) A D G hADG
      · right
        right
        exact tarski_between_exchange3 (Geo := Geo) P D A G hPDA hPAG
    · have hGAP : Geo.Between G A P :=
        tarski_between_symmetry (Geo := Geo) P A G hPAG
      have hDGA : Geo.Between D G A :=
        tarski_between_inner_transitivity (Geo := Geo) D G A P hDGP hGAP
      left
      exact tarski_between_symmetry (Geo := Geo) D G A hDGA


------------------------------------------------------------
-- Konstrukcje i własności środków odcinków (Midpoint)
------------------------------------------------------------

theorem tarski_symmetric_point_exists
    [TarskiNeutral Geo]
    (P Q : Geo.Point) :
    ∃ X : Geo.Point,
      TarskiIsMidpoint Geo Q P X := by
  obtain ⟨X, hPQX, hQXPQ⟩ :=
    TarskiNeutral.segment_construction (Geo := Geo) P Q P Q
  have hPQQX : Geo.Congruent P Q Q X :=
    tarski_congruent_symmetry (Geo := Geo) Q X P Q hQXPQ
  exact ⟨X, hPQX, hPQQX⟩

theorem tarski_midpoint_ne_second
    [TarskiNeutral Geo]
    (P B C : Geo.Point)
    (hBC : B ≠ C)
    (hP : TarskiIsMidpoint Geo P B C) :
    P ≠ C := by
  intro hPC
  subst C
  have hBP : B = P :=
    TarskiNeutral.congruent_identity (Geo := Geo) B P P hP.2
  exact hBC hBP

theorem tarski_noncollinear_ne_second_third
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C)) :
    B = C → False := by
  intro hBC
  subst C
  apply hNonCol
  left
  exact tarski_between_reflexivity (Geo := Geo) A B

theorem tarski_noncollinear_midpoint_second
    [TarskiNeutral Geo]
    (A B C P : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C) :
    Not (TarskiCollinear Geo A P C) := by
  intro hAPC
  have hBC : B = C → False :=
    tarski_noncollinear_ne_second_third Geo A B C hNonCol
  have hPC : P = C → False :=
    tarski_midpoint_ne_second Geo P B C hBC hP
  have hPCB : TarskiCollinear Geo P C B := by
    right
    right
    exact hP.1
  have hAPB : TarskiCollinear Geo A P B :=
    tarski_collinear_trans Geo A P C B hPC hAPC hPCB
  have hABP : TarskiCollinear Geo A B P :=
    tarski_collinear_symmetry Geo A P B hAPB
  have hBP : B = P → False := by
    intro hBP
    subst B
    have hPCPP : Geo.Congruent P C P P :=
      tarski_congruent_symmetry (Geo := Geo) P P P C hP.2
    have hPCeq : P = C :=
      TarskiNeutral.congruent_identity (Geo := Geo) P C P hPCPP
    exact hPC hPCeq
  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1
  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans Geo A B P C hBP hABP hBPC
  exact hNonCol hABC

theorem tarski_inner_five_segment
    [TarskiNeutral Geo]
    (A A' B B' C C' D D' : Geo.Point)
    (hABC : Geo.Between A B C)
    (hA'B'C' : Geo.Between A' B' C')
    (hAC : Geo.Congruent A C A' C')
    (hBC : Geo.Congruent B C B' C')
    (hAD : Geo.Congruent A D A' D')
    (hCD : Geo.Congruent C D C' D') :
    Geo.Congruent B D B' D' := by
  by_cases hACeq : A = C
  · subst C
    have hABeq : A = B :=
      TarskiNeutral.between_identity (Geo := Geo) A B hABC
    subst B
    have hA'C'AA : Geo.Congruent A' C' A A :=
      tarski_congruent_symmetry (Geo := Geo) A A A' C' hAC
    have hA'C'eq : A' = C' :=
      TarskiNeutral.congruent_identity (Geo := Geo) A' C' A hA'C'AA
    subst C'
    have hA'B'eq : A' = B' :=
      TarskiNeutral.between_identity (Geo := Geo) A' B' hA'B'C'
    subst B'
    exact hAD
  · obtain ⟨E, hACE, hCEAC⟩ :=
      TarskiNeutral.segment_construction (Geo := Geo) A C A C
    obtain ⟨E', hA'C'E', hC'E'AC⟩ :=
      TarskiNeutral.segment_construction (Geo := Geo) A' C' A C
    have hACCE : Geo.Congruent A C C E :=
      tarski_congruent_symmetry (Geo := Geo) C E A C hCEAC
    have hACC'E' : Geo.Congruent A C C' E' :=
      tarski_congruent_symmetry (Geo := Geo) C' E' A C hC'E'AC
    have hCEC'E' : Geo.Congruent C E C' E' :=
      TarskiNeutral.congruent_transitivity (Geo := Geo) A C C E C' E' hACCE hACC'E'
    have hEDE'D' : Geo.Congruent E D E' D' :=
      TarskiNeutral.five_segment (Geo := Geo) A A' C C' E E' D D' hACeq hACE hA'C'E' hAC hCEC'E' hAD hCD
    have hECA : Geo.Between E C A :=
      tarski_between_symmetry (Geo := Geo) A C E hACE
    have hCBA : Geo.Between C B A :=
      tarski_between_symmetry (Geo := Geo) A B C hABC
    have hECB : Geo.Between E C B :=
      tarski_between_inner_transitivity (Geo := Geo) E C B A hECA hCBA
    have hE'C'A' : Geo.Between E' C' A' :=
      tarski_between_symmetry (Geo := Geo) A' C' E' hA'C'E'
    have hC'B'A' : Geo.Between C' B' A' :=
      tarski_between_symmetry (Geo := Geo) A' B' C' hA'B'C'
    have hE'C'B' : Geo.Between E' C' B' :=
      tarski_between_inner_transitivity (Geo := Geo) E' C' B' A' hE'C'A' hC'B'A'
    have hEC : E ≠ C := by
      intro hEq
      subst E
      have hCCAC : Geo.Congruent C C A C := hCEAC
      have hACCC : Geo.Congruent A C C C :=
        tarski_congruent_symmetry (Geo := Geo) C C A C hCCAC
      have hAC' : A = C :=
        TarskiNeutral.congruent_identity (Geo := Geo) A C C hACCC
      exact hACeq hAC'
    have hECE'C' : Geo.Congruent E C E' C' :=
      tarski_congruent_reverse_both (Geo := Geo) C E C' E' hCEC'E'
    have hCBC'B' : Geo.Congruent C B C' B' :=
      tarski_congruent_reverse_both (Geo := Geo) B C B' C' hBC
    exact
      TarskiNeutral.five_segment
        (Geo := Geo) E E' C C' B B' D D' hEC hECB hE'C'B' hECE'C' hCBC'B' hEDE'D' hCD

theorem tarski_two_medians_intersect
    [TarskiNeutral Geo]
    (A B C E F : Geo.Point)
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B) :
    Exists fun G : Geo.Point =>
      TarskiCollinear Geo B E G /\
      TarskiCollinear Geo C F G := by
  have hCEA : Geo.Between C E A :=
    tarski_between_symmetry (Geo := Geo) A E C hE.1
  have hBFA : Geo.Between B F A :=
    tarski_between_symmetry (Geo := Geo) A F B hF.1
  obtain ⟨G, hEGB, hFGC⟩ :=
    TarskiNeutral.inner_pasch (Geo := Geo) C B A E F hCEA hBFA
  have hBEG : TarskiCollinear Geo B E G := Or.inr (Or.inl hEGB)
  have hCFG : TarskiCollinear Geo C F G := Or.inr (Or.inl hFGC)
  exact ⟨G, hBEG, hCFG⟩

theorem tarski_l4_5
    [TarskiNeutral Geo]
    (A B C A' C' : Geo.Point)
    (hABC : Geo.Between A B C)
    (hAC : Geo.Congruent A C A' C') :
    ∃ B' : Geo.Point,
      Geo.Between A' B' C' ∧
      Geo.Congruent A B A' B' ∧
      Geo.Congruent B C B' C' ∧
      Geo.Congruent A C A' C' := by
  by_cases hABeq : A = B
  · subst B
    have hA'A'C' : Geo.Between A' A' C' := by
      have hC'A'A' : Geo.Between C' A' A' :=
        tarski_between_reflexivity (Geo := Geo) C' A'
      exact tarski_between_symmetry (Geo := Geo) C' A' A' hC'A'A'
    have hAAA'A' : Geo.Congruent A A A' A' :=
      tarski_congruent_zero (Geo := Geo) A A'
    exact ⟨A', hA'A'C', hAAA'A', hAC, hAC⟩
  · have hACne : A ≠ C := by
      intro hACeq
      subst C
      have hAB : A = B :=
        TarskiNeutral.between_identity (Geo := Geo) A B hABC
      exact hABeq hAB
    have hA'C'ne : A' ≠ C' := by
      intro hA'C'eq
      subst C'
      have hACA'A' : Geo.Congruent A C A' A' := hAC
      have hACeq : A = C :=
        TarskiNeutral.congruent_identity (Geo := Geo) A C A' hACA'A'
      exact hACne hACeq
    obtain ⟨X, hC'A'X, hA'XA'C'⟩ :=
      TarskiNeutral.segment_construction (Geo := Geo) C' A' A' C'
    have hXA' : X ≠ A' := by
      intro hXA'eq
      subst X
      have hA'A'A'C' : Geo.Congruent A' A' A' C' := hA'XA'C'
      have hA'C'A'A' : Geo.Congruent A' C' A' A' :=
        tarski_congruent_symmetry (Geo := Geo) A' A' A' C' hA'A'A'C'
      have hA'C'eq : A' = C' :=
        TarskiNeutral.congruent_identity (Geo := Geo) A' C' A' hA'C'A'A'
      exact hA'C'ne hA'C'eq
    obtain ⟨B', hXA'B', hA'B'AB⟩ :=
      TarskiNeutral.segment_construction (Geo := Geo) X A' A B
    have hA'B'ne : A' ≠ B' := by
      intro hA'B'eq
      subst B'
      have hA'A'AB : Geo.Congruent A' A' A B := hA'B'AB
      have hABA'A' : Geo.Congruent A B A' A' :=
        tarski_congruent_symmetry (Geo := Geo) A' A' A B hA'A'AB
      have hABeq' : A = B :=
        TarskiNeutral.congruent_identity (Geo := Geo) A B A' hABA'A'
      exact hABeq hABeq'
    obtain ⟨C'', hXB'C'', hB'C''BC⟩ :=
      TarskiNeutral.segment_construction (Geo := Geo) X B' B C
    have hA'B'C'' : Geo.Between A' B' C'' :=
      tarski_between_exchange3 (Geo := Geo) X A' B' C'' hXA'B' hXB'C''
    have hXA'C'' : Geo.Between X A' C'' :=
      tarski_between_outer_transitivity (Geo := Geo) X A' B' C'' hXA'B' hA'B'C'' hA'B'ne
    have hA'C''AC : Geo.Congruent A' C'' A C :=
      tarski_l2_11_nondegenerate (Geo := Geo) A' B' C'' A B C hA'B'C'' hABC hA'B'ne hA'B'AB hB'C''BC
    have hXA'C' : Geo.Between X A' C' :=
      tarski_between_symmetry (Geo := Geo) C' A' X hC'A'X
    have hA'C'AC : Geo.Congruent A' C' A C :=
      tarski_congruent_symmetry (Geo := Geo) A C A' C' hAC
    have hC''C' : C'' = C' :=
      tarski_construction_uniqueness (Geo := Geo) X A' C'' C' A C hXA' hXA'C'' hXA'C' hA'C''AC hA'C'AC
    subst C''
    have hABA'B' : Geo.Congruent A B A' B' :=
      tarski_congruent_symmetry (Geo := Geo) A' B' A B hA'B'AB
    have hBCB'C' : Geo.Congruent B C B' C' :=
      tarski_congruent_symmetry (Geo := Geo) B' C' B C hB'C''BC
    exact ⟨B', hA'B'C'', hABA'B', hBCB'C', hAC⟩

theorem tarski_l4_6
    [TarskiNeutral Geo]
    (A B C A' B' C' : Geo.Point)
    (hABC : Geo.Between A B C)
    (hAB : Geo.Congruent A B A' B')
    (hBC : Geo.Congruent B C B' C')
    (hAC : Geo.Congruent A C A' C') :
    Geo.Between A' B' C' := by
  obtain ⟨B'', hA'B''C', hABB'', hBCB'', _⟩ :=
    tarski_l4_5 (Geo := Geo) A B C A' C' hABC hAC
  have hCBC'B' : Geo.Congruent C B C' B' :=
    tarski_congruent_reverse_both (Geo := Geo) B C B' C' hBC
  have hBBB''B' : Geo.Congruent B B B'' B' :=
    tarski_inner_five_segment (Geo := Geo) A A' B B'' C C' B B' hABC hA'B''C' hAC hBCB'' hAB hCBC'B'
  have hB''B'BB : Geo.Congruent B'' B' B B :=
    tarski_congruent_symmetry (Geo := Geo) B B B'' B' hBBB''B'
  have hB''eqB' : B'' = B' :=
    TarskiNeutral.congruent_identity (Geo := Geo) B'' B' B hB''B'BB
  subst B'
  exact hA'B''C'

theorem tarski_l4_16
    [TarskiNeutral Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hCol : TarskiCollinear Geo A B C)
    (hABne : A ≠ B)
    (hAB : Geo.Congruent A B A' B')
    (hBC : Geo.Congruent B C B' C')
    (hAC : Geo.Congruent A C A' C')
    (hAD : Geo.Congruent A D A' D')
    (hBD : Geo.Congruent B D B' D') :
    Geo.Congruent C D C' D' := by
  rcases hCol with hABC | hBCA | hCAB
  · have hA'B'C' : Geo.Between A' B' C' :=
      tarski_l4_6 (Geo := Geo) A B C A' B' C' hABC hAB hBC hAC
    exact
      TarskiNeutral.five_segment (Geo := Geo) A A' B B' C C' D D' hABne hABC hA'B'C' hAB hBC hAD hBD
  · have hB'C'A' : Geo.Between B' C' A' :=
      tarski_l4_6 (Geo := Geo) B C A B' C' A' hBCA hBC
        (tarski_congruent_reverse_both (Geo := Geo) A C A' C' hAC)
        (tarski_congruent_reverse_both (Geo := Geo) A B A' B' hAB)
    exact
      tarski_inner_five_segment (Geo := Geo) B B' C C' A A' D D' hBCA hB'C'A'
        (tarski_congruent_reverse_both (Geo := Geo) A B A' B' hAB)
        (tarski_congruent_reverse_both (Geo := Geo) A C A' C' hAC) hBD hAD
  · have hBAC : Geo.Between B A C :=
      tarski_between_symmetry (Geo := Geo) C A B hCAB
    have hB'A'C' : Geo.Between B' A' C' :=
      tarski_l4_6 (Geo := Geo) B A C B' A' C' hBAC
        (tarski_congruent_reverse_both (Geo := Geo) A B A' B' hAB) hAC hBC
    exact
      TarskiNeutral.five_segment (Geo := Geo) B B' A A' C C' D D' (Ne.symm hABne) hBAC hB'A'C'
        (tarski_congruent_reverse_both (Geo := Geo) A B A' B' hAB) hAC hBD hAD

theorem tarski_l7_13_aux
    [TarskiNeutral Geo]
    (A P Q P' Q' : Geo.Point) :
    exists X X' Y Y' : Geo.Point,
      Geo.Between P' P X /\
      Geo.Congruent P X Q A /\
      Geo.Between X P' X' /\
      Geo.Congruent P' X' Q A /\
      Geo.Between Q' Q Y /\
      Geo.Congruent Q Y P A /\
      Geo.Between Y Q' Y' /\
      Geo.Congruent Q' Y' P A := by
  obtain ⟨X, hPprimePX, hPXQA⟩ :=
    TarskiNeutral.segment_construction (Geo := Geo) P' P Q A
  obtain ⟨X', hXPprimeXprime, hPprimeXprimeQA⟩ :=
    TarskiNeutral.segment_construction (Geo := Geo) X P' Q A
  obtain ⟨Y, hQprimeQY, hQYPA⟩ :=
    TarskiNeutral.segment_construction (Geo := Geo) Q' Q P A
  obtain ⟨Y', hYQprimeYprime, hQprimeYprimePA⟩ :=
    TarskiNeutral.segment_construction (Geo := Geo) Y Q' P A
  exact
    ⟨X, X', Y, Y', hPprimePX, hPXQA, hXPprimeXprime, hPprimeXprimeQA, hQprimeQY, hQYPA, hYQprimeYprime, hQprimeYprimePA⟩

theorem tarski_l7_13_betweenness
    [TarskiNeutral Geo]
    (A P Q P' Q' X X' Y Y' : Geo.Point)
    (hPA : P ≠ A)
    (hPmid : TarskiIsMidpoint Geo A P' P)
    (hQmid : TarskiIsMidpoint Geo A Q' Q)
    (hPprimePX : Geo.Between P' P X)
    (hXPprimeXprime : Geo.Between X P' X')
    (hQprimeQY : Geo.Between Q' Q Y)
    (hYQprimeYprime : Geo.Between Y Q' Y') :
    Geo.Between Y A Q' /\
    Geo.Between P' A X /\
    Geo.Between A P X /\
    Geo.Between Y Q A /\
    Geo.Between A Q' Y' /\
    Geo.Between X' P' A /\
    Geo.Between X A X' /\
    Geo.Between Y A Y' := by
  rcases hPmid with ⟨hPprimeAP, hPprimeAAP⟩
  rcases hQmid with ⟨hQprimeAQ, hQprimeAAQ⟩
  have hAP : A ≠ P := by
    intro hAPeq
    exact hPA hAPeq.symm
  have hPprimeA : P' ≠ A := by
    intro hEq
    subst P'
    have hAPAA : Geo.Congruent A P A A :=
      tarski_congruent_symmetry (Geo := Geo) A A A P hPprimeAAP
    have hEqAP : A = P :=
      TarskiNeutral.congruent_identity (Geo := Geo) A P A hAPAA
    exact hAP hEqAP
  have hAPprime : A ≠ P' := by
    intro hEq
    exact hPprimeA hEq.symm
  have hAPX : Geo.Between A P X :=
    tarski_between_exchange3 (Geo := Geo) P' A P X hPprimeAP hPprimePX
  have hPprimeAX : Geo.Between P' A X :=
    tarski_between_outer_transitivity (Geo := Geo) P' A P X hPprimeAP hAPX hAP
  have hXprimePprimeX : Geo.Between X' P' X :=
    tarski_between_symmetry (Geo := Geo) X P' X' hXPprimeXprime
  have hXprimePprimeA : Geo.Between X' P' A :=
    tarski_between_inner_transitivity (Geo := Geo) X' P' A X hXprimePprimeX hPprimeAX
  have hXAPprime : Geo.Between X A P' :=
    tarski_between_symmetry (Geo := Geo) P' A X hPprimeAX
  have hAPprimeXprime : Geo.Between A P' X' :=
    tarski_between_exchange3 (Geo := Geo) X A P' X' hXAPprime hXPprimeXprime
  have hXAXprime : Geo.Between X A X' :=
    tarski_between_outer_transitivity (Geo := Geo) X A P' X' hXAPprime hAPprimeXprime hAPprime
  have hAQY : Geo.Between A Q Y :=
    tarski_between_exchange3 (Geo := Geo) Q' A Q Y hQprimeAQ hQprimeQY
  have hYQA : Geo.Between Y Q A :=
    tarski_between_symmetry (Geo := Geo) A Q Y hAQY
  by_cases hQA : Q = A
  · subst Q
    have hQprimeEqA : Q' = A :=
      TarskiNeutral.congruent_identity (Geo := Geo) Q' A A hQprimeAAQ
    subst Q'
    have hYAA : Geo.Between Y A A :=
      tarski_between_symmetry (Geo := Geo) A A Y hQprimeQY
    have hYprimeAA : Geo.Between Y' A A :=
      tarski_between_reflexivity (Geo := Geo) Y' A
    have hAAYprime : Geo.Between A A Y' :=
      tarski_between_symmetry (Geo := Geo) Y' A A hYprimeAA
    exact
      ⟨hYAA, hPprimeAX, hAPX, hYQA, hAAYprime, hXprimePprimeA, hXAXprime, hYQprimeYprime⟩
  · have hAQ : A ≠ Q := by
      intro hAQeq
      exact hQA hAQeq.symm
    have hQprimeA : Q' ≠ A := by
      intro hEq
      subst Q'
      have hAQAA : Geo.Congruent A Q A A :=
        tarski_congruent_symmetry (Geo := Geo) A A A Q hQprimeAAQ
      have hEqAQ : A = Q :=
        TarskiNeutral.congruent_identity (Geo := Geo) A Q A hAQAA
      exact hAQ hEqAQ
    have hAQprime : A ≠ Q' := by
      intro hEq
      exact hQprimeA hEq.symm
    have hQprimeAY : Geo.Between Q' A Y :=
      tarski_between_outer_transitivity (Geo := Geo) Q' A Q Y hQprimeAQ hAQY hAQ
    have hYAQprime : Geo.Between Y A Q' :=
      tarski_between_symmetry (Geo := Geo) Q' A Y hQprimeAY
    have hAQprimeYprime : Geo.Between A Q' Y' :=
      tarski_between_exchange3 (Geo := Geo) Y A Q' Y' hYAQprime hYQprimeYprime
    have hYAYprime : Geo.Between Y A Y' :=
      tarski_between_outer_transitivity (Geo := Geo) Y A Q' Y' hYAQprime hAQprimeYprime hAQprime
    exact
      ⟨hYAQprime, hPprimeAX, hAPX, hYQA, hAQprimeYprime, hXprimePprimeA, hXAXprime, hYAYprime⟩

theorem tarski_l7_13_congruent_AX_YA
    [TarskiNeutral Geo]
    (A P Q X Y : Geo.Point)
    (hPA : P ≠ A)
    (hAPX : Geo.Between A P X)
    (hYQA : Geo.Between Y Q A)
    (hPXQA : Geo.Congruent P X Q A)
    (hQYPA : Geo.Congruent Q Y P A) :
    Geo.Congruent A X Y A := by
  have hAP : A ≠ P := by
    intro hAPeq
    exact hPA hAPeq.symm
  have hYQAP : Geo.Congruent Y Q A P :=
    tarski_congruent_reverse_both (Geo := Geo) Q Y P A hQYPA
  have hAPYQ : Geo.Congruent A P Y Q :=
    tarski_congruent_symmetry (Geo := Geo) Y Q A P hYQAP
  exact
    tarski_l2_11_nondegenerate (Geo := Geo) A P X Y Q A hAPX hYQA hAP hAPYQ hPXQA

theorem tarski_l7_13_congruent_YQprime_PprimeX
    [TarskiNeutral Geo]
    (A P' Q' X Y : Geo.Point)
    (hYA : Y ≠ A)
    (hYAQprime : Geo.Between Y A Q')
    (hPprimeAX : Geo.Between P' A X)
    (hYAPprimeA : Geo.Congruent Y A P' A)
    (hAQprimeAX : Geo.Congruent A Q' A X) :
    Geo.Congruent Y Q' P' X := by
  exact
    tarski_l2_11_nondegenerate (Geo := Geo) Y A Q' P' A X hYAQprime hPprimeAX hYA hYAPprimeA hAQprimeAX

theorem tarski_l7_13_congruent_QprimeY_XPprime
    [TarskiNeutral Geo]
    (P' Q' X Y : Geo.Point)
    (hYQprimePprimeX : Geo.Congruent Y Q' P' X) :
    Geo.Congruent Q' Y X P' := by
  exact
    tarski_congruent_reverse_both (Geo := Geo) Y Q' P' X hYQprimePprimeX

theorem tarski_l7_13_l4_16_step
    [TarskiNeutral Geo]
    (A P' Q' X Y : Geo.Point)
    (hYAQprime : Geo.Between Y A Q')
    (hYA : Y ≠ A)
    (hYAPprimeA : Geo.Congruent Y A P' A)
    (hAQprimeAX : Geo.Congruent A Q' A X)
    (hYQprimePprimeX : Geo.Congruent Y Q' P' X)
    (hYPprime : Geo.Congruent Y P' P' Y)
    (hAPprime : Geo.Congruent A P' A Y) :
    Geo.Congruent Q' P' X Y := by
  have hColYAQprime : TarskiCollinear Geo Y A Q' := Or.inl hYAQprime
  exact
    tarski_l4_16 (Geo := Geo) Y A Q' P' P' A X Y hColYAQprime hYA hYAPprimeA hAQprimeAX hYQprimePprimeX hYPprime hAPprime

theorem tarski_l7_13_congruent_AYprime_XprimeA
    [TarskiNeutral Geo]
    (A P' Q' X' Y' : Geo.Point)
    (hAQprime : A ≠ Q')
    (hAQprimeYprime : Geo.Between A Q' Y')
    (hXprimePprimeA : Geo.Between X' P' A)
    (hAQprimeXprimePprime : Geo.Congruent A Q' X' P')
    (hQprimeYprimePprimeA : Geo.Congruent Q' Y' P' A) :
    Geo.Congruent A Y' X' A := by
  exact
    tarski_l2_11_nondegenerate (Geo := Geo) A Q' Y' X' P' A hAQprimeYprime hXprimePprimeA hAQprime hAQprimeXprimePprime hQprimeYprimePprimeA

theorem tarski_l7_13_congruent_AY_AYprime
    [TarskiNeutral Geo]
    (A P Q Q' Y Y' : Geo.Point)
    (hAQ : A ≠ Q)
    (hAQY : Geo.Between A Q Y)
    (hAQprimeYprime : Geo.Between A Q' Y')
    (hAQAQprime : Geo.Congruent A Q A Q')
    (hQYPA : Geo.Congruent Q Y P A)
    (hQprimeYprimePA : Geo.Congruent Q' Y' P A) :
    Geo.Congruent A Y A Y' := by
  have hPAQY : Geo.Congruent P A Q Y :=
    tarski_congruent_symmetry (Geo := Geo) Q Y P A hQYPA
  have hPAQprimeYprime : Geo.Congruent P A Q' Y' :=
    tarski_congruent_symmetry (Geo := Geo) Q' Y' P A hQprimeYprimePA
  have hQYQprimeYprime : Geo.Congruent Q Y Q' Y' :=
    TarskiNeutral.congruent_transitivity (Geo := Geo) P A Q Y Q' Y' hPAQY hPAQprimeYprime
  exact
    tarski_l2_11_nondegenerate (Geo := Geo) A Q Y A Q' Y' hAQY hAQprimeYprime hAQ hAQAQprime hQYQprimeYprime

theorem tarski_l7_13_congruent_XA_YprimeA
    [TarskiNeutral Geo]
    (A X Y Y' : Geo.Point)
    (hAXYA : Geo.Congruent A X Y A)
    (hAYAYprime : Geo.Congruent A Y A Y') :
    Geo.Congruent X A Y' A := by
  have hXAAY : Geo.Congruent X A A Y :=
    tarski_congruent_reverse_both (Geo := Geo) A X Y A hAXYA
  have hAYXA : Geo.Congruent A Y X A :=
    tarski_congruent_symmetry (Geo := Geo) X A A Y hXAAY
  have hAYYprimeA : Geo.Congruent A Y Y' A :=
    (Geometry.Tarski.Geo.congruent_reverse_second Geo A Y A Y').mp hAYAYprime
  exact
    TarskiNeutral.congruent_transitivity (Geo := Geo) A Y X A Y' A hAYXA hAYYprimeA

theorem tarski_l7_13_congruent_AXprime_AY
    [TarskiNeutral Geo]
    (A X' Y Y' : Geo.Point)
    (hAYprimeXprimeA : Geo.Congruent A Y' X' A)
    (hAYAYprime : Geo.Congruent A Y A Y') :
    Geo.Congruent A X' A Y := by
  have hYprimeAAXprime : Geo.Congruent Y' A A X' :=
    tarski_congruent_reverse_both (Geo := Geo) A Y' X' A hAYprimeXprimeA
  have hYAYprimeA : Geo.Congruent Y A Y' A :=
    tarski_congruent_reverse_both (Geo := Geo) A Y A Y' hAYAYprime
  have hYprimeAYA : Geo.Congruent Y' A Y A :=
    tarski_congruent_symmetry (Geo := Geo) Y A Y' A hYAYprimeA
  have hAXprimeYA : Geo.Congruent A X' Y A :=
    TarskiNeutral.congruent_transitivity (Geo := Geo) Y' A A X' Y A hYprimeAAXprime hYprimeAYA
  exact
    (Geometry.Tarski.Geo.congruent_reverse_second Geo A X' Y A).mp hAXprimeYA

theorem tarski_l7_13_congruent_AX_AXprime
    [TarskiNeutral Geo]
    (A X X' Y : Geo.Point)
    (hAXYA : Geo.Congruent A X Y A)
    (hAXprimeAY : Geo.Congruent A X' A Y) :
    Geo.Congruent A X A X' := by
  have hYAAX : Geo.Congruent Y A A X :=
    tarski_congruent_symmetry (Geo := Geo) A X Y A hAXYA
  have hAYAX : Geo.Congruent A Y A X :=
    (Geometry.Tarski.Geo.congruent_reverse_first Geo Y A A X).mp hYAAX
  have hAYAXprime : Geo.Congruent A Y A X' :=
    tarski_congruent_symmetry (Geo := Geo) A X' A Y hAXprimeAY
  exact
    TarskiNeutral.congruent_transitivity (Geo := Geo) A Y A X A X' hAYAX hAYAXprime

theorem tarski_l7_13_congruent_XXprime_YprimeY
    [TarskiNeutral Geo]
    (A X X' Y Y' : Geo.Point)
    (hXA : X ≠ A)
    (hXAXprime : Geo.Between X A X')
    (hYAYprime : Geo.Between Y A Y')
    (hXAYprimeA : Geo.Congruent X A Y' A)
    (hAXprimeAY : Geo.Congruent A X' A Y) :
    Geo.Congruent X X' Y' Y := by
  have hYprimeAY : Geo.Between Y' A Y :=
    tarski_between_symmetry (Geo := Geo) Y A Y' hYAYprime
  exact
    tarski_l2_11_nondegenerate (Geo := Geo) X A X' Y' A Y hXAXprime hYprimeAY hXA hXAYprimeA hAXprimeAY

theorem tarski_l7_13_congruent_XprimeYprime_YX
    [TarskiNeutral Geo]
    (A X X' Y Y' : Geo.Point)
    (hXA : X ≠ A)
    (hXAXprime : Geo.Between X A X')
    (hXAYprimeA : Geo.Congruent X A Y' A)
    (hAXprimeAY : Geo.Congruent A X' A Y)
    (hXXprimeYprimeY : Geo.Congruent X X' Y' Y) :
    Geo.Congruent X' Y' Y X := by
  have hColXAXprime : TarskiCollinear Geo X A X' := Or.inl hXAXprime
  have hXYprimeYprimeX : Geo.Congruent X Y' Y' X := by
    have hXYprimeXYprime : Geo.Congruent X Y' X Y' :=
      tarski_congruent_reflexivity (Geo := Geo) X Y'
    exact
      (Geometry.Tarski.Geo.congruent_reverse_second Geo X Y' X Y').mp hXYprimeXYprime
  have hAXAYprime : Geo.Congruent A X A Y' :=
    tarski_congruent_reverse_both (Geo := Geo) X A Y' A hXAYprimeA
  have hAYprimeAX : Geo.Congruent A Y' A X :=
    tarski_congruent_symmetry (Geo := Geo) A X A Y' hAXAYprime
  exact
    tarski_l4_16 (Geo := Geo) X A X' Y' Y' A Y X hColXAXprime hXA hXAYprimeA hAXprimeAY hXXprimeYprimeY hXYprimeYprimeX hAYprimeAX

theorem tarski_l7_13_congruent_QX_QprimeXprime
    [TarskiNeutral Geo]
    (A Q Q' X X' Y Y' : Geo.Point)
    (hYQA : Geo.Between Y Q A)
    (hAQprimeYprime : Geo.Between A Q' Y')
    (hAYAYprime : Geo.Congruent A Y A Y')
    (hQAQprimeA : Geo.Congruent Q A Q' A)
    (hXprimeYprimeYX : Geo.Congruent X' Y' Y X)
    (hAXAXprime : Geo.Congruent A X A X') :
    Geo.Congruent Q X Q' X' := by
  have hYprimeQprimeA : Geo.Between Y' Q' A :=
    tarski_between_symmetry (Geo := Geo) A Q' Y' hAQprimeYprime
  have hYAYprimeA : Geo.Congruent Y A Y' A :=
    tarski_congruent_reverse_both (Geo := Geo) A Y A Y' hAYAYprime
  have hYXXprimeYprime : Geo.Congruent Y X X' Y' :=
    tarski_congruent_symmetry (Geo := Geo) X' Y' Y X hXprimeYprimeYX
  have hYXYprimeXprime : Geo.Congruent Y X Y' X' :=
    (Geometry.Tarski.Geo.congruent_reverse_second Geo Y X X' Y').mp hYXXprimeYprime
  exact
    tarski_inner_five_segment (Geo := Geo) Y Y' Q Q' A A X X' hYQA hYprimeQprimeA hYAYprimeA hQAQprimeA hYXYprimeXprime hAXAXprime

theorem tarski_l7_13_final_inner_step
    [TarskiNeutral Geo]
    (A P Q P' Q' X X' : Geo.Point)
    (hPmid : TarskiIsMidpoint Geo A P' P)
    (hQmid : TarskiIsMidpoint Geo A Q' Q)
    (hAPX : Geo.Between A P X)
    (hXprimePprimeA : Geo.Between X' P' A)
    (hAXAXprime : Geo.Congruent A X A X')
    (hQXQprimeXprime : Geo.Congruent Q X Q' X') :
    Geo.Congruent P Q P' Q' := by
  rcases hPmid with ⟨_, hPprimeAAP⟩
  rcases hQmid with ⟨_, hQprimeAAQ⟩
  have hXPA : Geo.Between X P A :=
    tarski_between_symmetry (Geo := Geo) A P X hAPX
  have hXAXprimeA : Geo.Congruent X A X' A :=
    tarski_congruent_reverse_both (Geo := Geo) A X A X' hAXAXprime
  have hAPPprimeA : Geo.Congruent A P P' A :=
    tarski_congruent_symmetry (Geo := Geo) P' A A P hPprimeAAP
  have hPAPprimeA : Geo.Congruent P A P' A :=
    (Geometry.Tarski.Geo.congruent_reverse_first Geo A P P' A).mp hAPPprimeA
  have hXQXprimeQprime : Geo.Congruent X Q X' Q' :=
    tarski_congruent_reverse_both (Geo := Geo) Q X Q' X' hQXQprimeXprime
  have hAQQprimeA : Geo.Congruent A Q Q' A :=
    tarski_congruent_symmetry (Geo := Geo) Q' A A Q hQprimeAAQ
  have hAQAQprime : Geo.Congruent A Q A Q' :=
    (Geometry.Tarski.Geo.congruent_reverse_second Geo A Q Q' A).mp hAQQprimeA
  exact
    tarski_inner_five_segment (Geo := Geo) X X' P P' A A Q Q' hXPA hXprimePprimeA hXAXprimeA hPAPprimeA hXQXprimeQprime hAQAQprime

theorem tarski_central_symmetry_congruent
    [TarskiNeutral Geo]
    (M P Q P' Q' : Geo.Point)
    (hPmid : TarskiIsMidpoint Geo M P P')
    (hQmid : TarskiIsMidpoint Geo M Q Q') :
    Geo.Congruent P Q P' Q' := by
  by_cases hPM : P = M
  · subst P
    have hPprimeM : P' = M := by
      have hMMPprimeM : Geo.Congruent M M P' M :=
        (Geometry.Tarski.Geo.congruent_reverse_second Geo M M M P').mp hPmid.2
      have hPprimeMMM : Geo.Congruent P' M M M :=
        tarski_congruent_symmetry (Geo := Geo) M M P' M hMMPprimeM
      exact
        TarskiNeutral.congruent_identity (Geo := Geo) P' M M hPprimeMMM
    subst P'
    exact
      (Geometry.Tarski.Geo.congruent_reverse_first Geo Q M M Q').mp hQmid.2
  · by_cases hQM : Q = M
    · subst Q
      have hQprimeM : Q' = M := by
        have hMMQprimeM : Geo.Congruent M M Q' M :=
          (Geometry.Tarski.Geo.congruent_reverse_second Geo M M M Q').mp hQmid.2
        have hQprimeMMM : Geo.Congruent Q' M M M :=
          tarski_congruent_symmetry (Geo := Geo) M M Q' M hMMQprimeM
        exact
          TarskiNeutral.congruent_identity (Geo := Geo) Q' M M hQprimeMMM
      subst Q'
      exact
        (Geometry.Tarski.Geo.congruent_reverse_second Geo P M M P').mp hPmid.2
    · have hPmidRev : TarskiIsMidpoint Geo M P' P := by
        constructor
        · exact tarski_between_symmetry (Geo := Geo) P M P' hPmid.1
        · have hMPPPprimeM : Geo.Congruent M P P' M :=
            tarski_congruent_reverse_both (Geo := Geo) P M M P' hPmid.2
          exact
            tarski_congruent_symmetry (Geo := Geo) M P P' M hMPPPprimeM
      have hQmidRev : TarskiIsMidpoint Geo M Q' Q := by
        constructor
        · exact tarski_between_symmetry (Geo := Geo) Q M Q' hQmid.1
        · have hMQQprimeM : Geo.Congruent M Q Q' M :=
            tarski_congruent_reverse_both (Geo := Geo) Q M M Q' hQmid.2
          exact
            tarski_congruent_symmetry (Geo := Geo) M Q Q' M hMQQprimeM
      obtain
        ⟨X, X', Y, Y', hPprimePX, hPXQA, hXPprimeXprime, hPprimeXprimeQM, hQprimeQY, hQYPA, hYQprimeYprime, hQprimeYprimePA⟩ :=
        tarski_l7_13_aux (Geo := Geo) M P Q P' Q'
      obtain
        ⟨hYMQprime, hPprimeMX, hMPX, hYQM, hMQprimeYprime, hXprimePprimeM, hXMXprime, hYMYprime⟩ :=
        tarski_l7_13_betweenness (Geo := Geo) M P Q P' Q' X X' Y Y' hPM hPmidRev hQmidRev hPprimePX hXPprimeXprime hQprimeQY hYQprimeYprime
      have hMX_YM : Geo.Congruent M X Y M :=
        tarski_l7_13_congruent_AX_YA (Geo := Geo) M P Q X Y hPM hMPX hYQM hPXQA hQYPA
      have hQMPprimeXprime : Geo.Congruent Q M P' X' :=
        tarski_congruent_symmetry (Geo := Geo) P' X' Q M hPprimeXprimeQM
      have hMQprimePprimeXprime : Geo.Congruent M Q' P' X' :=
        TarskiNeutral.congruent_transitivity (Geo := Geo) Q M M Q' P' X' hQmid.2 hQMPprimeXprime
      have hMQprimeXprimePprime : Geo.Congruent M Q' X' P' :=
        (Geometry.Tarski.Geo.congruent_reverse_second Geo M Q' P' X').mp hMQprimePprimeXprime
      have hPMPprimeM : Geo.Congruent P M P' M :=
        (Geometry.Tarski.Geo.congruent_reverse_second Geo P M M P').mp hPmid.2
      have hQprimeYprimePprimeM : Geo.Congruent Q' Y' P' M :=
        TarskiNeutral.congruent_transitivity (Geo := Geo) P M Q' Y' P' M
          (tarski_congruent_symmetry (Geo := Geo) Q' Y' P M hQprimeYprimePA) hPMPprimeM
      have hMYprimeXprimeM : Geo.Congruent M Y' X' M :=
        tarski_l7_13_congruent_AYprime_XprimeA (Geo := Geo) M P' Q' X' Y'
          (by
            intro hMQprime
            have hQprimeM : Q' = M := hMQprime.symm
            subst Q'
            have hQM' : Q = M := by
              exact TarskiNeutral.congruent_identity (Geo := Geo) Q M M hQmid.2
            exact hQM hQM')
          hMQprimeYprime hXprimePprimeM hMQprimeXprimePprime hQprimeYprimePprimeM
      have hMQMQprime : Geo.Congruent M Q M Q' :=
        (Geometry.Tarski.Geo.congruent_reverse_second Geo M Q Q' M).mp
          (tarski_congruent_reverse_both (Geo := Geo) Q M M Q' hQmid.2)
      have hMQY : Geo.Between M Q Y :=
        tarski_between_symmetry (Geo := Geo) Y Q M hYQM
      have hMY_MYprime : Geo.Congruent M Y M Y' :=
        tarski_l7_13_congruent_AY_AYprime (Geo := Geo) M P Q Q' Y Y'
          (by
            intro hMQ
            exact hQM hMQ.symm)
          hMQY hMQprimeYprime hMQMQprime hQYPA hQprimeYprimePA
      have hXM_YprimeM : Geo.Congruent X M Y' M :=
        tarski_l7_13_congruent_XA_YprimeA (Geo := Geo) M X Y Y' hMX_YM hMY_MYprime
      have hMXprime_MY : Geo.Congruent M X' M Y :=
        tarski_l7_13_congruent_AXprime_AY (Geo := Geo) M X' Y Y' hMYprimeXprimeM hMY_MYprime
      have hXXprime_YprimeY : Geo.Congruent X X' Y' Y :=
        tarski_l7_13_congruent_XXprime_YprimeY (Geo := Geo) M X X' Y Y'
          (by
            intro hXM
            subst X
            have hMPM : Geo.Between M P M := hMPX
            have hMPeq : M = P :=
              TarskiNeutral.between_identity (Geo := Geo) M P hMPM
            exact hPM hMPeq.symm)
          hXMXprime hYMYprime hXM_YprimeM hMXprime_MY
      have hXprimeYprime_YX : Geo.Congruent X' Y' Y X :=
        tarski_l7_13_congruent_XprimeYprime_YX (Geo := Geo) M X X' Y Y'
          (by
            intro hXM
            subst X
            have hMPM : Geo.Between M P M := hMPX
            have hMPeq : M = P :=
              TarskiNeutral.between_identity (Geo := Geo) M P hMPM
            exact hPM hMPeq.symm)
          hXMXprime hXM_YprimeM hMXprime_MY hXXprime_YprimeY
      have hMX_MXprime : Geo.Congruent M X M X' :=
        tarski_l7_13_congruent_AX_AXprime (Geo := Geo) M X X' Y hMX_YM hMXprime_MY
      have hQM_QprimeM : Geo.Congruent Q M Q' M :=
        (Geometry.Tarski.Geo.congruent_reverse_second Geo Q M M Q').mp hQmid.2
      have hQX_QprimeXprime : Geo.Congruent Q X Q' X' :=
        tarski_l7_13_congruent_QX_QprimeXprime (Geo := Geo) M Q Q' X X' Y Y' hYQM hMQprimeYprime hMY_MYprime hQM_QprimeM hXprimeYprime_YX hMX_MXprime
      exact
        tarski_l7_13_final_inner_step (Geo := Geo) M P Q P' Q' X X' hPmidRev hQmidRev hMPX hXprimePprimeM hMX_MXprime hQX_QprimeXprime


theorem tarski_midpoint_symmetry
    [TarskiNeutral Geo]
    (M A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B) :
    TarskiIsMidpoint Geo M B A := by
  constructor
  · exact tarski_between_symmetry (Geo := Geo) A M B hM.1
  · have h₁ : Geo.Congruent M A B M :=
      tarski_congruent_reverse_both (Geo := Geo) A M M B hM.2
    exact tarski_congruent_symmetry (Geo := Geo) M A B M h₁


------------------------------------------------------------
-- Równoległość i teoria równoległoboku
------------------------------------------------------------

theorem tarski_parallel_strict_collinear_right
    [TarskiNeutral Geo]
    (A X B P C : Geo.Point)
    (hPar : TarskiParallelStrict Geo A X C P)
    (hBPC : TarskiCollinear Geo B P C)
    (hBP : B = P → False) :
    TarskiParallelStrict Geo A X B P := by
  rcases hPar with ⟨hAX, hCP, hNoInt⟩
  constructor
  · exact hAX
  constructor
  · exact hBP
  · intro hInt
    apply hNoInt
    rcases hInt with ⟨Y, hYAX, hYBP⟩
    have hYPB : TarskiCollinear Geo Y P B :=
      tarski_collinear_symmetry Geo Y B P hYBP
    have hPCB : TarskiCollinear Geo P C B :=
      (tarski_collinear_cycle Geo B P C).mp hBPC
    have hPBC : TarskiCollinear Geo P B C :=
      tarski_collinear_symmetry Geo P C B hPCB
    have hPB : P = B → False := by
      intro hPB
      exact hBP hPB.symm
    have hYPC : TarskiCollinear Geo Y P C :=
      tarski_collinear_trans Geo Y P B C hPB hYPB hPBC
    have hYCP : TarskiCollinear Geo Y C P :=
      tarski_collinear_symmetry Geo Y P C hYPC
    exact ⟨Y, hYAX, hYCP⟩

theorem tarski_midpoint_ne_first
    [TarskiNeutral Geo]
    (P B C : Geo.Point)
    (hBC : B = C → False)
    (hP : TarskiIsMidpoint Geo P B C) :
    B = P → False := by
  intro hBP
  subst B
  have hPCPP : Geo.Congruent P C P P :=
    tarski_congruent_symmetry (Geo := Geo) P P P C hP.2
  have hPC : P = C :=
    TarskiNeutral.congruent_identity (Geo := Geo) P C P hPCPP
  exact hBC hPC

theorem tarski_midpoint_noncol_left
    [TarskiNeutral Geo]
    (A B C P : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C) :
    Not (TarskiCollinear Geo A P B) := by
  intro hAPB
  have hBC : B = C → False :=
    tarski_noncollinear_ne_second_third Geo A B C hNonCol
  have hBP : B = P → False :=
    tarski_midpoint_ne_first Geo P B C hBC hP
  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1
  have hABP : TarskiCollinear Geo A B P :=
    tarski_collinear_symmetry Geo A P B hAPB
  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans Geo A B P C hBP hABP hBPC
  exact hNonCol hABC

theorem tarski_parallel_strict_symm_right
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hPar : TarskiParallelStrict Geo A B C D) :
    TarskiParallelStrict Geo A B D C := by
  rcases hPar with ⟨hAB, hCD, hNoInt⟩
  constructor
  · exact hAB
  constructor
  · intro hDC
    exact hCD hDC.symm
  · intro hInt
    apply hNoInt
    rcases hInt with ⟨X, hXAB, hXDC⟩
    have hXCD : TarskiCollinear Geo X C D :=
      tarski_collinear_symmetry Geo X D C hXDC
    exact ⟨X, hXAB, hXCD⟩

/-!
## Three-midpoint configuration
-/

theorem tarski_midsegment_aux_congruent
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    Geo.Congruent A X B P := by
  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry Geo Q P X hQPX
  have hAXCP : Geo.Congruent A X C P :=
    tarski_central_symmetry_congruent Geo Q A X C P hQ hQXP
  have hPCBP : Geo.Congruent P C B P :=
    tarski_congruent_symmetry (Geo := Geo) B P P C hP.2
  have hPCCP : Geo.Congruent P C C P :=
    TarskiNeutral.congruent_reversal (Geo := Geo) P C
  have hCPBP : Geo.Congruent C P B P :=
    TarskiNeutral.congruent_transitivity (Geo := Geo) P C C P B P hPCCP hPCBP
  have hCPAX : Geo.Congruent C P A X :=
    tarski_congruent_symmetry (Geo := Geo) A X C P hAXCP
  exact
    TarskiNeutral.congruent_transitivity (Geo := Geo) C P A X B P hCPAX hCPBP

theorem tarski_midsegment_aux_ne
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    A = X → False := by
  intro hAX
  subst X
  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second Geo A B C P hNonCol hP
  have hAC : A = C → False := by
    intro hAC
    subst C
    apply hAPC
    right
    left
    exact tarski_between_reflexivity (Geo := Geo) P A
  have hQCA : TarskiIsMidpoint Geo Q C A :=
    tarski_midpoint_symmetry Geo Q A C hQ
  have hQA : Q = A → False :=
    tarski_midpoint_ne_second Geo Q C A (fun hCA => hAC hCA.symm) hQCA
  have hPQA : TarskiCollinear Geo P Q A := by
    left
    exact hQPX.1
  have hQAC : TarskiCollinear Geo Q A C := by
    have hQCAcol : TarskiCollinear Geo Q C A := by
      right
      right
      exact hQ.1
    exact tarski_collinear_symmetry Geo Q C A hQCAcol
  have hPQC : TarskiCollinear Geo P Q C :=
    tarski_collinear_trans Geo P Q A C hQA hPQA hQAC
  have hAP : A = P → False := by
    intro hAPeq
    subst P
    apply hAPC
    left
    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity (Geo := Geo) C A
    exact tarski_between_symmetry (Geo := Geo) C A A hCAA
  have hQAP : TarskiIsMidpoint Geo Q A P :=
    tarski_midpoint_symmetry Geo Q P A hQPX
  have hQP : Q = P → False :=
    tarski_midpoint_ne_second Geo Q A P hAP hQAP
  have hAPQ : TarskiCollinear Geo A P Q := by
    have hQAPcol : TarskiCollinear Geo Q A P := by
      right
      right
      exact hQPX.1
    exact (tarski_collinear_cycle Geo Q A P).mp hQAPcol
  have hAPC' : TarskiCollinear Geo A P C :=
    tarski_collinear_trans Geo A P Q C (fun hPQ => hQP hPQ.symm) hAPQ hPQC
  exact hAPC hAPC'

theorem tarski_midsegment_aux_noncol
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    Not (TarskiCollinear Geo A X Q) := by
  intro hAXQ
  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second Geo A B C P hNonCol hP
  have hAC : A = C → False :=
    fun hAC =>
      hNonCol (by
        right
        left
        rw [hAC]
        exact tarski_between_reflexivity (Geo := Geo) B C)
  have hAQ : A = Q → False :=
    tarski_midpoint_ne_first Geo Q A C hAC hQ
  have hAQX : TarskiCollinear Geo A Q X :=
    tarski_collinear_symmetry Geo A X Q hAXQ
  have hQXP : TarskiCollinear Geo Q X P := by
    right
    right
    exact hQPX.1
  have hPX : P = X → False := by
    intro hPX
    have hPQP : Geo.Between P Q P := by
      simpa [hPX] using hQPX.1
    have hPQ : P = Q :=
      TarskiNeutral.between_identity (Geo := Geo) P Q hPQP
    apply hAPC
    simpa [hPQ] using (tarski_midpoint_collinear Geo Q A C hQ)
  have hQX : Q = X → False :=
    tarski_midpoint_ne_second Geo Q P X hPX hQPX
  have hAQP : TarskiCollinear Geo A Q P :=
    tarski_collinear_trans Geo A Q X P hQX hAQX hQXP
  have hAPQ : TarskiCollinear Geo A P Q :=
    tarski_collinear_symmetry Geo A Q P hAQP
  have hQAC : TarskiCollinear Geo Q A C :=
    tarski_collinear_symmetry Geo Q C A
      ((tarski_collinear_cycle Geo A Q C).mp (tarski_midpoint_collinear Geo Q A C hQ))
  have hPQC : TarskiCollinear Geo P Q C :=
    tarski_collinear_trans Geo P Q A C (fun hQA => hAQ hQA.symm)
      ((tarski_collinear_cycle Geo A P Q).mp hAPQ) hQAC
  have hPQ : P = Q → False := by
    intro hPQ
    subst P
    apply hAPC
    exact tarski_midpoint_collinear Geo Q A C hQ
  have hAPC' : TarskiCollinear Geo A P C :=
    tarski_collinear_trans Geo A P Q C hPQ hAPQ hPQC
  exact hAPC hAPC'

theorem tarski_midsegment_aux_parallel
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A X C P := by
  have hAX : A = X → False :=
    tarski_midsegment_aux_ne Geo A B C P Q X hNonCol hP hQ hQPX
  have hAXQ : Not (TarskiCollinear Geo A X Q) :=
    tarski_midsegment_aux_noncol Geo A B C P Q X hNonCol hP hQ hQPX
  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry Geo Q P X hQPX
  exact
    tarski_central_symmetry_parallel Geo Q A X C P hAXQ hQ hQXP

theorem tarski_midsegment_aux_parallel_BP
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A X B P := by
  have hParAXCP : TarskiParallelStrict Geo A X C P :=
    tarski_midsegment_aux_parallel Geo A B C P Q X hNonCol hP hQ hQPX
  have hBC : B = C → False :=
    tarski_noncollinear_ne_second_third Geo A B C hNonCol
  have hBP : B = P → False :=
    tarski_midpoint_ne_first Geo P B C hBC hP
  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1
  exact
    tarski_parallel_strict_collinear_right Geo A X B P C hParAXCP hBPC hBP

theorem tarski_midsegment_parallelogram_cases
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelogram Geo A X B P ∨
    TarskiParallelogram Geo A X P B := by
  have hCong : Geo.Congruent A X B P :=
    tarski_midsegment_aux_congruent Geo A B C P Q X hP hQ hQPX
  have hPar : TarskiParallelStrict Geo A X B P :=
    tarski_midsegment_aux_parallel_BP Geo A B C P Q X hNonCol hP hQ hQPX
  exact
    tarski_parallel_congruent_parallelogram_cases Geo A X B P hPar hCong

theorem tarski_midsegment_first_parallelogram_impossible
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X)
    (hPar : TarskiParallelogram Geo A X B P) :
    False := by
  rcases hPar with ⟨_hNondeg, M, hMAB, hMXP⟩
  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry Geo Q P X hQPX
  have hMQ : M = Q :=
    tarski_midpoint_unique Geo M Q X P hMXP hQXP
  subst M
  have hQAB : TarskiIsMidpoint Geo Q A B := hMAB
  have hAB : A = B → False := by
    intro hABeq
    subst B
    apply hNonCol
    left
    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity (Geo := Geo) C A
    exact tarski_between_symmetry (Geo := Geo) C A A hCAA
  have hQBA : TarskiIsMidpoint Geo Q B A :=
    tarski_midpoint_symmetry Geo Q A B hQAB
  have hQA : Q = A → False :=
    tarski_midpoint_ne_second Geo Q B A (fun hBA => hAB hBA.symm) hQBA
  have hQB : Q = B → False :=
    tarski_midpoint_ne_second Geo Q A B hAB hQAB
  have hAQB : TarskiCollinear Geo A Q B := by
    left
    exact hQAB.1
  have hABQ : TarskiCollinear Geo A B Q :=
    tarski_collinear_symmetry Geo A Q B hAQB
  have hBQA : TarskiCollinear Geo B Q A :=
    (tarski_collinear_cycle Geo A B Q).mp hABQ
  have hAQC : TarskiCollinear Geo A Q C := by
    left
    exact hQ.1
  have hQCA : TarskiCollinear Geo Q C A :=
    (tarski_collinear_cycle Geo A Q C).mp hAQC
  have hQAC : TarskiCollinear Geo Q A C :=
    tarski_collinear_symmetry Geo Q C A hQCA
  have hBQC : TarskiCollinear Geo B Q C :=
    tarski_collinear_trans Geo B Q A C hQA hBQA hQAC
  have hBQ : B = Q → False := by
    intro hBQ
    exact hQB hBQ.symm
  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans Geo A B Q C hBQ hABQ hBQC
  exact hNonCol hABC

theorem tarski_midsegment_second_parallelogram
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelogram Geo A X P B := by
  have hCases :
      TarskiParallelogram Geo A X B P ∨
      TarskiParallelogram Geo A X P B :=
    tarski_midsegment_parallelogram_cases Geo A B C P Q X hNonCol hP hQ hQPX
  rcases hCases with hBad | hGood
  · exact False.elim
      (tarski_midsegment_first_parallelogram_impossible Geo A B C P Q X hNonCol hQ hQPX hBad)
  · exact hGood

theorem tarski_parallelogram_opposite_parallel
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A C D))
    (hPar : TarskiParallelogram Geo A B C D) :
    TarskiParallelStrict Geo A D B C := by
  rcases hPar with ⟨_, M, hMAC, hMBD⟩

  have hDAC : Not (TarskiCollinear Geo D A C) := by
    intro h
    exact hNonCol ((tarski_collinear_cycle Geo D A C).mp h)

  have hDMA : Not (TarskiCollinear Geo D M A) :=
    tarski_midpoint_noncol_left Geo D A C M hDAC hMAC

  have hADM : Not (TarskiCollinear Geo A D M) := by
    intro h
    exact hDMA ((tarski_collinear_cycle Geo A D M).mp h)

  have hMDB : TarskiIsMidpoint Geo M D B :=
    tarski_midpoint_symmetry Geo M B D hMBD

  have hParADCB : TarskiParallelStrict Geo A D C B :=
    tarski_central_symmetry_parallel
      Geo M A D C B hADM hMAC hMDB

  exact
    tarski_parallel_strict_symm_right
      Geo A D C B hParADCB

theorem tarski_midsegment_parallel_AB_XP
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A B X P := by
  have hPar :
      TarskiParallelogram Geo A X P B :=
    tarski_midsegment_second_parallelogram Geo A B C P Q X hNonCol hP hQ hQPX
  have hAPB : Not (TarskiCollinear Geo A P B) :=
    tarski_midpoint_noncol_left Geo A B C P hNonCol hP
  exact
    tarski_parallelogram_opposite_parallel Geo A X P B hAPB hPar

theorem tarski_midpoint_reverse
    [TarskiNeutral Geo]
    (M A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B) :
    TarskiIsMidpoint Geo M B A := by
  rcases hM with ⟨hBet, hCong⟩
  constructor
  ·
    exact
      tarski_between_symmetry
        (Geo := Geo)
        A M B
        hBet
  ·
    have h₁ : Geo.Congruent M A B M := by
      exact
        tarski_congruent_reverse_both
          (Geo := Geo)
          A M M B
          hCong

    exact
      tarski_congruent_symmetry
        (Geo := Geo)
        M A B M
        h₁

theorem tarski_congruent_commutativity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent B A D C := by
  exact
    tarski_congruent_reverse_both
      (Geo := Geo)
      A B C D
      h

theorem tarski_congruent_4321
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent D C B A := by
  have h1 : Geo.Congruent B A D C :=
    tarski_congruent_commutativity
      (Geo := Geo)
      A B C D
      h
  exact
    tarski_congruent_symmetry
      (Geo := Geo)
      B A D C
      h1

theorem tarski_congruent_right_commutativity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent A B D C := by
  exact
    (Geometry.Tarski.Geo.congruent_reverse_second Geo A B C D).mp hABCD

theorem tarski_congruent_left_commutativity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent B A C D := by
  exact
    (Geometry.Tarski.Geo.congruent_reverse_first Geo A B C D).mp hABCD

theorem tarski_congruent_3421
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent C D B A := by

  have h1 : Geo.Congruent C D A B :=
    tarski_congruent_symmetry
      (Geo := Geo)
      A B C D
      h

  exact
    tarski_congruent_right_commutativity
      (Geo := Geo)
      C D A B
      h1
theorem tarski_congruent_4312
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent D C A B := by

  have h1 : Geo.Congruent C D A B :=
    tarski_congruent_symmetry
      (Geo := Geo)
      A B C D
      h

  exact
    tarski_congruent_left_commutativity
      (Geo := Geo)
      C D A B
      h1

theorem tarski_midpoint_unique_prim
    [TarskiNeutral Geo]
    (M A B C : Geo.Point)
    (hMAB : TarskiIsMidpoint Geo M A B)
    (hMAC : TarskiIsMidpoint Geo M A C) :
    B = C := by

  have hMBA : TarskiIsMidpoint Geo M B A :=
    tarski_midpoint_reverse
      (Geo := Geo)
      M A B
      hMAB

  have hMCA : TarskiIsMidpoint Geo M C A :=
    tarski_midpoint_reverse
      (Geo := Geo)
      M A C
      hMAC

  rcases hMBA with ⟨hBetB, hCongB⟩
  rcases hMCA with ⟨hBetC, hCongC⟩

  by_cases hMA : M = A

  · subst hMA

    have hBM : B = M := by
      exact
        TarskiNeutral.congruent_identity
          (Geo := Geo)
          B
          M
          M
          hCongB

    have hCM : C = M := by
      exact
        TarskiNeutral.congruent_identity
          (Geo := Geo)
          C
          M
          M
          hCongC

    subst B
    subst C
    rfl

  ·
    have hAB : Geo.Between A M B := by
      exact
        tarski_between_symmetry
          (Geo := Geo)
          B M A
          hBetB

    have hAC : Geo.Between A M C := by
      exact
        tarski_between_symmetry
          (Geo := Geo)
          C M A
          hBetC

    have hCongB' : Geo.Congruent M B M A := by
      exact
        tarski_congruent_left_commutativity
          (Geo := Geo)
          B M M A
          hCongB

    have hCongC' : Geo.Congruent M C M A := by
      exact
        tarski_congruent_left_commutativity
          (Geo := Geo)
          C M M A
          hCongC

    have hAM : A ≠ M := by
      intro h
      exact hMA h.symm

    exact
      tarski_construction_uniqueness
        (Geo := Geo)
        A
        M
        B
        C
        M
        A
        hAM
        hAB
        hAC
        hCongB'
        hCongC'


theorem tarski_parallelogram_opposite_parallel_prim
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A C D))
    (hPar : TarskiParallelogram Geo A B C D) :
    TarskiParallelStrict Geo A D B C := by
  rcases hPar with ⟨_, M, hMAC, hMBD⟩

  have hDAC : Not (TarskiCollinear Geo D A C) := by
    intro h
    exact hNonCol ((tarski_collinear_cycle Geo D A C).mp h)

  have hDMA : Not (TarskiCollinear Geo D M A) :=
    tarski_midpoint_noncol_left Geo D A C M hDAC hMAC

  have hADM : Not (TarskiCollinear Geo A D M) := by
    intro h
    exact hDMA ((tarski_collinear_cycle Geo A D M).mp h)

  have hMDB : TarskiIsMidpoint Geo M D B :=
    tarski_midpoint_symmetry Geo M B D hMBD

  have hParADCB : TarskiParallelStrict Geo A D C B :=
    tarski_central_symmetry_parallel
      Geo M A D C B hADM hMAC hMDB

  exact
    tarski_parallel_strict_symm_right
      Geo A D C B hParADCB

theorem tarski_between_congruent_eq
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C)
    (hCong : Geo.Congruent A B A C) :
    B = C := by
  have hBCBC : Geo.Congruent B C B C :=
    tarski_congruent_reflexivity
      (Geo := Geo) B C

  have hBCCB : Geo.Congruent B C C B :=
    (Geometry.Tarski.Geo.congruent_reverse_second
      Geo B C B C).mp hBCBC

  have hACAB : Geo.Congruent A C A B :=
    tarski_congruent_symmetry
      (Geo := Geo) A B A C hCong

  have hACB : Geo.Between A C B :=
    tarski_l4_6
      (Geo := Geo)
      A B C
      A C B
      hABC
      hCong
      hBCCB
      hACAB

  have hBCB : Geo.Between B C B :=
    tarski_between_exchange3
      (Geo := Geo)
      A B C B
      hABC
      hACB

  exact
    TarskiNeutral.between_identity
      (Geo := Geo) B C hBCB


theorem tarski_collinear_equidistant_midpoint_cases
    [TarskiNeutral Geo]
    (M A B : Geo.Point)
    (hCol : TarskiCollinear Geo A M B)
    (hCong : Geo.Congruent M A M B) :
    A = B ∨ TarskiIsMidpoint Geo M A B := by
  rcases hCol with hAMB | hMAB | hABM

  · right
    constructor
    · exact hAMB
    · exact
        (Geometry.Tarski.Geo.congruent_reverse_first
          Geo A M M B).mpr hCong

  · left
    have hMBA : Geo.Congruent M B M A :=
      tarski_congruent_symmetry
        (Geo := Geo) M A M B hCong

    exact
      (tarski_between_congruent_eq
        (Geo := Geo) M B A hMAB hMBA).symm

  · left
    have hMAB : Geo.Between M A B :=
      tarski_between_symmetry
        (Geo := Geo) B A M hABM

    exact
      tarski_between_congruent_eq
        (Geo := Geo) M A B hMAB hCong

theorem tarski_collinear_trans1
    [TarskiNeutral Geo]
    (P Q A B : Geo.Point)
    (hPQ : P ≠ Q)
    (hPQA : TarskiCollinear Geo P Q A)
    (hPQB : TarskiCollinear Geo P Q B) :
    TarskiCollinear Geo P A B := by

  have hQAP : TarskiCollinear Geo Q A P :=
    tarski_collinear_rotate
      Geo P Q A hPQA

  have hAPQ : TarskiCollinear Geo A P Q :=
    tarski_collinear_rotate
      Geo Q A P hQAP

  have hAPB : TarskiCollinear Geo A P B :=
    tarski_collinear_trans
      Geo A P Q B
      hPQ
      hAPQ
      hPQB

  exact
    tarski_collinear_symmetry
      Geo P B A
      (tarski_collinear_rotate Geo A P B hAPB)

theorem tarski_midpoint_midpoint_col
    [TarskiNeutral Geo]
    (A B A' B' M : Geo.Point)
    (hAB : A ≠ B)
    (hMA : TarskiIsMidpoint Geo M A A')
    (hMB : TarskiIsMidpoint Geo M B B')
    (hCol : TarskiCollinear Geo A B B') :
    A' ≠ B' ∧
    TarskiCollinear Geo A A' B' ∧
    TarskiCollinear Geo B A' B' := by

  have hCong : Geo.Congruent A B A' B' :=
    tarski_central_symmetry_congruent
      Geo M A B A' B' hMA hMB

  have hA'B' : A' ≠ B' := by
    intro hEq
    subst B'

    have hABeq : A = B :=
      TarskiNeutral.congruent_identity
        A B A' hCong

    exact hAB hABeq

  have hAMA' : TarskiCollinear Geo A M A' :=
    tarski_midpoint_collinear
      Geo M A A' hMA

  have hBMB' : TarskiCollinear Geo B M B' :=
    tarski_midpoint_collinear
      Geo M B B' hMB

  by_cases hBB' : B = B'

  · subst B'

    have hBM : B = M :=
      TarskiNeutral.between_identity
        (Geo := Geo) B M hMB.left

    subst M

    have hABA' : TarskiCollinear Geo A B A' :=
      tarski_midpoint_collinear
        Geo B A A' hMA

    have hAA'B : TarskiCollinear Geo A A' B :=
      tarski_collinear_symmetry
        Geo A B A' hABA'

    have hBA'B : TarskiCollinear Geo B A' B :=
      Or.inr
        (Or.inl
          (tarski_between_reflexivity
            (Geo := Geo) A' B))

    exact
      And.intro hA'B'
        (And.intro hAA'B hBA'B)

  ·
    have hBB'M : TarskiCollinear Geo B B' M :=
      tarski_collinear_symmetry
        Geo B M B' hBMB'

    have hABM : TarskiCollinear Geo A B M := by
      exact
        tarski_collinear_trans
          Geo A B B' M hBB' hCol hBB'M

    by_cases hAM : A = M

    ·
      have hCongAA' : Geo.Congruent A A A A' := by
        simpa [hAM] using hMA.right

      have hCongA'AA : Geo.Congruent A A' A A :=
        tarski_congruent_symmetry
          (Geo := Geo) A A A A' hCongAA'

      have hAA' : A = A' :=
        TarskiNeutral.congruent_identity
          A A' A hCongA'AA

      subst A'

      have hAAB' : TarskiCollinear Geo A A B' :=
        Or.inr
          (Or.inr
            (tarski_between_reflexivity
              (Geo := Geo) B' A))

      have hBB'A : TarskiCollinear Geo B B' A :=
        tarski_collinear_rotate
          Geo A B B' hCol

      have hBAB' : TarskiCollinear Geo B A B' :=
        tarski_collinear_symmetry
          Geo B B' A hBB'A

      exact
        And.intro hA'B'
          (And.intro hAAB' hBAB')

    ·
      have hAMB : TarskiCollinear Geo A M B :=
        tarski_collinear_symmetry
          Geo A B M hABM

      have hABA' : TarskiCollinear Geo A B A' :=
        tarski_collinear_trans1
          Geo A M B A'
          hAM
          hAMB
          hAMA'

      have hAA'B' : TarskiCollinear Geo A A' B' :=
        tarski_collinear_trans1
          Geo A B A' B'
          hAB
          hABA'
          hCol

      have hBA'A : TarskiCollinear Geo B A' A :=
        tarski_collinear_rotate
          Geo A B A' hABA'

      have hBAA' : TarskiCollinear Geo B A A' :=
        tarski_collinear_symmetry
          Geo B A' A hBA'A

      have hBB'A : TarskiCollinear Geo B B' A :=
        tarski_collinear_rotate
          Geo A B B' hCol

      have hBAB' : TarskiCollinear Geo B A B' :=
        tarski_collinear_symmetry
          Geo B B' A hBB'A

      have hBA'B' : TarskiCollinear Geo B A' B' :=
        tarski_collinear_trans1
          Geo B A A' B'
          hAB.symm
          hBAA'
          hBAB'

      exact
        And.intro hA'B'
          (And.intro hAA'B' hBA'B')




end Tarski

end Geometry

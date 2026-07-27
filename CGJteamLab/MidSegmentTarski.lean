import CGJteamLab.TarskiInterface
import CGJteamLab.TarskiAxioms

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Geo)

--variable [HilbertIncidence Geo]
--variable [TarskiGeometryBaseBridge Geo]


theorem tarski_midpoint_parallelogram_construction
    [TarskiNeutral Geo]
    (A B C P Q : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C) :
    ∃ X : Geo.Point,
      TarskiIsMidpoint Geo Q P X ∧
      TarskiParallelogram Geo A P C X := by

  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second
      Geo A B C P hNonCol hP

  obtain ⟨X, hQPX⟩ :=
    tarski_symmetric_point_exists
      Geo P Q

  have hPar :
      TarskiParallelogram Geo A P C X :=
    tarski_midpoint_parallelogram
      Geo A P C X Q
      hAPC
      hQ
      hQPX

  exact ⟨X, hQPX, hPar⟩


theorem tarski_midsegment_aux_congruent
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    Geo.Congruent A X B P := by

  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry
      Geo Q P X hQPX

  have hAXCP : Geo.Congruent A X C P :=
    tarski_central_symmetry_congruent
      Geo Q A X C P hQ hQXP

  have hPCBP : Geo.Congruent P C B P :=
    tarski_congruent_symmetry
      (Geo := Geo) B P P C hP.2

  have hPCCP : Geo.Congruent P C C P :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo) P C

  have hCPBP : Geo.Congruent C P B P :=
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      P C C P B P
      hPCCP
      hPCBP

  have hCPAX : Geo.Congruent C P A X :=
    tarski_congruent_symmetry
      (Geo := Geo) A X C P hAXCP

  exact
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      C P A X B P
      hCPAX
      hCPBP


theorem tarski_midsegment_aux_ne
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    A = X -> False := by

  intro hAX
  subst X

  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second
      Geo A B C P hNonCol hP

  have hAC : A = C -> False := by
    intro hAC
    subst C
    apply hAPC
    right
    left
    exact tarski_between_reflexivity
      (Geo := Geo) P A

  have hQCA : TarskiIsMidpoint Geo Q C A :=
    tarski_midpoint_symmetry
      Geo Q A C hQ

  have hQA : Q = A -> False :=
    tarski_midpoint_ne_second
      Geo Q C A
      (fun hCA => hAC hCA.symm)
      hQCA

  have hPQA : TarskiCollinear Geo P Q A := by
    left
    exact hQPX.1

  have hQAC : TarskiCollinear Geo Q A C := by
    have hQCAcol : TarskiCollinear Geo Q C A := by
      right
      right
      exact hQ.1
    exact
      tarski_collinear_symmetry
        Geo Q C A hQCAcol

  have hPQC : TarskiCollinear Geo P Q C :=
    tarski_collinear_trans
      Geo P Q A C
      hQA
      hPQA
      hQAC

  have hAP : A = P -> False := by
    intro hAPeq
    subst P
    apply hAPC
    left

    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity
        (Geo := Geo) C A

    exact tarski_between_symmetry
      (Geo := Geo) C A A hCAA

  have hQAP : TarskiIsMidpoint Geo Q A P :=
    tarski_midpoint_symmetry
      Geo Q P A hQPX

  have hQP : Q = P -> False :=
    tarski_midpoint_ne_second
      Geo Q A P
      hAP
      hQAP

  have hAPQ : TarskiCollinear Geo A P Q := by
    have hQAPcol : TarskiCollinear Geo Q A P := by
      right
      right
      exact hQPX.1

    exact
      (tarski_collinear_cycle Geo Q A P).mp hQAPcol

  have hAPC' : TarskiCollinear Geo A P C :=
    tarski_collinear_trans
      Geo A P Q C
      (fun hPQ => hQP hPQ.symm)
      hAPQ
      hPQC

  exact hAPC hAPC'


theorem tarski_midsegment_aux_parallel
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A X C P := by

  have hAX : A = X -> False :=
    tarski_midsegment_aux_ne
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry
      Geo Q P X hQPX

  exact
    tarski_central_symmetry_parallel
      Geo Q A X C P
      hAX
      hQ
      hQXP


theorem tarski_midsegment_aux_parallel_BP
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A X B P := by

  have hParAXCP : TarskiParallelStrict Geo A X C P :=
    tarski_midsegment_aux_parallel
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hBC : B = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A B C hNonCol

  have hBP : B = P -> False :=
    tarski_midpoint_ne_first
      Geo P B C hBC hP

  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1

  exact
    tarski_parallel_strict_collinear_right
      Geo A X B P C
      hParAXCP
      hBPC
      hBP


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
    tarski_midsegment_aux_congruent
      Geo A B C P Q X
      hP hQ hQPX

  have hPar : TarskiParallelStrict Geo A X B P :=
    tarski_midsegment_aux_parallel_BP
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  exact
    tarski_parallel_congruent_parallelogram_cases
      Geo A X B P
      hPar
      hCong


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
    tarski_midpoint_symmetry
      Geo Q P X hQPX

  have hMQ : M = Q :=
    tarski_midpoint_unique
      Geo M Q X P
      hMXP
      hQXP

  subst M

  have hQAB : TarskiIsMidpoint Geo Q A B :=
    hMAB

  have hAB : A = B -> False := by
    intro hABeq
    subst B
    apply hNonCol
    left

    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity
        (Geo := Geo) C A

    exact
      tarski_between_symmetry
        (Geo := Geo) C A A hCAA

  have hQBA : TarskiIsMidpoint Geo Q B A :=
    tarski_midpoint_symmetry
      Geo Q A B hQAB

  have hQA : Q = A -> False :=
    tarski_midpoint_ne_second
      Geo Q B A
      (fun hBA => hAB hBA.symm)
      hQBA

  have hQB : Q = B -> False :=
    tarski_midpoint_ne_second
      Geo Q A B
      hAB
      hQAB

  have hAQB : TarskiCollinear Geo A Q B := by
    left
    exact hQAB.1

  have hABQ : TarskiCollinear Geo A B Q :=
    tarski_collinear_symmetry
      Geo A Q B hAQB

  have hBQA : TarskiCollinear Geo B Q A :=
    (tarski_collinear_cycle Geo A B Q).mp hABQ

  have hAQC : TarskiCollinear Geo A Q C := by
    left
    exact hQ.1

  have hQCA : TarskiCollinear Geo Q C A :=
    (tarski_collinear_cycle Geo A Q C).mp hAQC

  have hQAC : TarskiCollinear Geo Q A C :=
    tarski_collinear_symmetry
      Geo Q C A hQCA

  have hBQC : TarskiCollinear Geo B Q C :=
    tarski_collinear_trans
      Geo B Q A C
      hQA
      hBQA
      hQAC

  have hBQ : B = Q -> False := by
    intro hBQ
    exact hQB hBQ.symm

  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans
      Geo A B Q C
      hBQ
      hABQ
      hBQC

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
    tarski_midsegment_parallelogram_cases
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  rcases hCases with hBad | hGood

  · exact False.elim
      (tarski_midsegment_first_parallelogram_impossible
        Geo A B C P Q X
        hNonCol hQ hQPX hBad)

  · exact hGood


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
    tarski_midsegment_second_parallelogram
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hAPB : Not (TarskiCollinear Geo A P B) :=
    tarski_midpoint_noncol_left
      Geo A B C P
      hNonCol hP

  exact
    tarski_parallelogram_opposite_parallel
      Geo A X P B
      hAPB
      hPar


theorem tarski_midsegment_parallel_strict
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A B Q P := by

  have hParABXP : TarskiParallelStrict Geo A B X P := by
    exact
      tarski_midsegment_parallel_AB_XP
        Geo A B C P Q X
        hNonCol hP hQ hQPX

  rcases hParABXP with ⟨hAB, hXP, hNoInt⟩

  have hPQX : TarskiCollinear Geo P Q X := by
    left
    exact hQPX.1

  have hQXP : TarskiCollinear Geo Q X P := by
    exact
      (tarski_collinear_cycle Geo P Q X).mp hPQX

  have hQPXcol : TarskiCollinear Geo Q P X := by
    exact
      tarski_collinear_symmetry
        Geo Q X P hQXP

  have hPX : P = X -> False := by
    intro hPX
    exact hXP hPX.symm

  have hPQ : P = Q -> False := by
    exact
      tarski_midpoint_ne_first
        Geo Q P X
        hPX
        hQPX

  have hQP : Q = P -> False := by
    intro hQP
    exact hPQ hQP.symm

  have hParABXP' : TarskiParallelStrict Geo A B X P := by
    exact ⟨hAB, hXP, hNoInt⟩

  exact
    tarski_parallel_strict_collinear_right
      Geo A B Q P X
      hParABXP'
      hQPXcol
      hQP

/-
Public Tarski Midsegment Theorem.

If P is the midpoint of BC and Q is the midpoint of AC
in a noncollinear triangle ABC, then AB is strictly parallel
to QP.

The auxiliary symmetric point X used in the proof is constructed
internally and does not appear in the theorem interface.
-/
theorem MidsegmentTheoremTarski
    [TarskiNeutral Geo]
    (A B C P Q : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C) :
    TarskiParallelStrict Geo A B Q P := by

  obtain ⟨X, hQPX⟩ :=
    tarski_symmetric_point_exists
      Geo P Q

  exact
    tarski_midsegment_parallel_strict
      Geo A B C P Q X
      hNonCol hP hQ hQPX

end Tarski

end Geometry

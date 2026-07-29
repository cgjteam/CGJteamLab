import CGJteamLab.MidSegmentParallelTarski

namespace Geometry
namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)



/-
Finlay configuration: C and G are distinct.

Since E is the midpoint of AC, noncollinearity of ABC implies
that B,E,C are noncollinear. Hence G cannot coincide with C
when B,E,G are collinear.
-/

theorem FinlayTarskiStep1a
    [TarskiNeutral Geo]
    (A B P F G : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo B P A))
    (hF : TarskiIsMidpoint Geo F B A)
    (hG : TarskiIsMidpoint Geo G A P) :
    TarskiParallelStrict Geo B P F G := by

  have hGPA : TarskiIsMidpoint Geo G P A :=
    tarski_midpoint_symmetry
      Geo G A P hG

  exact
    MidsegmentTheoremTarski
      Geo B P A G F
      hNonCol
      hGPA
      hF
/-
Finlay Step 1b.

From BP strictly parallel FG and the collinearity of C,F,G,
extend the second parallel line from FG to CG.
-/
theorem FinlayTarskiStep1b
    [TarskiNeutral Geo]
    (A B C P F G : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo B P A))
    (hF : TarskiIsMidpoint Geo F B A)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hCG : C = G -> False) :
    TarskiParallelStrict Geo B P C G := by

  have hBPFG : TarskiParallelStrict Geo B P F G :=
    FinlayTarskiStep1a
      Geo A B P F G
      hNonCol hF hG

  have hCGF : TarskiCollinear Geo C G F :=
    tarski_collinear_symmetry
      Geo C F G hCFG

  exact
    tarski_parallel_strict_collinear_right
      Geo B P C G F
      hBPFG
      hCGF
      hCG



theorem finlay_tarski_C_ne_G
    [TarskiNeutral Geo]
    (A B C E G : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hBEG : TarskiCollinear Geo B E G) :
    C = G -> False := by

  have hBAC : Not (TarskiCollinear Geo B A C) := by
    intro hBAC
    apply hNonCol

    have hBCA : TarskiCollinear Geo B C A :=
      tarski_collinear_symmetry
        Geo B A C hBAC

    have hCAB : TarskiCollinear Geo C A B :=
      (tarski_collinear_cycle Geo B C A).mp hBCA

    exact
      (tarski_collinear_cycle Geo C A B).mp hCAB

  have hBEC : Not (TarskiCollinear Geo B E C) :=
    tarski_noncollinear_midpoint_second
      Geo B A C E
      hBAC
      hE

  intro hCG
  subst G

  exact hBEC hBEG

theorem finlay_tarski_B_ne_G
    [TarskiNeutral Geo]
    (A B C F G : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hF : TarskiIsMidpoint Geo F A B)
    (hCFG : TarskiCollinear Geo C F G) :
    B = G -> False := by

  have hCAB : Not (TarskiCollinear Geo C A B) := by
    intro hCAB
    apply hNonCol

    exact
      (tarski_collinear_cycle Geo C A B).mp hCAB

  have hCFB : Not (TarskiCollinear Geo C F B) :=
    tarski_noncollinear_midpoint_second
      Geo C A B F
      hCAB
      hF

  intro hBG
  subst G

  exact hCFB hCFG

theorem finlay_tarski_A_ne_P
    [TarskiNeutral Geo]
    (A B C P F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G) :
    A ≠ P := by

  have hCAB : Not (TarskiCollinear Geo C A B) := by
    intro hCAB
    apply hNonColABC
    exact
      (tarski_collinear_cycle Geo C A B).mp hCAB

  have hCFA : Not (TarskiCollinear Geo C F A) :=
    tarski_midpoint_noncol_left
      Geo C A B F
      hCAB
      hF

  intro hAP
  subst P

  have hAG : A = G :=
    TarskiNeutral.between_identity
      (Geo := Geo)
      A G
      hG.1

  subst G
  exact hCFA hCFG

theorem finlay_tarski_noncollinear_BPA
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    Not (TarskiCollinear Geo B P A) := by

  have hAP : A ≠ P :=
    finlay_tarski_A_ne_P
      Geo A B C P F G
      hNonColABC
      hF
      hG
      hCFG

  have hBG : B = G -> False :=
    finlay_tarski_B_ne_G
      Geo A B C F G
      hNonColABC
      hF
      hCFG

  intro hBPA

  have hBAP : TarskiCollinear Geo B A P :=
    tarski_collinear_symmetry
      Geo B P A hBPA

  have hAGP : TarskiCollinear Geo A G P := by
    left
    exact hG.1

  have hAPG : TarskiCollinear Geo A P G :=
    tarski_collinear_symmetry
      Geo A G P hAGP

  have hBAG : TarskiCollinear Geo B A G :=
    tarski_collinear_trans
      Geo B A P G
      hAP
      hBAP
      hAPG

  have hBGA : TarskiCollinear Geo B G A :=
    tarski_collinear_symmetry
      Geo B A G hBAG

  have hGAB : TarskiCollinear Geo G A B :=
    (tarski_collinear_cycle Geo B G A).mp hBGA

  have hABG : TarskiCollinear Geo A B G :=
    (tarski_collinear_cycle Geo G A B).mp hGAB

  have hBGE : TarskiCollinear Geo B G E :=
    tarski_collinear_symmetry
      Geo B E G hBEG

  have hABE : TarskiCollinear Geo A B E :=
    tarski_collinear_trans
      Geo A B G E
      hBG
      hABG
      hBGE

  have hAEB : TarskiCollinear Geo A E B :=
    tarski_collinear_symmetry
      Geo A B E hABE

  have hEBA : TarskiCollinear Geo E B A :=
    (tarski_collinear_cycle Geo A E B).mp hAEB

  have hBAE : TarskiCollinear Geo B A E :=
    (tarski_collinear_cycle Geo E B A).mp hEBA

  have hBEA : TarskiCollinear Geo B E A :=
    tarski_collinear_symmetry
      Geo B A E hBAE

  have hBAC : Not (TarskiCollinear Geo B A C) := by
    intro hBAC
    apply hNonColABC

    have hBCA : TarskiCollinear Geo B C A :=
      tarski_collinear_symmetry
        Geo B A C hBAC

    have hCAB' : TarskiCollinear Geo C A B :=
      (tarski_collinear_cycle Geo B C A).mp hBCA

    exact
      (tarski_collinear_cycle Geo C A B).mp hCAB'

  have hBEA_not : Not (TarskiCollinear Geo B E A) :=
    tarski_midpoint_noncol_left
      Geo B A C E
      hBAC
      hE

  exact hBEA_not hBEA

theorem finlay_tarski_noncollinear_CPA
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    Not (TarskiCollinear Geo C P A) := by


  have hAP : A ≠ P :=
    finlay_tarski_A_ne_P
      Geo A B C P F G
      hNonColABC
      hF
      hG
      hCFG

  have hCG : C = G -> False :=
    finlay_tarski_C_ne_G
      Geo A B C E G
      hNonColABC
      hE
      hBEG

  intro hCPA

  have hCAP : TarskiCollinear Geo C A P :=
    tarski_collinear_symmetry
      Geo C P A hCPA

  have hAGP : TarskiCollinear Geo A G P := by
    left
    exact hG.1

  have hAPG : TarskiCollinear Geo A P G :=
    tarski_collinear_symmetry
      Geo A G P hAGP

  have hCAG : TarskiCollinear Geo C A G :=
    tarski_collinear_trans
      Geo C A P G
      hAP
      hCAP
      hAPG

  have hCGA : TarskiCollinear Geo C G A :=
    tarski_collinear_symmetry
      Geo C A G hCAG

  have hGAC : TarskiCollinear Geo G A C :=
    (tarski_collinear_cycle Geo C G A).mp hCGA

  have hACG : TarskiCollinear Geo A C G :=
    (tarski_collinear_cycle Geo G A C).mp hGAC

  have hCGF : TarskiCollinear Geo C G F :=
    tarski_collinear_symmetry
      Geo C F G hCFG

  have hACF : TarskiCollinear Geo A C F :=
    tarski_collinear_trans
      Geo A C G F
      hCG
      hACG
      hCGF

  have hCFA : TarskiCollinear Geo C F A :=
    (tarski_collinear_cycle Geo A C F).mp hACF

  have hCAB : Not (TarskiCollinear Geo C A B) := by
    intro hCAB
    apply hNonColABC
    exact
      (tarski_collinear_cycle Geo C A B).mp hCAB

  have hCFA_not : Not (TarskiCollinear Geo C F A) :=
    tarski_midpoint_noncol_left
      Geo C A B F
      hCAB
      hF

  exact hCFA_not hCFA

/-
Finlay Step 1.

Using the two midpoint configurations:
  F midpoint AB,
  E midpoint AC,
  G midpoint AP,

together with the median collinearities
  C,F,G and B,E,G,

we obtain:
  BP strictly parallel CG,
  CP strictly parallel BG.
-/
theorem FinlayTarskiStep1
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    TarskiParallelStrict Geo B P C G ∧
    TarskiParallelStrict Geo C P B G := by

  have hNonColBPA : Not (TarskiCollinear Geo B P A) :=
    finlay_tarski_noncollinear_BPA
      Geo A B C P E F G
      hNonColABC
      hE hF hG
      hCFG hBEG

  have hNonColCPA : Not (TarskiCollinear Geo C P A) :=
    finlay_tarski_noncollinear_CPA
      Geo A B C P E F G
      hNonColABC
      hE hF hG
      hCFG hBEG

  have hCG : C = G -> False :=
    finlay_tarski_C_ne_G
      Geo A B C E G
      hNonColABC
      hE
      hBEG

  have hBG : B = G -> False :=
    finlay_tarski_B_ne_G
      Geo A B C F G
      hNonColABC
      hF
      hCFG

  have hFBA : TarskiIsMidpoint Geo F B A :=
    tarski_midpoint_symmetry
      Geo F A B hF

  have hBPCG : TarskiParallelStrict Geo B P C G :=
    FinlayTarskiStep1b
      Geo A B C P F G
      hNonColBPA
      hFBA
      hG
      hCFG
      hCG

  have hGPA : TarskiIsMidpoint Geo G P A :=
    tarski_midpoint_symmetry
      Geo G A P hG

  have hECA : TarskiIsMidpoint Geo E C A :=
    tarski_midpoint_symmetry
      Geo E A C hE

  have hCPEG : TarskiParallelStrict Geo C P E G :=
    MidsegmentTheoremTarski
      Geo C P A G E
      hNonColCPA
      hGPA
      hECA

  have hBGE : TarskiCollinear Geo B G E :=
    tarski_collinear_symmetry
      Geo B E G hBEG

  have hCPBG : TarskiParallelStrict Geo C P B G :=
    tarski_parallel_strict_collinear_right
      Geo C P B G E
      hCPEG
      hBGE
      hBG

  exact ⟨hBPCG, hCPBG⟩

theorem FinlayTarskiStep2
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    TarskiParallelogram Geo B P C G := by

  have hStep1 :=
    FinlayTarskiStep1
      Geo A B C P E F G
      hNonColABC
      hE hF hG
      hCFG hBEG

  rcases hStep1 with ⟨hBPCG, hCPBG⟩

  have hPCBG : TarskiParallelStrict Geo P C B G :=
    tarski_parallel_strict_symm_left
      Geo C P B G hCPBG

  exact
    tarski_parallelogram_of_two_parallel_pairs
      Geo B P C G
      hBPCG
      hPCBG

/-
Finlay Step 3.

Since BPCG is a Tarski parallelogram, its diagonals BC and PG
have a common midpoint D.

Thus D is simultaneously:
  - the midpoint of BC,
  - the midpoint of PG.

In the Tarski formulation this combines the intersection and
diagonal-midpoint steps of the classical Finlay proof.
-/
theorem FinlayTarskiStep3
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    Exists fun D : Geo.Point =>
      TarskiIsMidpoint Geo D B C /\
      TarskiIsMidpoint Geo D P G := by

  have hPar :
      TarskiParallelogram Geo B P C G :=
    FinlayTarskiStep2
      Geo A B C P E F G
      hNonColABC
      hE hF hG
      hCFG hBEG

  rcases hPar with ⟨hNondeg, D, hDBC, hDPG⟩

  exact ⟨D, hDBC, hDPG⟩

/-
Finlay Step 4.

Let D be the common midpoint of the diagonals BC and PG
of the Tarski parallelogram BPCG.

Since G is the midpoint of AP, the points A,G,P are collinear.
Since D is the midpoint of PG, the points P,D,G are collinear.

Hence A,G,D are collinear, and since D is the midpoint of BC,
the line AG is the third median of triangle ABC.
-/
theorem FinlayTarskiStep4
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    Exists fun D : Geo.Point =>
      TarskiIsMidpoint Geo D B C /\
      TarskiCollinear Geo A G D := by

  obtain ⟨D, hDBC, hDPG⟩ :=
    FinlayTarskiStep3
      Geo A B C P E F G
      hNonColABC
      hE hF hG
      hCFG hBEG

  have hAGP : TarskiCollinear Geo A G P := by
    left
    exact hG.1

  have hPDG : TarskiCollinear Geo P D G := by
    left
    exact hDPG.1

  have hAP : A ≠ P :=
    finlay_tarski_A_ne_P
      Geo A B C P F G
      hNonColABC
      hF
      hG
      hCFG


  have hGP : G = P -> False :=
    tarski_midpoint_ne_second
      Geo G A P
      hAP
      hG

  have hDGP : TarskiCollinear Geo D G P :=
    (tarski_collinear_cycle Geo P D G).mp hPDG

  have hGPD : TarskiCollinear Geo G P D :=
    (tarski_collinear_cycle Geo D G P).mp hDGP

  have hAGD : TarskiCollinear Geo A G D :=
    tarski_collinear_trans
      Geo A G P D
      hGP
      hAGP
      hGPD

  exact ⟨D, hDBC, hAGD⟩

/-
Finlay's Theorem in Tarski geometry.

Let ABC be a noncollinear triangle. Let E and F be the midpoints
of AC and AB, respectively, and let G lie on the medians BE and CF.

Assume G is the midpoint of AP for the auxiliary point P used in
the midsegment construction.

Then there exists a midpoint D of BC such that A, G, and D are
collinear. Hence G lies on the third median of triangle ABC.
-/
theorem FinlayProofTarski
    [TarskiNeutral Geo]
    (A B C P E F G : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hCFG : TarskiCollinear Geo C F G)
    (hBEG : TarskiCollinear Geo B E G) :
    Exists fun D : Geo.Point =>
      TarskiIsMidpoint Geo D B C /\
      TarskiCollinear Geo A G D := by

  exact
    FinlayTarskiStep4
      Geo A B C P E F G
      hNonColABC
      hE hF hG
      hCFG hBEG

end Tarski

end Geometry

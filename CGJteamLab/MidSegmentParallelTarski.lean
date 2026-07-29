import CGJteamLab.TarskiInterface

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)



/-
Final bridge between the three-midpoint theory developed
in TarskiInterface and the public Midsegment theorem.

The auxiliary point X is eliminated by transferring
parallelism from XP to QP.
-/
theorem tarski_midsegment_parallel_strict
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A B Q P := by

  have hParABXP : TarskiParallelStrict Geo A B X P :=
    tarski_midsegment_parallel_AB_XP
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hPQX : TarskiCollinear Geo P Q X := by
    left
    exact hQPX.1

  have hQXP : TarskiCollinear Geo Q X P :=
    (tarski_collinear_cycle Geo P Q X).mp hPQX

  have hQPXcol : TarskiCollinear Geo Q P X :=
    tarski_collinear_symmetry Geo Q X P hQXP

  have hPX : P = X -> False := by
    intro hPX
    exact hParABXP.2.1 hPX.symm

  have hPQ : P = Q -> False :=
    tarski_midpoint_ne_first Geo Q P X hPX hQPX

  have hQP : Q = P -> False := by
    intro hQP
    exact hPQ hQP.symm

  exact
    tarski_parallel_strict_collinear_right
      Geo A B Q P X
      hParABXP
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

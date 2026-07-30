import CGJteamLab.TarskiInterface

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)

/-!
# Gupta midpoint construction

This module isolates Gupta's construction used in the proof that the
base of an isosceles triangle has a midpoint.

The file contains only the constructive configuration and the elementary
properties already derived from Tarski neutral geometry.
-/

/-!
## Construction layer
-/

/-- P is the reflection of C in A. -/
theorem gupta_P_reflection
    [TarskiNeutral Geo]
    (A C : Geo.Point) :
    ∃ P,
      Geo.Between C A P ∧
      Geo.Congruent A P A C := by
  obtain ⟨P, hCAP, hAPAC⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo)
      C A A C
  exact ⟨P, hCAP, hAPAC⟩

/-- Q is the reflection of C in B, with BQ copied from AP. -/
theorem gupta_Q_reflection
    [TarskiNeutral Geo]
    (A B C P : Geo.Point) :
    ∃ Q,
      Geo.Between C B Q ∧
      Geo.Congruent B Q A P := by
  obtain ⟨Q, hCBQ, hBQAP⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo)
      C B A P
  exact ⟨Q, hCBQ, hBQAP⟩

/-- Gupta's first Inner Pasch construction. -/
theorem gupta_R_construction
    [TarskiNeutral Geo]
    (A B C P Q : Geo.Point)
    (hCAP : Geo.Between C A P)
    (hCBQ : Geo.Between C B Q) :
    ∃ R,
      Geo.Between A R Q ∧
      Geo.Between B R P := by

  have hPAC : Geo.Between P A C :=
    tarski_between_symmetry
      (Geo := Geo)
      C A P
      hCAP

  have hQBC : Geo.Between Q B C :=
    tarski_between_symmetry
      (Geo := Geo)
      C B Q
      hCBQ

  obtain ⟨R, hARQ, hBRP⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      P Q C A B
      hPAC
      hQBC

  exact ⟨R, hARQ, hBRP⟩

/-- Gupta's second Inner Pasch construction. -/
theorem gupta_X_construction
    [TarskiNeutral Geo]
    (A B C P R : Geo.Point)
    (hBRP : Geo.Between B R P)
    (hCAP : Geo.Between C A P) :
    ∃ X,
      Geo.Between R X C ∧
      Geo.Between A X B := by

  obtain ⟨X, hRXC, hAXB⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      B C P R A
      hBRP
      hCAP

  exact ⟨X, hRXC, hAXB⟩

/--
The complete constructive Gupta configuration.

The isosceles hypothesis is retained in the statement because it belongs to
the final theorem, although the pure construction itself does not use it.
-/
theorem tarski_gupta_configuration
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (_hCAB : Geo.Congruent C A C B) :
    ∃ P Q R X : Geo.Point,
      Geo.Between C A P ∧
      Geo.Congruent A P A C ∧
      Geo.Between C B Q ∧
      Geo.Congruent B Q A P ∧
      Geo.Between A R Q ∧
      Geo.Between B R P ∧
      Geo.Between R X C ∧
      Geo.Between A X B := by

  obtain ⟨P, hCAP, hAPAC⟩ :=
    gupta_P_reflection
      (Geo := Geo)
      A C

  obtain ⟨Q, hCBQ, hBQAP⟩ :=
    gupta_Q_reflection
      (Geo := Geo)
      A B C P

  obtain ⟨R, hARQ, hBRP⟩ :=
    gupta_R_construction
      (Geo := Geo)
      A B C P Q
      hCAP
      hCBQ

  obtain ⟨X, hRXC, hAXB⟩ :=
    gupta_X_construction
      (Geo := Geo)
      A B C P R
      hBRP
      hCAP

  exact
    ⟨P, Q, R, X,
      hCAP,
      hAPAC,
      hCBQ,
      hBQAP,
      hARQ,
      hBRP,
      hRXC,
      hAXB⟩

/-!
## Basic properties
-/

/-- In the Gupta configuration, A is the midpoint of CP. -/
theorem gupta_P_midpoint
    [TarskiNeutral Geo]
    (A C P : Geo.Point)
    (hCAP : Geo.Between C A P)
    (hAPAC : Geo.Congruent A P A C) :
    TarskiIsMidpoint Geo A C P := by

  constructor

  · exact hCAP

  ·
    have hACAP : Geo.Congruent A C A P :=
      tarski_congruent_symmetry
        (Geo := Geo)
        A P A C
        hAPAC

    exact
      (Geometry.Tarski.Geo.congruent_reverse_first
        Geo A C A P).mp hACAP

/--
In the Gupta configuration, B is the midpoint of CQ,
provided CA is congruent to CB.
-/
theorem gupta_Q_midpoint
    [TarskiNeutral Geo]
    (A B C P Q : Geo.Point)
    (hCAB : Geo.Congruent C A C B)
    (hAPAC : Geo.Congruent A P A C)
    (hCBQ : Geo.Between C B Q)
    (hBQAP : Geo.Congruent B Q A P) :
    TarskiIsMidpoint Geo B C Q := by

  constructor

  · exact hCBQ

  ·
    have hAPBQ : Geo.Congruent A P B Q :=
      tarski_congruent_symmetry
        (Geo := Geo)
        B Q A P
        hBQAP

    have hBQAC : Geo.Congruent B Q A C :=
      TarskiNeutral.congruent_transitivity
        (Geo := Geo)
        A P B Q A C
        hAPBQ hAPAC

    have hACBQ : Geo.Congruent A C B Q :=
      tarski_congruent_symmetry
        (Geo := Geo)
        B Q A C
        hBQAC

    have hACBC : Geo.Congruent A C B C :=
      tarski_congruent_reverse_both
        (Geo := Geo)
        C A C B
        hCAB

    have hBQBC : Geo.Congruent B Q B C :=
      TarskiNeutral.congruent_transitivity
        (Geo := Geo)
        A C B Q B C
        hACBQ hACBC

    have hBCBQ : Geo.Congruent B C B Q :=
      tarski_congruent_symmetry
        (Geo := Geo)
        B Q B C
        hBQBC

    exact
      (Geometry.Tarski.Geo.congruent_reverse_first
        Geo B C B Q).mp hBCBQ

/-- The point R lies on both AQ and BP. -/
theorem gupta_R_incidence
    [TarskiNeutral Geo]
    (A B P Q R : Geo.Point)
    (hARQ : Geo.Between A R Q)
    (hBRP : Geo.Between B R P) :
    TarskiCollinear Geo A R Q ∧
    TarskiCollinear Geo B R P := by

  exact ⟨Or.inl hARQ, Or.inl hBRP⟩

/-- The point X lies on both RC and AB. -/
theorem gupta_X_incidence
    [TarskiNeutral Geo]
    (A B C R X : Geo.Point)
    (hRXC : Geo.Between R X C)
    (hAXB : Geo.Between A X B) :
    TarskiCollinear Geo R X C ∧
    TarskiCollinear Geo A X B := by

  exact ⟨Or.inl hRXC, Or.inl hAXB⟩

/-!
## First metric property
-/

/--
In the nondegenerate Gupta configuration, BP is congruent to AQ.

Five-Segment is applied to the two chains C-A-P and C-B-Q.
-/
theorem gupta_BP_congruent_AQ
    [TarskiNeutral Geo]
    (A B C P Q : Geo.Point)
    (hCA : C ≠ A)
    (hCAB : Geo.Congruent C A C B)
    (hCAP : Geo.Between C A P)
    (hCBQ : Geo.Between C B Q)
    (hBQAP : Geo.Congruent B Q A P) :
    Geo.Congruent B P A Q := by

  have hAPBQ : Geo.Congruent A P B Q :=
    tarski_congruent_symmetry
      (Geo := Geo)
      B Q A P
      hBQAP

  have hCBCA : Geo.Congruent C B C A :=
    tarski_congruent_symmetry
      (Geo := Geo)
      C A C B
      hCAB

  have hABBA : Geo.Congruent A B B A :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo)
      A B

  have hPBQA : Geo.Congruent P B Q A :=
    TarskiNeutral.five_segment
      (Geo := Geo)
      C C A B P Q B A
      hCA
      hCAP
      hCBQ
      hCAB
      hAPBQ
      hCBCA
      hABBA

  exact
    tarski_congruent_reverse_both
      (Geo := Geo)
      P B Q A
      hPBQA

/--
The auxiliary point R1 used in Gupta's proof lies on AQ
and cuts from A a segment congruent to BR.
-/
theorem gupta_R1_properties
    [TarskiNeutral Geo]
    (A B Q R R1 : Geo.Point)
    (hAR1Q : Geo.Between A R1 Q)
    (hAR1BR : Geo.Congruent A R1 B R) :
    Geo.Between A R1 Q ∧
    Geo.Congruent A R1 B R := by
  exact ⟨hAR1Q, hAR1BR⟩

theorem gupta_RA_congruent_R1B
    [TarskiNeutral Geo]
    (A B P Q R R1 : Geo.Point)
    (hBR : B ≠ R)
    (hBRP : Geo.Between B R P)
    (hAR1Q : Geo.Between A R1 Q)
    (hBPAQ : Geo.Congruent B P A Q)
    (hRPR1Q : Geo.Congruent R P R1 Q)
    (hBAAB : Geo.Congruent B A A B)
    (hPAQB : Geo.Congruent P A Q B) :
    Geo.Congruent R A R1 B := by

  exact
    tarski_inner_five_segment
      (Geo := Geo)
      B A R R1 P Q A B
      hBR
      hBRP
      hAR1Q
      hBPAQ
      hRPR1Q
      hBAAB
      hPAQB

/--
The auxiliary point R1 is collinear with B and P.
-/
theorem gupta_R1_collinear_BRP
    [TarskiPlane Geo]
    (A B P Q R R1 : Geo.Point)
    (hARQ : Geo.Between A R Q)
    (hRAR1B : Geo.Congruent R A R1 B)
    (hAQBP : Geo.Congruent A Q B P)
    (hRQR1P : Geo.Congruent R Q R1 P) :
    TarskiCollinear Geo B R1 P := by

  have hColARQ : TarskiCollinear Geo A R Q := by
    exact Or.inl hARQ

  have hARBR1 : Geo.Congruent A R B R1 := by
    exact
      tarski_congruent_reverse_both
        (Geo := Geo)
        R A R1 B
        hRAR1B

  exact
    tarski_collinear_congruence_transfer
      (Geo := Geo)
      A R Q
      B R1 P
      hColARQ
      hARBR1
      hAQBP
      hRQR1P

/--
The auxiliary point R1 coincides with R.

This is the direct translation of clause 104 as used at line 2956
of the OTTER proof of SST Satz 7.25.
-/
theorem gupta_R1_eq_R
    [TarskiPlane Geo]
    (A B P Q R R1 : Geo.Point)
    (hAQ : A ≠ Q)
    (hPB : P ≠ B)
    (hARQ : Geo.Between A R Q)
    (hBRP : Geo.Between B R P)
    (hAR1Q : Geo.Between A R1 Q)
    (hBR1P : TarskiCollinear Geo B R1 P)
    (hNotPBQ : ¬ TarskiCollinear Geo P B Q) :
    R1 = R := by

  apply Classical.byContradiction
  intro hR1R

  have hRR1 : R ≠ R1 := by
    intro h
    exact hR1R h.symm

  have hAQR : TarskiCollinear Geo A Q R := by
    exact
      tarski_collinear_symmetry
        (Geo := Geo)
        A R Q
        (Or.inl hARQ)

  have hPBR : TarskiCollinear Geo P B R := by
    have hBRPcol : TarskiCollinear Geo B R P :=
      Or.inl hBRP

    have hRPB : TarskiCollinear Geo R P B :=
      tarski_collinear_rotate
        (Geo := Geo)
        B R P
        hBRPcol

    exact
      tarski_collinear_rotate
        (Geo := Geo)
        R P B
        hRPB

  have hAQR1 : TarskiCollinear Geo A Q R1 := by
    exact
      tarski_collinear_symmetry
        (Geo := Geo)
        A R1 Q
        (Or.inl hAR1Q)

  have hPBR1 : TarskiCollinear Geo P B R1 := by
    have hR1PB : TarskiCollinear Geo R1 P B :=
      tarski_collinear_rotate
        (Geo := Geo)
        B R1 P
        hBR1P

    exact
      tarski_collinear_rotate
        (Geo := Geo)
        R1 P B
        hR1PB

  have hAQQ : TarskiCollinear Geo A Q Q := by
    exact
      Or.inl
        (tarski_between_reflexivity
          (Geo := Geo)
          A Q)

  have hPBQ : TarskiCollinear Geo P B Q :=
    tarski_collinear_two_common_points
      (Geo := Geo)
      A Q
      P B
      R R1 Q
      hAQ
      hPB
      hAQR
      hPBR
      hAQR1
      hPBR1
      hRR1
      hAQQ

  exact hNotPBQ hPBQ

/--
After identifying the auxiliary point R1 with R,
the congruence RA ≅ R1B becomes RA ≅ RB.
-/
theorem gupta_RA_congruent_RB
    [TarskiPlane Geo]
    (A B R R1 : Geo.Point)
    (hRAR1B : Geo.Congruent R A R1 B)
    (hR1R : R1 = R) :
    Geo.Congruent R A R B := by
  simpa [hR1R] using hRAR1B





end Tarski

end Geometry

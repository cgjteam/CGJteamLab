import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.HilbertInterfaceXI
import CGJteamLab.Proposition12
import CGJteamLab.Proposition32
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.Proposition16
import CGJteamLab.Proposition19
import CGJteamLab.Proposition2_13
import CGJteamLab.Proposition17

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Hilbert/Forder Book IV circle propositions

Consolidated proof module for the circle theorems used by the
crossing-rays and proportion developments.
-/

/- BEGIN folded proof support: Crossing_circle_stage1_v2.lean -/
/-!
# Crossing-rays circle kernel -- stage 1

This file extracts the clean geometric preparation hidden inside the old
Pascal workshop, but DOES NOT import `HilbertPascal` and DOES NOT use either
of its temporary circle axioms.

The nondegenerate crossing configuration is reduced to:

* exact order of the two secants,
* the corresponding angle/supplement classification,
* a genuine Hilbert circle through A, C, D.

The remaining circle theorem is therefore sharply localized: prove that B is
on this circle from the angle classification, and then prove the same-chord
inscribed-angle conclusion.

No new axiom is declared here.
-/

theorem hilbert_crossing_first_secant_noncollinear_stage1
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    Not (PrimCollinear Geo A C B) := by

  intro hACB

  have hOAC :
      PrimCollinear Geo O A C :=
    hRayAC.2.2.1

  have hOAB :
      PrimCollinear Geo O A B :=
    hilbert_primCollinear_trans
      Geo
      O A C B
      hAC
      hOAC
      hACB

  have hABO :
      PrimCollinear Geo A B O :=
    PrimCollinearCycle
      Geo O A B hOAB

  have hAOB' :
      PrimCollinear Geo A O B :=
    PrimCollinearRotate
      Geo A B O hABO

  exact hAOB hAOB'

theorem hilbert_crossing_second_secant_noncollinear_stage1
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayBD : HilbertSameRay Geo O B D)
    (hBD : B ≠ D) :
    Not (PrimCollinear Geo A D B) := by

  intro hADB

  have hOBD :
      PrimCollinear Geo O B D :=
    hRayBD.2.2.1

  have hBDO :
      PrimCollinear Geo B D O :=
    PrimCollinearCycle
      Geo O B D hOBD

  have hABD :
      PrimCollinear Geo A B D :=
    PrimCollinearRotate
      Geo A D B hADB

  have hABO :
      PrimCollinear Geo A B O :=
    hilbert_primCollinear_trans
      Geo
      A B D O
      hBD
      hABD
      hBDO

  have hAOB' :
      PrimCollinear Geo A O B :=
    PrimCollinearRotate
      Geo A B O hABO

  exact hAOB hAOB'

theorem hilbert_crossing_nondegenerate_data_stage1
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D) :
    Not (PrimCollinear Geo O A D) ∧
    Not (PrimCollinear Geo O B C) ∧
    (Geo.Between O A C ∨ Geo.Between O C A) ∧
    (Geo.Between O B D ∨ Geo.Between O D B) := by

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAC.1

  have hRayBB :
      HilbertSameRay Geo O B B :=
    hilbert_sameRay_refl
      Geo O B hRayBD.1

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  have hOAD :
      Not (PrimCollinear Geo O A D) := by
    intro h
    exact
      hAOD
        (PrimCollinearSwap
          Geo O A D h)

  have hCOB :
      Not (PrimCollinear Geo C O B) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C B
      hAOB
      hRayAC
      hRayBB

  have hOBC :
      Not (PrimCollinear Geo O B C) := by
    intro h
    exact
      hCOB
        (PrimCollinearRotate
          Geo
          C B O
          (PrimCollinearSymm
            Geo O B C h))

  have hOrderAC :
      Geo.Between O A C ∨
      Geo.Between O C A := by

    rcases
        hilbert_sameRay_cases
          Geo O A C hRayAC
      with hEq | hOAC | hOCA

    · exact False.elim (hAC hEq)

    · exact Or.inl hOAC

    · exact Or.inr hOCA

  have hOrderBD :
      Geo.Between O B D ∨
      Geo.Between O D B := by

    rcases
        hilbert_sameRay_cases
          Geo O B D hRayBD
      with hEq | hOBD | hODB

    · exact False.elim (hBD hEq)

    · exact Or.inl hOBD

    · exact Or.inr hODB

  exact
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

theorem hilbert_crossing_angle_at_O_stage1
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D) :
    Geo.AngleCongruent
      A O D
      B O C := by

  have hAOB_AOD :
      Geo.Angle A O B =
      Geo.Angle A O D :=
    hilbert_angle_eq_of_sameRay_second
      Geo O A B D hRayBD

  have hBOA_BOC :
      Geo.Angle B O A =
      Geo.Angle B O C :=
    hilbert_angle_eq_of_sameRay_second
      Geo O B A C hRayAC

  have hAOB_BOA :
      Geo.AngleCongruent
        A O B
        B O A :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      A O B).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo A O B)

  unfold Geometry.Geo.AngleCongruent at hAOB_BOA ⊢

  rw [← hAOB_AOD, ← hBOA_BOC]

  exact hAOB_BOA

theorem hilbert_crossing_outer_outer_angles_stage1
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hOBC : Not (PrimCollinear Geo O B C))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
      C A D
      C B D := by

  --------------------------------------------------------------------
  -- A != D.
  --------------------------------------------------------------------

  have hADO :
      Not (PrimCollinear Geo A D O) := by

    intro h

    have hDOA :
        PrimCollinear Geo D O A :=
      PrimCollinearCycle
        Geo A D O h

    have hOAD' :
        PrimCollinear Geo O A D :=
      PrimCollinearCycle
        Geo D O A hDOA

    exact hOAD hOAD'

  have hAD :
      A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D O hADO

  --------------------------------------------------------------------
  -- B != C.
  --------------------------------------------------------------------

  have hBCO :
      Not (PrimCollinear Geo B C O) := by

    intro h

    have hCOB :
        PrimCollinear Geo C O B :=
      PrimCollinearCycle
        Geo B C O h

    have hOBC' :
        PrimCollinear Geo O B C :=
      PrimCollinearCycle
        Geo C O B hCOB

    exact hOBC hOBC'

  have hBC :
      B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C O hBCO

  --------------------------------------------------------------------
  -- Since O-A-C, angle DAC is supplementary to OAD.
  --------------------------------------------------------------------

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSuppA :
      BookZeroSupplement Geo
        O A D
        D C :=
    ⟨hRayADD, hOAC⟩

  --------------------------------------------------------------------
  -- Since O-B-D, angle CBD is supplementary to OBC.
  --------------------------------------------------------------------

  have hRayBCC :
      HilbertSameRay Geo B C C :=
    hilbert_sameRay_refl
      Geo B C hBC.symm

  have hSuppB :
      BookZeroSupplement Geo
        O B C
        C D :=
    ⟨hRayBCC, hOBD⟩

  --------------------------------------------------------------------
  -- Supplements of congruent angles are congruent.
  --------------------------------------------------------------------

  have hDAC_CBD :
      Geo.AngleCongruent
        D A C
        C B D :=
    bookZero_43_supplements
      Geo
      O A D
      D C
      O B C
      C D
      hAngle
      hSuppA
      hSuppB
      hOAD
      hOBC

  --------------------------------------------------------------------
  -- Reverse the first angle: DAC = CAD.
  --------------------------------------------------------------------

  exact
    (Geo.angle_congruent_reverse_first
      D A C
      C B D).mp
      hDAC_CBD

theorem hilbert_crossing_inner_inner_angles_stage1
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
      C A D
      C B D := by

  have hACO :
      Geo.Between A C O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.2.2

  have hBDO :
      Geo.Between B D O :=
    (HilbertOrder.between_incidence
      O D B hODB).2.2.2.2

  have hRayACO :
      HilbertSameRay Geo A C O :=
    hilbert_sameRay_of_between
      Geo A C O hACO

  have hRayAOC :
      HilbertSameRay Geo A O C :=
    hilbert_sameRay_symm
      Geo A C O hRayACO

  have hRayBDO :
      HilbertSameRay Geo B D O :=
    hilbert_sameRay_of_between
      Geo B D O hBDO

  have hRayBOD :
      HilbertSameRay Geo B O D :=
    hilbert_sameRay_symm
      Geo B D O hRayBDO

  have hLeft :
      Geo.Angle O A D =
      Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A O C D hRayAOC

  have hRight :
      Geo.Angle O B C =
      Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B O D C hRayBOD

  have hCAD_DBC :
      Geo.AngleCongruent
        C A D
        D B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hLeft, ← hRight]

    exact hAngle

  exact
    (Geo.angle_congruent_reverse_second
      C A D
      D B C).mp
      hCAD_DBC

theorem hilbert_crossing_mixed_outer_inner_angle_data_stage1
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    BookZeroSupplement Geo
        O A D
        D C
    ∧
    Geo.AngleCongruent
        O A D
        C B D := by

  have hADO :
      Not (PrimCollinear Geo A D O) := by
    intro h
    exact
      hOAD
        (PrimCollinearRotate
          Geo
          O D A
          (PrimCollinearSymm
            Geo A D O h))

  have hAD :
      A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D O hADO

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSuppA :
      BookZeroSupplement Geo
        O A D
        D C :=
    ⟨hRayADD, hOAC⟩

  have hBDO :
      Geo.Between B D O :=
    (HilbertOrder.between_incidence
      O D B hODB).2.2.2.2

  have hRayBDO :
      HilbertSameRay Geo B D O :=
    hilbert_sameRay_of_between
      Geo B D O hBDO

  have hRayBOD :
      HilbertSameRay Geo B O D :=
    hilbert_sameRay_symm
      Geo B D O hRayBDO

  have hRight :
      Geo.Angle O B C =
      Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B O D C hRayBOD

  have hOAD_DBC :
      Geo.AngleCongruent
        O A D
        D B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hRight]

    exact hAngle

  have hOAD_CBD :
      Geo.AngleCongruent
        O A D
        C B D :=
    (Geo.angle_congruent_reverse_second
      O A D
      D B C).mp
      hOAD_DBC

  exact
    ⟨hSuppA, hOAD_CBD⟩

theorem hilbert_crossing_mixed_inner_outer_angle_data_stage1
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOBC : Not (PrimCollinear Geo O B C))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
        C A D
        O B C
    ∧
    BookZeroSupplement Geo
        O B C
        C D := by

  --------------------------------------------------------------------
  -- Transport OAD to CAD, since O-C-A.
  --------------------------------------------------------------------

  have hACO :
      Geo.Between A C O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.2.2

  have hRayACO :
      HilbertSameRay Geo A C O :=
    hilbert_sameRay_of_between
      Geo A C O hACO

  have hRayAOC :
      HilbertSameRay Geo A O C :=
    hilbert_sameRay_symm
      Geo A C O hRayACO

  have hLeft :
      Geo.Angle O A D =
      Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A O C D hRayAOC

  have hCAD_OBC :
      Geo.AngleCongruent
        C A D
        O B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hLeft]

    exact hAngle

  --------------------------------------------------------------------
  -- Since O-B-D, CBD is supplementary to OBC.
  --------------------------------------------------------------------

  have hBCO :
      Not (PrimCollinear Geo B C O) := by
    intro h

    have hCOB :
        PrimCollinear Geo C O B :=
      PrimCollinearCycle
        Geo B C O h

    have hOBC' :
        PrimCollinear Geo O B C :=
      PrimCollinearCycle
        Geo C O B hCOB

    exact hOBC hOBC'

  have hBC :
      B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C O hBCO

  have hRayBCC :
      HilbertSameRay Geo B C C :=
    hilbert_sameRay_refl
      Geo B C hBC.symm

  have hSuppB :
      BookZeroSupplement Geo
        O B C
        C D :=
    ⟨hRayBCC, hOBD⟩

  exact
    ⟨hCAD_OBC, hSuppB⟩

theorem hilbert_crossing_nondegenerate_angle_classification_stage1
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    (
      Geo.AngleCongruent
        C A D
        C B D
    )
    ∨
    (
      BookZeroSupplement Geo
        O A D
        D C
      ∧
      Geo.AngleCongruent
        O A D
        C B D
    )
    ∨
    (
      Geo.AngleCongruent
        C A D
        O B C
      ∧
      BookZeroSupplement Geo
        O B C
        C D
    ) := by

  rcases
      hilbert_crossing_nondegenerate_data_stage1
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- O-A-C
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-A-C and O-B-D
    --------------------------------------------------------------

    · left

      exact
        hilbert_crossing_outer_outer_angles_stage1
          Geo
          O A C B D
          hOAD
          hOBC
          hOAC
          hOBD
          hAngle

    --------------------------------------------------------------
    -- O-A-C and O-D-B
    --------------------------------------------------------------

    · right
      left

      exact
        hilbert_crossing_mixed_outer_inner_angle_data_stage1
          Geo
          O A C B D
          hOAD
          hOAC
          hODB
          hAngle

  --------------------------------------------------------------------
  -- O-C-A
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-C-A and O-B-D
    --------------------------------------------------------------

    · right
      right

      exact
        hilbert_crossing_mixed_inner_outer_angle_data_stage1
          Geo
          O A C B D
          hOBC
          hOCA
          hOBD
          hAngle

    --------------------------------------------------------------
    -- O-C-A and O-D-B
    --------------------------------------------------------------

    · left

      exact
        hilbert_crossing_inner_inner_angles_stage1
          Geo
          O A C B D
          hOCA
          hODB
          hAngle


------------------------------------------------------------------------
-- Circumcircle of the three already controlled points A,C,D.
------------------------------------------------------------------------

/--
In the nondegenerate crossing configuration, A,C,D determine a genuine
Hilbert circle.  This uses the production circumcenter theorem from
`HilbertInterfaceXI`, not the experimental Pascal file.
-/
theorem hilbert_crossing_acd_circumcircle_stage1
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D := by

  have hOAC :
      PrimCollinear Geo O A C :=
    hRayAC.2.2.1

  have hACD :
      Not (PrimCollinear Geo A C D) := by
    intro hACD
    have hOAD' :
        PrimCollinear Geo O A D :=
      hilbert_primCollinear_trans
        Geo
        O A C D
        hAC
        hOAC
        hACD
    exact hOAD hOAD'

  rcases
      hilbert_triangle_circumcenter_exists_XI
        Geo
        A C D
        hACD
    with
    ⟨K, hKA_KC, hKA_KD⟩

  refine
    ⟨K, ?_, ?_, ?_⟩

  · unfold HilbertCircle
    exact
      hilbert_congruent_reflexive
        Geo K A

  · unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K A K C
        hKA_KC

  · unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K A K D
        hKA_KD


------------------------------------------------------------------------
-- Combined nondegenerate certificate.
------------------------------------------------------------------------

/--
All non-circle-theorem data needed for the nondegenerate crossing case.

The theorem constructs a circle through A,C,D and simultaneously records
the exact angle/supplement alternative forced by the two secant orders.
No assertion that B lies on the circle is assumed or hidden here.
-/
theorem hilbert_crossing_nondegenerate_certificate_stage1
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D ∧
      (
        Geo.AngleCongruent
          C A D
          C B D
        ∨
        (
          BookZeroSupplement Geo
            O A D
            D C
          ∧
          Geo.AngleCongruent
            O A D
            C B D
        )
        ∨
        (
          Geo.AngleCongruent
            C A D
            O B C
          ∧
          BookZeroSupplement Geo
            O B C
            C D
        )
      ) := by

  rcases
      hilbert_crossing_nondegenerate_data_stage1
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD, _hOBC, _hOrderAC, _hOrderBD⟩

  rcases
      hilbert_crossing_acd_circumcircle_stage1
        Geo
        O A C D
        hOAD
        hRayAC
        hAC
    with
    ⟨K, hA, hC, hD⟩

  have hClass :=
    hilbert_crossing_nondegenerate_angle_classification_stage1
      Geo
      O A C B D
      hAOB
      hRayAC
      hRayBD
      hAC
      hBD
      hAngle

  exact
    ⟨K,
      hA,
      hC,
      hD,
      hClass⟩
/- END folded proof support: Crossing_circle_stage1_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage2_v1.lean -/
/-!
# Crossing-rays circle kernel -- stage 2

Stage 1 isolated the four order/angle configurations and constructed the
circumcircle through A,C,D.

This stage adds the exact side-of-chord information for the same four
order configurations.  It also closes the degenerate cases A=C or B=D
without any circle-converse theorem.

The only genuinely open nondegenerate circle step after this file is:

* same side of chord CD + equal subtended angles  -> concyclic;
* opposite sides of chord CD + supplementary subtended angles -> concyclic.

Those are precisely the source-faithful circle converses corresponding
to Forder IV.19 and IV.20.

No new axiom is declared here.
-/

------------------------------------------------------------------------
-- 1. Degenerate crossing cases are already completely cyclic.
------------------------------------------------------------------------

theorem hilbert_crossing_concyclic_degenerate_stage2
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hDeg : A = C ∨ B = D) :
    HilbertConcyclic4 Geo A C D B := by

  rcases hDeg with hACeq | hBDeq

  --------------------------------------------------------------------
  -- A = C.
  --------------------------------------------------------------------

  · subst C

    by_cases hBD : B = D

    --------------------------------------------------------------
    -- A = C and B = D.
    --------------------------------------------------------------

    · subst D

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A O B
            hAOB
        with
        ⟨K, _hKA_KO, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact
          hilbert_congruent_reflexive
            Geo K A

      · exact hKA_KB

      · exact hKA_KB

    --------------------------------------------------------------
    -- A = C, B != D.
    --------------------------------------------------------------

    · have hADB :
          Not (PrimCollinear Geo A D B) :=
        hilbert_crossing_second_secant_noncollinear_stage1
          Geo
          O A B D
          hAOB
          hRayBD
          hBD

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A D B
            hADB
        with
        ⟨K, hKA_KD, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact
          hilbert_congruent_reflexive
            Geo K A

      · exact hKA_KD

      · exact hKA_KB

  --------------------------------------------------------------------
  -- B = D.
  --------------------------------------------------------------------

  · subst D

    by_cases hAC : A = C

    --------------------------------------------------------------
    -- Again A = C and B = D.
    --------------------------------------------------------------

    · subst C

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A O B
            hAOB
        with
        ⟨K, _hKA_KO, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact
          hilbert_congruent_reflexive
            Geo K A

      · exact hKA_KB

      · exact hKA_KB

    --------------------------------------------------------------
    -- B = D, A != C.
    --------------------------------------------------------------

    · have hACB :
          Not (PrimCollinear Geo A C B) :=
        hilbert_crossing_first_secant_noncollinear_stage1
          Geo
          O A C B
          hAOB
          hRayAC
          hAC

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A C B
            hACB
        with
        ⟨K, hKA_KC, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact hKA_KC

      · exact hKA_KB

      · exact hKA_KB


------------------------------------------------------------------------
-- 2. Outer/outer: A and B are on the same side of chord CD.
------------------------------------------------------------------------

theorem hilbert_crossing_outer_outer_sameSide_chord_stage2
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertSameSide Geo A B chord := by

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_of_between
      Geo O A C hOAC

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_of_between
      Geo O B D hOBD

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hOCD :
      Not (PrimCollinear Geo O C D) := by
    intro h
    apply hCOD
    exact
      PrimCollinearRotate
        Geo C D O
        (PrimCollinearCycle
          Geo O C D h)

  have hODC :
      Not (PrimCollinear Geo O D C) := by
    intro h
    exact
      hOCD
        (PrimCollinearRotate
          Geo O D C h)

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    apply hOCD
    exact
      PrimCollinearCycle
        Geo D O C
        (PrimCollinearCycle
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O A D C
        hOAC
        hOCD
    with
    ⟨chord1, hDchord1, hCchord1, hOA⟩

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O B C D
        hOBD
        hODC
    with
    ⟨chord2, hCchord2, hDchord2, hOB⟩

  have hChordEq :
      chord1 = chord2 :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      chord1 chord2
      hCchord1
      hDchord1
      hCchord2
      hDchord2

  rw [← hChordEq] at hOB

  have hAO :
      HilbertSameSide Geo A O chord1 :=
    hilbert_sameSide_symm
      Geo O A chord1 hOA

  have hAB :
      HilbertSameSide Geo A B chord1 :=
    hilbert_sameSide_trans
      Geo A O B chord1
      hAO
      hOB

  exact
    ⟨chord1,
      hCchord1,
      hDchord1,
      hAB⟩


------------------------------------------------------------------------
-- 3. Inner/inner: A and B are on the same side of chord CD.
------------------------------------------------------------------------

theorem hilbert_crossing_inner_inner_sameSide_chord_stage2
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertSameSide Geo A B chord := by

  have hRayCA :
      HilbertSameRay Geo O C A :=
    hilbert_sameRay_of_between
      Geo O C A hOCA

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_symm
      Geo O C A hRayCA

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨chord, hCchord, hDchord⟩

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hSame :
      HilbertSameSide Geo A B chord :=
    hilbert_third_side_endpoints_sameSide
      Geo
      O A B
      C D
      chord
      hOAB
      hOCA
      hODB
      hCchord
      hDchord

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hSame⟩


------------------------------------------------------------------------
-- 4. Mixed outer/inner: A and B are on opposite sides of chord CD.
------------------------------------------------------------------------

theorem hilbert_crossing_mixed_outer_inner_oppositeSide_chord_stage2
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertOppositeSide Geo A B chord := by

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_of_between
      Geo O A C hOAC

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hOCD :
      Not (PrimCollinear Geo O C D) := by
    intro h
    exact
      hCOD
        (PrimCollinearSwap
          Geo O C D h)

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨chord, hCchord, hDchord⟩

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O A D C
        hOAC
        hOCD
    with
    ⟨chord1, hDchord1, hCchord1, hOA1⟩

  have hChordEq :
      chord1 = chord :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      chord1 chord
      hCchord1
      hDchord1
      hCchord
      hDchord

  have hOA :
      HilbertSameSide Geo O A chord := by
    rw [← hChordEq]
    exact hOA1

  have hOppOB :
      HilbertOppositeSide Geo O B chord :=
    ⟨hOA.1,
      by
        intro hBchord

        have hODBData :=
          HilbertOrder.between_incidence
            O D B hODB

        have hDB :
            D ≠ B :=
          hODBData.2.1

        have hODBcol :
            PrimCollinear Geo O D B :=
          hODBData.2.2.2.1

        have hDBO :
            PrimCollinear Geo D B O :=
          PrimCollinearCycle
            Geo O D B hODBcol

        have hOchord :
            H.OnLine O chord :=
          hilbert_collinear_on_line
            Geo
            D B O
            chord
            hDB
            hDchord
            hBchord
            hDBO

        exact hOA.1 hOchord,
      ⟨D, hODB, hDchord⟩⟩

  have hOppBO :
      HilbertOppositeSide Geo B O chord :=
    hilbert_oppositeSide_symm
      Geo O B chord hOppOB

  have hOppBA :
      HilbertOppositeSide Geo B A chord :=
    hilbert_oppositeSide_transport_right
      Geo
      B O A
      chord
      hOppBO
      hOA

  have hOppAB :
      HilbertOppositeSide Geo A B chord :=
    hilbert_oppositeSide_symm
      Geo B A chord hOppBA

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hOppAB⟩


------------------------------------------------------------------------
-- 5. Mixed inner/outer by symmetry.
------------------------------------------------------------------------

theorem hilbert_crossing_mixed_inner_outer_oppositeSide_chord_stage2
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertOppositeSide Geo A B chord := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  rcases
      hilbert_crossing_mixed_outer_inner_oppositeSide_chord_stage2
        Geo
        O B D A C
        hBOA
        hOBD
        hOCA
    with
    ⟨chord,
      hDchord,
      hCchord,
      hOppBA⟩

  have hOppAB :
      HilbertOppositeSide Geo A B chord :=
    hilbert_oppositeSide_symm
      Geo B A chord hOppBA

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hOppAB⟩


------------------------------------------------------------------------
-- 6. Exact nondegenerate chord classification.
------------------------------------------------------------------------

/--
For a nondegenerate crossing-rays configuration, the unique chord CD
falls into exactly the form needed by the two classical circle converses.

Same-side branches already carry equal subtended angles.

Opposite-side branches carry the exact Book Zero supplement witness and
the congruent companion angle from Stage 1.
-/
theorem hilbert_crossing_nondegenerate_chord_classification_stage2
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      (
        (
          HilbertSameSide Geo A B chord ∧
          Geo.AngleCongruent
            C A D
            C B D
        )
        ∨
        (
          HilbertOppositeSide Geo A B chord ∧
          BookZeroSupplement Geo
            O A D
            D C ∧
          Geo.AngleCongruent
            O A D
            C B D
        )
        ∨
        (
          HilbertOppositeSide Geo A B chord ∧
          Geo.AngleCongruent
            C A D
            O B C ∧
          BookZeroSupplement Geo
            O B C
            C D
        )
      ) := by

  rcases
      hilbert_crossing_nondegenerate_data_stage1
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- O-A-C.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-A-C and O-B-D: same side + equal angles.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_outer_outer_sameSide_chord_stage2
            Geo
            O A C B D
            hAOB
            hOAC
            hOBD
      with
      ⟨chord, hCchord, hDchord, hSame⟩

      have hEq :
          Geo.AngleCongruent
            C A D
            C B D :=
        hilbert_crossing_outer_outer_angles_stage1
          Geo
          O A C B D
          hOAD
          hOBC
          hOAC
          hOBD
          hAngle

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inl ⟨hSame, hEq⟩⟩

    --------------------------------------------------------------
    -- O-A-C and O-D-B: opposite side + supplement at A.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_outer_inner_oppositeSide_chord_stage2
            Geo
            O A C B D
            hAOB
            hOAC
            hODB
      with
      ⟨chord, hCchord, hDchord, hOpp⟩

      rcases
          hilbert_crossing_mixed_outer_inner_angle_data_stage1
            Geo
            O A C B D
            hOAD
            hOAC
            hODB
            hAngle
      with
      ⟨hSuppA, hCongA⟩

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inr
            (Or.inl
              ⟨hOpp,
                hSuppA,
                hCongA⟩)⟩

  --------------------------------------------------------------------
  -- O-C-A.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-C-A and O-B-D: opposite side + supplement at B.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_inner_outer_oppositeSide_chord_stage2
            Geo
            O A C B D
            hAOB
            hOCA
            hOBD
      with
      ⟨chord, hCchord, hDchord, hOpp⟩

      rcases
          hilbert_crossing_mixed_inner_outer_angle_data_stage1
            Geo
            O A C B D
            hOBC
            hOCA
            hOBD
            hAngle
      with
      ⟨hCongB, hSuppB⟩

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inr
            (Or.inr
              ⟨hOpp,
                hCongB,
                hSuppB⟩)⟩

    --------------------------------------------------------------
    -- O-C-A and O-D-B: same side + equal angles.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_inner_inner_sameSide_chord_stage2
            Geo
            O A C B D
            hAOB
            hOCA
            hODB
      with
      ⟨chord, hCchord, hDchord, hSame⟩

      have hEq :
          Geo.AngleCongruent
            C A D
            C B D :=
        hilbert_crossing_inner_inner_angles_stage1
          Geo
          O A C B D
          hOCA
          hODB
          hAngle

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inl ⟨hSame, hEq⟩⟩
/- END folded proof support: Crossing_circle_stage2_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage3_v3.lean -/
/-!
# Crossing-rays circle kernel -- stage 3

Stage 2 reduced the nondegenerate crossing configuration to the exact
same-side / opposite-side alternatives for the chord CD.

This file now isolates the two classical circle converses used by
Forder:

* IV.19:
    same side of CD + equal angles subtending CD -> concyclic;

* IV.20:
    opposite sides of CD + supplementary subtended angles -> concyclic.

They are represented here as explicit `Prop` interfaces, not axioms.
From them we prove the complete crossing-chords concyclicity theorem,
including the degenerate cases already discharged in Stage 2.

Thus the old ad hoc crossing-chords concyclicity assumption is reduced
to two source-faithful circle theorems.
-/

------------------------------------------------------------------------
-- 3. Crossing configuration -> concyclicity from IV.19 + IV.20.
------------------------------------------------------------------------

/--
The complete converse circle theorem for the crossing-rays configuration.

No circle theorem is assumed in crossing-specific form.

Instead, the proof uses:

* Stage 2 order/side/angle classification;
* Forder IV.19 in the same-side branches;
* Forder IV.20 in the mixed branches;
* the already-proved degenerate crossing theorem.

This is exactly the source decomposition hidden by the former temporary
`circle_crossing_chords_concyclic` axiom.
-/
theorem hilbert_crossing_chords_concyclic_of_forder_stage3
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV19 :
      HilbertForderIV19CircleConverse
        (Geo := Geo))
    (hIV20 :
      HilbertForderIV20CircleConverse
        (Geo := Geo))
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    HilbertConcyclic4 Geo A C D B := by

  by_cases hAC : A = C

  --------------------------------------------------------------------
  -- Degenerate first secant.
  --------------------------------------------------------------------

  · exact
      hilbert_crossing_concyclic_degenerate_stage2
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        (Or.inl hAC)

  by_cases hBD : B = D

  --------------------------------------------------------------------
  -- Degenerate second secant.
  --------------------------------------------------------------------

  · exact
      hilbert_crossing_concyclic_degenerate_stage2
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        (Or.inr hBD)

  --------------------------------------------------------------------
  -- Proper chord CD.
  --------------------------------------------------------------------

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  --------------------------------------------------------------------
  -- Stage 2 gives exactly the IV.19 / IV.20 alternatives.
  --------------------------------------------------------------------

  rcases
      hilbert_crossing_nondegenerate_chord_classification_stage2
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
        hAngle
    with
    ⟨chord,
      hCchord,
      hDchord,
      hClass⟩

  rcases hClass with
    hSameCase | hMixedCase

  --------------------------------------------------------------------
  -- Same side: direct Forder IV.19.
  --------------------------------------------------------------------

  · rcases hSameCase with
      ⟨hSame, hEq⟩

    exact
      hIV19
        C D A B
        chord
        hCD
        hCchord
        hDchord
        hSame
        hEq

  rcases hMixedCase with
    hMixedA | hMixedB

  --------------------------------------------------------------------
  -- Opposite sides, supplement at A: direct Forder IV.20.
  --------------------------------------------------------------------

  · rcases hMixedA with
      ⟨hOpp, hSuppA, hCongA⟩

    exact
      hIV20
        C D A B O
        chord
        hCD
        hCchord
        hDchord
        hOpp
        hSuppA
        hCongA

  --------------------------------------------------------------------
  -- Opposite sides, supplement at B.
  --
  -- Apply IV.20 after swapping
  --
  --   C <-> D
  --   A <-> B.
  --
  -- The resulting cyclic order B,D,C,A is then converted back to
  -- A,C,D,B by reversal followed by one cyclic rotation.
  --------------------------------------------------------------------

  · rcases hMixedB with
      ⟨hOpp, hCongB, hSuppB⟩

    have hOppBA :
        HilbertOppositeSide Geo B A chord :=
      hilbert_oppositeSide_symm
        Geo A B chord hOpp

    have hOBC_CAD :
        Geo.AngleCongruent
          O B C
          C A D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        C A D
        O B C
        hCongB

    have hOBC_DAC :
        Geo.AngleCongruent
          O B C
          D A C :=
      (Geo.angle_congruent_reverse_second
        O B C
        C A D).mp
        hOBC_CAD

    have hCyclicSwap :
        HilbertConcyclic4 Geo
          B D C A :=
      hIV20
        D C B A O
        chord
        hCD.symm
        hDchord
        hCchord
        hOppBA
        hSuppB
        hOBC_DAC

    have hCyclicRev :
        HilbertConcyclic4 Geo
          B A C D :=
      hilbert_concyclic4_reverse
        Geo
        B D C A
        hCyclicSwap

    exact
      hilbert_concyclic4_rotate
        Geo
        B A C D
        hCyclicRev
/- END folded proof support: Crossing_circle_stage3_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage4_secant_tangent_v5.lean -/
/-!
# Circle converse infrastructure -- stage 4

Forder IV.19 uses the following elementary circle-line dichotomy.

Given a point A on a circle and a line through A, either

* the line has a second point E on the circle, or
* the line is perpendicular at A to the radius KA, i.e. it is tangent
  there in the synthetic sense needed by the proof.

No circle-line continuity theorem is required.

If the center K lies on the line, the second point is the antipodal
extension across K.

If K is off the line, drop the perpendicular KH to the line.  When H=A
we are in the tangent case.  Otherwise reflect A across H to E.  Since
K lies on the perpendicular bisector of AE, KA ~= KE, so E is the
second point of the same circle.

This is the exact construction hidden in Forder's phrase "the circle
either meets AD in E != A,D, or AD touches the circle at A".
-/

------------------------------------------------------------------------
-- 2. A line through a circle point: second point or tangent.
------------------------------------------------------------------------

/--
Synthetic secant/tangent dichotomy for a line through a point of a
Hilbert circle.

No continuity or circle-line intersection axiom is used.
-/
theorem hilbert_circle_line_second_or_tangent_stage4
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A D : Geo.Point)
    (line : Geo.Line)
    (hA : HilbertCircle Geo K R A)
    (hKA : Ne K A)
    (hAD : Ne A D)
    (hAline : H.OnLine A line)
    (hDline : H.OnLine D line) :
    (
      exists E : Geo.Point,
        Ne E A /\
        H.OnLine E line /\
        HilbertCircle Geo K R E
    )
    \/
    HilbertCircleTangentAtStage4
      (Geo := Geo)
      K A line := by

  have hKA_KR :
      Geo.Congruent K A K R := by
    simpa [HilbertCircle] using hA

  by_cases hKline : H.OnLine K line

  --------------------------------------------------------------------
  -- The center lies on the line: take the antipodal point.
  --------------------------------------------------------------------

  · rcases
        hilbert_extend_segment_beyond
          Geo A K hKA.symm
      with
      ⟨E, hAKE, hAK_KE⟩

    have hAKEcol :
        PrimCollinear Geo A K E :=
      (HilbertOrder.between_incidence
        A K E hAKE).2.2.2.1

    have hEline :
        H.OnLine E line :=
      hilbert_collinear_on_line
        Geo
        A K E
        line
        hKA.symm
        hAline
        hKline
        hAKEcol

    have hAE :
        Ne A E :=
      (HilbertOrder.between_incidence
        A K E hAKE).2.2.1

    have hEneA :
        Ne E A := by
      intro hEA
      exact hAE hEA.symm

    have hKE_AK :
        Geo.Congruent K E A K :=
      hilbert_congruent_symmetry
        Geo
        A K
        K E
        hAK_KE

    have hKE_KA :
        Geo.Congruent K E K A :=
      (Geo.congruent_reverse_second
        K E
        A K).mp
        hKE_AK

    have hKE_KR :
        Geo.Congruent K E K R :=
      hilbert_congruent_transitivity
        Geo
        K E
        K A
        K R
        hKE_KA
        hKA_KR

    have hE :
        HilbertCircle Geo K R E := by
      simpa [HilbertCircle] using hKE_KR

    exact
      Or.inl
        ⟨E,
          hEneA,
          hEline,
          hE⟩

  --------------------------------------------------------------------
  -- The center is off the line.  Drop KH perpendicular to the line.
  --------------------------------------------------------------------

  · rcases
        hilbert_perpendicular_from_point_exists
          Geo
          A D K
          line
          hAD
          hAline
          hDline
          hKline
      with
      ⟨M, T, hMline, hTline, hRightTMK⟩

    by_cases hMA : M = A

    ------------------------------------------------------------------
    -- The perpendicular foot is A: tangent at A.
    ------------------------------------------------------------------

    · subst M

      have hRightCopy := hRightTMK

      rcases hRightCopy with
        ⟨X, hTAX, _hAngle⟩

      have hTA :
          Ne T A :=
        (HilbertOrder.between_incidence
          T A X hTAX).1

      have hTAK :
          Not (PrimCollinear Geo T A K) :=
        hilbert_not_collinear_of_off_line
          Geo
          T A K
          line
          hTA
          hTline
          hAline
          hKline

      exact
        Or.inr
          ⟨T,
            hTline,
            hTA,
            hTAK,
            hRightTMK⟩

    ------------------------------------------------------------------
    -- The perpendicular foot M differs from A.
    -- Reflect A across M to obtain the second circle point E.
    ------------------------------------------------------------------

    · have hAM :
          Ne A M := by
        intro hAMeq
        exact hMA hAMeq.symm

      rcases
          hilbert_extend_segment_beyond
            Geo A M hAM
        with
        ⟨E, hAME, hAM_ME⟩

      have hAMEcol :
          PrimCollinear Geo A M E :=
        (HilbertOrder.between_incidence
          A M E hAME).2.2.2.1

      have hEline :
          H.OnLine E line :=
        hilbert_collinear_on_line
          Geo
          A M E
          line
          hAM
          hAline
          hMline
          hAMEcol

      have hAE :
          Ne A E :=
        (HilbertOrder.between_incidence
          A M E hAME).2.2.1

      have hEneA :
          Ne E A := by
        intro hEA
        exact hAE hEA.symm

      have hMid :
          HilbertIsMidpoint Geo M A E :=
        ⟨hAME, hAM_ME⟩

      ----------------------------------------------------------------
      -- Normalize the perpendicular from the arbitrary line point T
      -- to the actual chord point A.
      ----------------------------------------------------------------

      have hRightCopy := hRightTMK

      rcases hRightCopy with
        ⟨X, hTMX, _hAngleTMK⟩

      have hTM :
          Ne T M :=
        (HilbertOrder.between_incidence
          T M X hTMX).1

      have hTMK :
          Not (PrimCollinear Geo T M K) :=
        hilbert_not_collinear_of_off_line
          Geo
          T M K
          line
          hTM
          hTline
          hMline
          hKline

      have hMTA :
          PrimCollinear Geo M T A :=
        ⟨line,
          hMline,
          hTline,
          hAline⟩

      have hRightAMK :
          HilbertRightAngle Geo A M K :=
        hilbert_right_angle_collinear_first_XI
          Geo
          T M K A
          hTMK
          hRightTMK
          hMTA
          hMA

      ----------------------------------------------------------------
      -- K lies on the perpendicular bisector of AE.
      ----------------------------------------------------------------

      have hAMK :
          Not (PrimCollinear Geo A M K) :=
        hilbert_not_collinear_of_off_line
          Geo
          A M K
          line
          hAM
          hAline
          hMline
          hKline

      have hMK :
          Ne M K := by
        intro hEq
        apply hKline
        rw [← hEq]
        exact hMline

      rcases
          HilbertPlaneIncidence.line_through
            M K hMK
        with
        ⟨bis, hMbis, hKbis⟩

      have hKA_KE :
          Geo.Congruent K A K E :=
        hilbert_point_on_perpendicularBisector_equidistant_XI
          Geo
          A E
          M K K
          bis
          hMid
          hAMK
          hRightAMK
          hMbis
          hKbis
          hKbis

      have hKE_KA :
          Geo.Congruent K E K A :=
        hilbert_congruent_symmetry
          Geo
          K A
          K E
          hKA_KE

      have hKE_KR :
          Geo.Congruent K E K R :=
        hilbert_congruent_transitivity
          Geo
          K E
          K A
          K R
          hKE_KA
          hKA_KR

      have hEcircle :
          HilbertCircle Geo K R E := by
        simpa [HilbertCircle] using hKE_KR

      exact
        Or.inl
          ⟨E,
            hEneA,
            hEline,
            hEcircle⟩
/- END folded proof support: Crossing_circle_stage4_secant_tangent_v5.lean -/

/- BEGIN folded proof support: Crossing_circle_stage5_forder19_secant_v3.lean -/
/-!
# Forder IV.19 -- stage 5, first secant branch

Stage 4 supplied the source-faithful dichotomy for a line through a
known point of a circle: either there is a second circle point on the
line, or the line is tangent there.

The present file isolates the first genuinely IV.19-specific rigidity
step.  It treats the secant subcase in which the second circle point E
lies on the same ray AD as the prescribed point D.

The only lower circle result used as an explicit interface is the
same-side half of Forder IV.16:

  A,B,C,E on one circle,
  C,E on the same side of AB
  --------------------------------
  angle ACB ~= angle AEB.

Together with the IV.19 hypothesis angle ACB ~= angle ADB, equality of
the two angles on the same secant ray forces E=D by the exterior-angle
uniqueness argument proved below.

No axiom is declared in this file.
-/

------------------------------------------------------------------------
-- 2. Uniqueness of a point on one secant ray from equality of angles.
------------------------------------------------------------------------

/--
If B and B' lie on one ray from O and

  angle OBC ~= angle OB'C,

then B=B'.  Either strict order alternative makes one of the two equal
angles an exterior angle of the triangle determined by the other point
and C, contradicting the exterior-angle theorem.
-/
theorem hilbert_equal_angles_same_secant_unique_stage5
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (O B Bp C : Geo.Point)
    (hOBC : Not (PrimCollinear Geo O B C))
    (hRay :
      HilbertSameRay Geo O B Bp)
    (hAngle :
      Geo.AngleCongruent
        O B C
        O Bp C) :
    B = Bp := by

  rcases
      hilbert_sameRay_cases
        Geo O B Bp hRay
    with
    hEq | hOBBp | hOBpB

  --------------------------------------------------------------------
  -- B = B'.
  --------------------------------------------------------------------

  · exact hEq

  --------------------------------------------------------------------
  -- O-B-B'.
  --------------------------------------------------------------------

  · have hOBBpData :=
      HilbertOrder.between_incidence
        O B Bp hOBBp

    have hBBp :
        Ne B Bp :=
      hOBBpData.2.1

    have hOBBpcol :
        PrimCollinear Geo O B Bp :=
      hOBBpData.2.2.2.1

    have hBBpC :
        Not (PrimCollinear Geo B Bp C) := by

      intro hBBpC

      have hOBC' :
          PrimCollinear Geo O B C :=
        hilbert_primCollinear_trans
          Geo
          O B Bp C
          hBBp
          hOBBpcol
          hBBpC

      exact hOBC hOBC'

    have hBpBO :
        Geo.Between Bp B O :=
      hOBBpData.2.2.2.2

    have hRayBpBO :
        HilbertSameRay Geo Bp B O :=
      hilbert_sameRay_of_between
        Geo Bp B O hBpBO

    have hAtBp :
        Geo.Angle B Bp C =
        Geo.Angle O Bp C :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        Bp B O C
        hRayBpBO

    have hCBO_OBpC :
        Geo.AngleCongruent
          C B O
          O Bp C :=
      (Geo.angle_congruent_reverse_first
        O B C
        O Bp C).mp
        hAngle

    have hExterior :
        Geo.AngleCongruent
          C B O
          B Bp C := by

      unfold Geometry.Geo.AngleCongruent
        at hCBO_OBpC ⊢

      rw [hAtBp]

      exact hCBO_OBpC

    exact
      False.elim
        ((hilbert_exterior_angle_not_congruent_other
            Geo
            B Bp C O
            hBBpC
            hBpBO)
          hExterior)

  --------------------------------------------------------------------
  -- O-B'-B.
  --------------------------------------------------------------------

  · have hOBpBData :=
      HilbertOrder.between_incidence
        O Bp B hOBpB

    have hBpB :
        Ne Bp B :=
      hOBpBData.2.1

    have hOBpBcol :
        PrimCollinear Geo O Bp B :=
      hOBpBData.2.2.2.1

    have hBpBC :
        Not (PrimCollinear Geo Bp B C) := by

      intro hBpBC

      have hOBBpcol :
          PrimCollinear Geo O B Bp :=
        PrimCollinearRotate
          Geo O Bp B hOBpBcol

      have hBBpC :
          PrimCollinear Geo B Bp C :=
        PrimCollinearSwap
          Geo Bp B C hBpBC

      have hOBC' :
          PrimCollinear Geo O B C :=
        hilbert_primCollinear_trans
          Geo
          O B Bp C
          hBpB.symm
          hOBBpcol
          hBBpC

      exact hOBC hOBC'

    have hBBpO :
        Geo.Between B Bp O :=
      hOBpBData.2.2.2.2

    have hRayBBpO :
        HilbertSameRay Geo B Bp O :=
      hilbert_sameRay_of_between
        Geo B Bp O hBBpO

    have hAtB :
        Geo.Angle Bp B C =
        Geo.Angle O B C :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        B Bp O C
        hRayBBpO

    have hSym :
        Geo.AngleCongruent
          O Bp C
          O B C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        O B C
        O Bp C
        hAngle

    have hCBpO_OBC :
        Geo.AngleCongruent
          C Bp O
          O B C :=
      (Geo.angle_congruent_reverse_first
        O Bp C
        O B C).mp
        hSym

    have hExterior :
        Geo.AngleCongruent
          C Bp O
          Bp B C := by

      unfold Geometry.Geo.AngleCongruent
        at hCBpO_OBC ⊢

      rw [hAtB]

      exact hCBpO_OBC

    exact
      False.elim
        ((hilbert_exterior_angle_not_congruent_other
            Geo
            Bp B C O
            hBpBC
            hBBpO)
          hExterior)


------------------------------------------------------------------------
-- 3. Forder IV.19: the same-ray secant branch.
------------------------------------------------------------------------

/--
Secant rigidity in the direct Forder IV.19 proof.

A and B determine the chord line.  C and D are on the same side of AB
and satisfy

  angle ACB ~= angle ADB.

Let E be a second point of the circle through A,B,C, lying on the same
ray AD as D.  Forder IV.16 gives angle ACB ~= angle AEB.  Hence
angle AEB ~= angle ADB, and the same-secant uniqueness theorem forces
E=D.

The conclusion is exactly the contradiction needed in IV.19 when D was
assumed not to lie on the circle.
-/
theorem hilbert_forder_IV19_secant_sameRay_stage5
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16 :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (K R A B C D E : Geo.Point)
    (chord lineAD : Geo.Line)
    (hAB : Ne A B)
    (hAD : Ne A D)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hBnotLineAD : Not (H.OnLine B lineAD))
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C)
    (hE : HilbertCircle Geo K R E)
    (hSameCD : HilbertSameSide Geo C D chord)
    (hRayADE : HilbertSameRay Geo A D E)
    (hAngle :
      Geo.AngleCongruent
        A C B
        A D B) :
    E = D := by

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSameDE :
      HilbertSameSide Geo D E chord :=
    hilbert_sameRay_points_sameSide
      Geo
      A D D E B
      lineAD chord
      hAline hDline
      hAchord hBchord
      hBnotLineAD
      hRayADD hRayADE

  have hSameCE :
      HilbertSameSide Geo C E chord :=
    hilbert_sameSide_trans
      Geo
      C D E
      chord
      hSameCD
      hSameDE

  have hACB_AEB :
      Geo.AngleCongruent
        A C B
        A E B :=
    hIV16
      K R A B C E
      chord
      hAB
      hAchord
      hBchord
      hA
      hB
      hC
      hE
      hSameCE

  have hAEB_ACB :
      Geo.AngleCongruent
        A E B
        A C B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A C B
      A E B
      hACB_AEB

  have hAEB_ADB :
      Geo.AngleCongruent
        A E B
        A D B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A E B
      A C B
      A D B
      hAEB_ACB
      hAngle

  have hABE :
      Not (PrimCollinear Geo A B E) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B E
      chord
      hAB
      hAchord
      hBchord
      hSameCE.2.1

  have hAEB :
      Not (PrimCollinear Geo A E B) := by
    intro hAEBcol
    apply hABE
    exact
      PrimCollinearRotate
        Geo A E B hAEBcol

  have hRayAED :
      HilbertSameRay Geo A E D :=
    hilbert_sameRay_symm
      Geo A D E hRayADE

  exact
    hilbert_equal_angles_same_secant_unique_stage5
      Geo
      A E D B
      hAEB
      hRayAED
      hAEB_ADB
/- END folded proof support: Crossing_circle_stage5_forder19_secant_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage5_forder19_secant_v5.lean -/
/-!
# Forder IV.19 -- stage 5, secant order split

The direct same-ray secant branch is already closed in v3.
This file adds the order normalization needed for the remaining secant
branch.

For a second point E on the carrier AD, with E != D, exactly the two
geometrically relevant alternatives are isolated:

* E lies on the same ray AD from A, or
* A lies strictly between D and E.

In the second alternative D and E lie on opposite sides of the chord AB.
Since C and D are on the same side of AB in Forder IV.19, C and E are
therefore on opposite sides of AB.

No new axiom or circle theorem is introduced here.
-/

------------------------------------------------------------------------
-- 1. Normalize the order of a second point on line AD.
------------------------------------------------------------------------

/--
Let A,D,E be distinct collinear points.  Relative to the ray from A
through D, either E lies on that same ray, or A lies between D and E.
-/
theorem hilbert_forder_IV19_secant_order_split_stage5
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H]
    (A D E : Geo.Point)
    (lineAD : Geo.Line)
    (hAD : Ne A D)
    (hDE : Ne D E)
    (hAE : Ne A E)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hEline : H.OnLine E lineAD) :
    HilbertSameRay Geo A D E \/
    Geo.Between D A E := by

  have hADEcol :
      PrimCollinear Geo A D E :=
    ⟨lineAD,
      hAline,
      hDline,
      hEline⟩

  rcases
      hilbert_between_trichotomy
        Geo A D E
        hAD
        hDE
        hAE
        hADEcol
    with
    hADE | hDEA | hEAD

  --------------------------------------------------------------------
  -- A-D-E: direct same ray.
  --------------------------------------------------------------------

  · exact
      Or.inl
        (hilbert_sameRay_of_between
          Geo A D E hADE)

  --------------------------------------------------------------------
  -- D-A-E: the opposite-ray case.
  --------------------------------------------------------------------

  · exact Or.inr hDEA

  --------------------------------------------------------------------
  -- A-E-D: E and D are still on the same ray from A.
  --------------------------------------------------------------------

  · have hRayAED :
        HilbertSameRay Geo A E D :=
      hilbert_sameRay_of_between
        Geo A E D hEAD

    exact
      Or.inl
        (hilbert_sameRay_symm
          Geo A E D hRayAED)


------------------------------------------------------------------------
-- 2. Opposite-ray branch -> opposite sides of the chord.
------------------------------------------------------------------------

/--
Forder IV.19 side normalization for the opposite-ray secant branch.

C and D are on the same side of chord AB.  If D-A-E, with D and E on
the carrier AD, then D and E are on opposite sides of AB because the
segment DE crosses AB at A.  Hence C and E are on opposite sides of AB.
-/
theorem hilbert_forder_IV19_oppositeRay_gives_oppositeSide_stage5
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H]
    (A B C D E : Geo.Point)
    (chord lineAD : Geo.Line)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hBnotLineAD : Not (H.OnLine B lineAD))
    (hSameCD : HilbertSameSide Geo C D chord)
    (hDAE : Geo.Between D A E) :
    HilbertOppositeSide Geo C E chord := by

  have hDAEdata :=
    HilbertOrder.between_incidence
      D A E hDAE

  have hDA :
      Ne D A :=
    hDAEdata.1

  have hAE :
      Ne A E :=
    hDAEdata.2.1

  have hDAEcol :
      PrimCollinear Geo D A E :=
    hDAEdata.2.2.2.1

  have hEline :
      H.OnLine E lineAD :=
    hilbert_collinear_on_line
      Geo
      D A E
      lineAD
      hDA
      hDline
      hAline
      hDAEcol

  have hEoff :
      Not (H.OnLine E chord) := by
    intro hEchord

    have hEq :
        chord = lineAD :=
      HilbertPlaneIncidence.line_unique
        A E hAE
        chord lineAD
        hAchord hEchord
        hAline hEline

    have hBline :
        H.OnLine B lineAD := by
      rw [← hEq]
      exact hBchord

    exact hBnotLineAD hBline

  have hDoff :
      Not (H.OnLine D chord) :=
    hSameCD.2.1

  have hOppDE :
      HilbertOppositeSide Geo D E chord :=
    ⟨hDoff,
      hEoff,
      ⟨A,
        hDAE,
        hAchord⟩⟩

  have hOppED :
      HilbertOppositeSide Geo E D chord :=
    hilbert_oppositeSide_symm
      Geo D E chord hOppDE

  have hSameDC :
      HilbertSameSide Geo D C chord :=
    hilbert_sameSide_symm
      Geo C D chord hSameCD

  have hOppEC :
      HilbertOppositeSide Geo E C chord :=
    hilbert_oppositeSide_transport_right
      Geo
      E D C
      chord
      hOppED
      hSameDC

  exact
    hilbert_oppositeSide_symm
      Geo E C chord hOppEC
/- END folded proof support: Crossing_circle_stage5_forder19_secant_v5.lean -/

/- BEGIN folded proof support: Crossing_circle_stage5_forder19_secant_v6.lean -/
/-!
# Forder IV.19 -- stage 5, opposite-ray secant branch

The same-ray secant branch was closed in v3 and the order/side
normalization was completed in v5.

This file isolates the opposite-side half of Forder IV.16 in the same
synthetic style already used for IV.20: supplementary angles are
represented by `BookZeroSupplement`, not by a numerical angle sum.

In the remaining secant branch D-A-E, IV.16 says that angle ACB is
congruent to a supplement of angle AEB.  Since angle ACB ~= angle ADB
by the IV.19 hypothesis, and the rays DA/DE agree, the remote interior
angle EDB becomes congruent to the exterior angle at E.  Hilbert's
exterior-angle theorem gives the contradiction.

No new axiom is introduced.
-/

------------------------------------------------------------------------
-- 2. The opposite-ray secant branch is impossible.
------------------------------------------------------------------------

/--
The remaining secant branch in Forder IV.19 cannot occur.

Assume D-A-E.  Since C,D are on the same side of AB, stage 5 v5 gives
that C,E are on opposite sides of AB.  Forder IV.16 therefore supplies
X with A-E-X and

  angle ACB ~= angle XEB.

Together with the IV.19 hypothesis

  angle ACB ~= angle ADB

and the fact that A and E determine the same ray from D, this gives

  angle EDB ~= angle XEB.

But D-E-X, so XEB is an exterior angle of triangle DEB.  It cannot be
congruent to the remote interior angle EDB.
-/
theorem hilbert_forder_IV19_secant_oppositeRay_impossible_stage5
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (K R A B C D E : Geo.Point)
    (chord lineAD : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hBnotLineAD : Not (H.OnLine B lineAD))
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C)
    (hE : HilbertCircle Geo K R E)
    (hSameCD : HilbertSameSide Geo C D chord)
    (hDAE : Geo.Between D A E)
    (hAngle :
      Geo.AngleCongruent
        A C B
        A D B) :
    False := by

  --------------------------------------------------------------------
  -- C and E are on opposite sides of chord AB.
  --------------------------------------------------------------------

  have hOppCE :
      HilbertOppositeSide Geo C E chord :=
    hilbert_forder_IV19_oppositeRay_gives_oppositeSide_stage5
      Geo
      A B C D E
      chord lineAD
      hAchord hBchord
      hAline hDline
      hBnotLineAD
      hSameCD
      hDAE

  --------------------------------------------------------------------
  -- Forder IV.16: ACB is congruent to a supplement XEB of AEB.
  --------------------------------------------------------------------

  rcases
      hIV16Opp
        K R A B C E
        chord
        hAB
        hAchord
        hBchord
        hA hB hC hE
        hOppCE
    with
    ⟨X, hSuppE, hACB_XEB⟩

  have hAEX :
      Geo.Between A E X :=
    hSuppE.2

  --------------------------------------------------------------------
  -- D-A-E and A-E-X imply D-E-X.
  --------------------------------------------------------------------

  have hDEX :
      Geo.Between D E X :=
    (hilbert_between_outer_trans
      Geo
      D A E X
      hDAE hAEX).1

  --------------------------------------------------------------------
  -- Replace ray DA by the same ray DE in angle ADB.
  --------------------------------------------------------------------

  have hRayDAE :
      HilbertSameRay Geo D A E :=
    hilbert_sameRay_of_between
      Geo D A E hDAE

  have hAtD :
      Geo.Angle A D B =
      Geo.Angle E D B :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      D A E B
      hRayDAE

  have hADB_ACB :
      Geo.AngleCongruent
        A D B
        A C B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A C B
      A D B
      hAngle

  have hADB_XEB :
      Geo.AngleCongruent
        A D B
        X E B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A D B
      A C B
      X E B
      hADB_ACB
      hACB_XEB

  have hEDB_XEB :
      Geo.AngleCongruent
        E D B
        X E B := by
    unfold Geometry.Geo.AngleCongruent
      at hADB_XEB ⊢
    rw [← hAtD]
    exact hADB_XEB

  --------------------------------------------------------------------
  -- XEB is an exterior angle of triangle DEB.
  --------------------------------------------------------------------

  have hDAEdata :=
    HilbertOrder.between_incidence
      D A E hDAE

  have hDA :
      Ne D A :=
    hDAEdata.1

  have hDE :
      Ne D E :=
    hDAEdata.2.2.1

  have hDAEcol :
      PrimCollinear Geo D A E :=
    hDAEdata.2.2.2.1

  have hEline :
      H.OnLine E lineAD :=
    hilbert_collinear_on_line
      Geo
      D A E
      lineAD
      hDA
      hDline
      hAline
      hDAEcol

  have hDEB :
      Not (PrimCollinear Geo D E B) :=
    hilbert_not_collinear_of_off_line
      Geo
      D E B
      lineAD
      hDE
      hDline
      hEline
      hBnotLineAD

  have hEDB :
      Not (PrimCollinear Geo E D B) := by
    intro h
    exact
      hDEB
        (PrimCollinearSwap
          Geo E D B h)

  have hXEB_EDB :
      Geo.AngleCongruent
        X E B
        E D B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E D B
      X E B
      hEDB_XEB

  have hBEX_EDB :
      Geo.AngleCongruent
        B E X
        E D B :=
    (Geo.angle_congruent_reverse_first
      X E B
      E D B).mp
      hXEB_EDB

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      E D B X
      hEDB
      hDEX)
      hBEX_EDB
/- END folded proof support: Crossing_circle_stage5_forder19_secant_v6.lean -/

/- BEGIN folded proof support: Crossing_circle_stage5_forder19_tangent_v2.lean -/
/-!
# Forder IV.19 -- stage 5, tangent branch

The secant branch of Forder IV.19 is closed in
`Crossing_circle_stage5_forder19_secant_v6`.

This file isolates the tangent-chord theorem Forder IV.18 in the exact
form needed by the remaining branch and proves that the tangent branch
is impossible under the IV.19 equal-angle hypothesis.

No numerical angle measure is introduced.
No new axiom is introduced: IV.18 is represented as a `Prop` interface,
just as IV.16 was in the secant branch.
-/

------------------------------------------------------------------------
-- 2. The tangent branch in Forder IV.19 is impossible.
------------------------------------------------------------------------

/--
The tangent alternative supplied by stage 4 cannot occur in Forder
IV.19.

C and D lie on the same side of chord AB.  Extend DA through A to Z,
so D-A-Z.  Then D and Z are on opposite sides of AB, hence C and Z are
also on opposite sides of AB.

Forder IV.18 gives

  angle BAZ ~= angle BCA.

After reversing the arms at C and using the IV.19 hypothesis

  angle ACB ~= angle ADB,

we obtain

  angle BAZ ~= angle ADB.

But D-A-Z, so BAZ is an exterior angle of triangle DAB and ADB is a
remote interior angle.  Hilbert's exterior-angle theorem gives the
contradiction.
-/
theorem hilbert_forder_IV19_tangent_impossible_stage5
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo))
    (K R A B C D : Geo.Point)
    (chord lineAD : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hBnotLineAD : Not (H.OnLine B lineAD))
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C)
    (hSameCD : HilbertSameSide Geo C D chord)
    (hTan :
      HilbertCircleTangentAtStage4
        (Geo := Geo) K A lineAD)
    (hAngle :
      Geo.AngleCongruent
        A C B
        A D B) :
    False := by

  --------------------------------------------------------------------
  -- D is off the chord, while A is on it; hence D != A.
  --------------------------------------------------------------------

  have hDoff :
      Not (H.OnLine D chord) :=
    hSameCD.2.1

  have hDA :
      Ne D A := by
    intro hDAeq
    subst D
    exact hDoff hAchord

  --------------------------------------------------------------------
  -- Extend DA through A to Z: D-A-Z.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        D A hDA
    with
    ⟨Z, hDAZ⟩

  have hDAZdata :=
    HilbertOrder.between_incidence
      D A Z hDAZ

  have hAZ :
      Ne A Z :=
    hDAZdata.2.1

  have hDZ :
      Ne D Z :=
    hDAZdata.2.2.1

  have hDAZcol :
      PrimCollinear Geo D A Z :=
    hDAZdata.2.2.2.1

  have hZline :
      H.OnLine Z lineAD :=
    hilbert_collinear_on_line
      Geo
      D A Z
      lineAD
      hDA
      hDline
      hAline
      hDAZcol

  --------------------------------------------------------------------
  -- Z is off chord AB.
  --------------------------------------------------------------------

  have hZoff :
      Not (H.OnLine Z chord) := by
    intro hZchord

    have hEq :
        chord = lineAD :=
      HilbertPlaneIncidence.line_unique
        A Z hAZ
        chord lineAD
        hAchord hZchord
        hAline hZline

    have hBline :
        H.OnLine B lineAD := by
      rw [<- hEq]
      exact hBchord

    exact hBnotLineAD hBline

  --------------------------------------------------------------------
  -- D and Z are opposite across AB because D-A-Z and A lies on AB.
  -- Transport from D to C using the given same-side hypothesis.
  --------------------------------------------------------------------

  have hOppDZ :
      HilbertOppositeSide Geo D Z chord :=
    ⟨hDoff,
      hZoff,
      ⟨A,
        hDAZ,
        hAchord⟩⟩

  have hOppZD :
      HilbertOppositeSide Geo Z D chord :=
    hilbert_oppositeSide_symm
      Geo D Z chord hOppDZ

  have hSameDC :
      HilbertSameSide Geo D C chord :=
    hilbert_sameSide_symm
      Geo C D chord hSameCD

  have hOppZC :
      HilbertOppositeSide Geo Z C chord :=
    hilbert_oppositeSide_transport_right
      Geo
      Z D C
      chord
      hOppZD
      hSameDC

  --------------------------------------------------------------------
  -- Forder IV.18: angle BAZ ~= angle BCA.
  --------------------------------------------------------------------

  have hBAZ_BCA :
      Geo.AngleCongruent
        B A Z
        B C A :=
    hIV18
      K R B A C Z
      chord lineAD
      hAB.symm
      hBchord
      hAchord
      hAline
      hZline
      hAZ.symm
      hB hA hC
      hTan
      hOppZC

  --------------------------------------------------------------------
  -- Reverse the arms at C: BCA is the same angle as ACB.
  --------------------------------------------------------------------

  have hBAZ_ACB :
      Geo.AngleCongruent
        B A Z
        A C B := by
    have hAtC :
        Geo.Angle B C A =
        Geo.Angle A C B :=
      Geo.angle_swap B C A
    unfold Geometry.Geo.AngleCongruent
      at hBAZ_BCA ⊢
    rw [← hAtC]
    exact hBAZ_BCA

  have hBAZ_ADB :
      Geo.AngleCongruent
        B A Z
        A D B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A Z
      A C B
      A D B
      hBAZ_ACB
      hAngle

  --------------------------------------------------------------------
  -- Triangle DAB is nondegenerate because B is off line AD.
  --------------------------------------------------------------------

  have hAD :
      Ne A D :=
    hDA.symm

  have hADB :
      Not (PrimCollinear Geo A D B) :=
    hilbert_not_collinear_of_off_line
      Geo
      A D B
      lineAD
      hAD
      hAline
      hDline
      hBnotLineAD

  --------------------------------------------------------------------
  -- BAZ is the exterior angle at A of triangle DAB.
  --------------------------------------------------------------------

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      A D B Z
      hADB
      hDAZ)
      hBAZ_ADB
/- END folded proof support: Crossing_circle_stage5_forder19_tangent_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage6_forder19_complete_v3.lean -/
/-!
# Forder IV.19 -- stage 6, complete converse

Stages 4 and 5 established all local ingredients for Forder IV.19:

* a line through a point of a circle has either a second circle point
  or is tangent there;
* the secant branch is impossible unless the prescribed point is that
  second circle point;
* the tangent branch is impossible under the IV.19 equal-angle
  hypothesis.

This file only composes those ingredients into the full source-faithful
Forder IV.19 converse used by `Crossing_circle_stage3_v2`.

No new axiom is introduced.
-/

------------------------------------------------------------------------
-- Complete Forder IV.19.
------------------------------------------------------------------------

/--
Forder IV.19.

If A and B lie on the same side of the chord line CD and

  angle CAD ~= angle CBD,

then A,C,D,B are concyclic.

The proof constructs the circumcircle through C,D,A.  If B is already
on it, the result is immediate.  Otherwise apply the stage-4
secant/tangent dichotomy to the line CB through the circle point C.

In the secant case, the second circle point E is either on the same ray
CB as B or C lies between B and E.  The first alternative forces E=B,
contrary to the assumption that B is off the circle; the second is the
opposite-ray contradiction proved in stage 5.

The tangent alternative is the tangent contradiction proved in stage 5.
-/
theorem hilbert_forder_IV19_circle_converse_stage6
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo)) :
    HilbertForderIV19CircleConverse
      (Geo := Geo) := by

  intro C D A B chord hCD hCchord hDchord hSameAB hAngle

  --------------------------------------------------------------------
  -- A is off chord CD, hence C,D,A form a genuine triangle.
  --------------------------------------------------------------------

  have hAoff :
      Not (H.OnLine A chord) :=
    hSameAB.1

  have hBoff :
      Not (H.OnLine B chord) :=
    hSameAB.2.1

  have hCDA :
      Not (PrimCollinear Geo C D A) :=
    hilbert_not_collinear_of_off_line
      Geo
      C D A
      chord
      hCD
      hCchord
      hDchord
      hAoff

  --------------------------------------------------------------------
  -- Circumcircle through C,D,A, with reference radius KC.
  --------------------------------------------------------------------

  rcases
      hilbert_triangle_circumcenter_exists_XI
        Geo
        C D A
        hCDA
    with
    ⟨K, hKC_KD, hKC_KA⟩

  have hCcircle :
      HilbertCircle Geo K C C :=
    hilbert_circle_reference_mem
      Geo K C

  have hDcircle :
      HilbertCircle Geo K C D := by
    unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K C
        K D
        hKC_KD

  have hAcircle :
      HilbertCircle Geo K C A := by
    unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K C
        K A
        hKC_KA

  --------------------------------------------------------------------
  -- If B is already on this circle, we are done.
  --------------------------------------------------------------------

  by_cases hBcircle :
      HilbertCircle Geo K C B

  · exact
      hilbert_concyclic4_of_circle
        Geo
        K C
        A C D B
        hAcircle
        hCcircle
        hDcircle
        hBcircle

  --------------------------------------------------------------------
  -- Otherwise analyze the carrier CB at the circle point C.
  --------------------------------------------------------------------

  · have hCB :
        Ne C B := by
      intro hCB
      subst B
      exact hBoff hCchord

    rcases
        HilbertPlaneIncidence.line_through
          C B hCB
      with
      ⟨lineCB, hCline, hBline⟩

    have hCDB :
        Not (PrimCollinear Geo C D B) :=
      hilbert_not_collinear_of_off_line
        Geo
        C D B
        chord
        hCD
        hCchord
        hDchord
        hBoff

    have hDnotLineCB :
        Not (H.OnLine D lineCB) := by
      intro hDline
      exact
        hCDB
          ⟨lineCB,
            hCline,
            hDline,
            hBline⟩

    ------------------------------------------------------------------
    -- The circle center differs from C.
    ------------------------------------------------------------------

    have hKC :
        Ne K C := by
      intro hKCeq
      subst K

      have hCDnull :
          Geo.Congruent C D C C :=
        hilbert_congruent_symmetry
          Geo
          C C
          C D
          hKC_KD

      have hEq :
          C = D :=
        bookZero_nullSegment1
          Geo C D C hCDnull

      exact hCD hEq

    rcases
        hilbert_circle_line_second_or_tangent_stage4
          Geo
          K C
          C B
          lineCB
          hCcircle
          hKC
          hCB
          hCline
          hBline
      with
      hSecant | hTangent

    ------------------------------------------------------------------
    -- Secant branch.
    ------------------------------------------------------------------

    · rcases hSecant with
        ⟨E, hEC, hEline, hEcircle⟩

      have hBE :
          Ne B E := by
        intro hBE
        subst E
        exact hBcircle hEcircle

      rcases
          hilbert_forder_IV19_secant_order_split_stage5
            Geo
            C B E
            lineCB
            hCB
            hBE
            hEC.symm
            hCline
            hBline
            hEline
        with
        hRayCBE | hBCE

      --------------------------------------------------------------
      -- E lies on the same ray CB as B.
      --------------------------------------------------------------

      · have hEq :
            E = B :=
          hilbert_forder_IV19_secant_sameRay_stage5
            Geo
            hIV16Same
            K C
            C D A B E
            chord lineCB
            hCD
            hCB
            hCchord
            hDchord
            hCline
            hBline
            hDnotLineCB
            hCcircle
            hDcircle
            hAcircle
            hEcircle
            hSameAB
            hRayCBE
            hAngle

        exact
          False.elim
            (hBE hEq.symm)

      --------------------------------------------------------------
      -- B-C-E: the opposite-ray secant branch.
      --------------------------------------------------------------

      · exact
          False.elim
            (hilbert_forder_IV19_secant_oppositeRay_impossible_stage5
              Geo
              hIV16Opp
              K C
              C D A B E
              chord lineCB
              hCD
              hCchord
              hDchord
              hCline
              hBline
              hDnotLineCB
              hCcircle
              hDcircle
              hAcircle
              hEcircle
              hSameAB
              hBCE
              hAngle)

    ------------------------------------------------------------------
    -- Tangent branch.
    ------------------------------------------------------------------

    · exact
        False.elim
          (hilbert_forder_IV19_tangent_impossible_stage5
            Geo
            hIV18
            K C
            C D A B
            chord lineCB
            hCD
            hCchord
            hDchord
            hCline
            hBline
            hDnotLineCB
            hCcircle
            hDcircle
            hAcircle
            hSameAB
            hTangent
            hAngle)
/- END folded proof support: Crossing_circle_stage6_forder19_complete_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage7_forder20_secant_sameRay_v2.lean -/
/-!
# Forder IV.20 -- stage 7, first secant branch

Forder IV.19 is now complete.  The next task is the supplementary
opposite-side converse IV.20.

This file treats the secant subcase in which the second circle point E
lies on the same ray CB as the prescribed point B.

The argument uses only the already isolated opposite-side half of
Forder IV.16 and Book Zero transport of supplementary angles.

No new axiom is introduced.
-/

/--
Same-ray secant rigidity for Forder IV.20.

Assume:

* C,D,A,E lie on one circle;
* A and B are on opposite sides of chord CD;
* E lies on the same ray CB as B;
* XAD is the supplement of CAD;
* angle XAD ~= angle CBD.

Since B and E are on the same side of CD, A and E are on opposite
sides.  Forder IV.16 says that CAD is supplementary to CED.  Transport
of supplements therefore gives

  angle XAD ~= angle CED.

Together with angle XAD ~= angle CBD we get

  angle CED ~= angle CBD.

Since E and B lie on one ray from C, the already proved secant
uniqueness theorem forces E=B.
-/
theorem hilbert_forder_IV20_secant_sameRay_stage7
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (K R C D A B E X : Geo.Point)
    (chord lineCB : Geo.Line)
    (hCD : Ne C D)
    (hCB : Ne C B)
    (hCchord : H.OnLine C chord)
    (hDchord : H.OnLine D chord)
    (hCline : H.OnLine C lineCB)
    (hBline : H.OnLine B lineCB)
    (hEline : H.OnLine E lineCB)
    (hDnotLineCB : Not (H.OnLine D lineCB))
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hAcircle : HilbertCircle Geo K R A)
    (hEcircle : HilbertCircle Geo K R E)
    (hOppAB : HilbertOppositeSide Geo A B chord)
    (hRayCBE : HilbertSameRay Geo C B E)
    (hSuppA :
      BookZeroSupplement Geo
        X A D
        D C)
    (hAngle :
      Geo.AngleCongruent
        X A D
        C B D) :
    E = B := by

  --------------------------------------------------------------------
  -- B and E are on the same side of chord CD.
  --------------------------------------------------------------------

  have hRayCBB :
      HilbertSameRay Geo C B B :=
    hilbert_sameRay_refl
      Geo C B hCB.symm

  have hSameBE :
      HilbertSameSide Geo B E chord :=
    hilbert_sameRay_points_sameSide
      Geo
      C B B E D
      lineCB chord
      hCline hBline
      hCchord hDchord
      hDnotLineCB
      hRayCBB hRayCBE

  --------------------------------------------------------------------
  -- Hence A and E are on opposite sides of chord CD.
  --------------------------------------------------------------------

  have hOppAE :
      HilbertOppositeSide Geo A E chord :=
    hilbert_oppositeSide_transport_right
      Geo
      A B E
      chord
      hOppAB
      hSameBE

  --------------------------------------------------------------------
  -- Forder IV.16: CAD is congruent to a supplement YED of CED.
  --------------------------------------------------------------------

  rcases
      hIV16Opp
        K R C D A E
        chord
        hCD
        hCchord
        hDchord
        hCcircle
        hDcircle
        hAcircle
        hEcircle
        hOppAE
    with
    ⟨Y, hSuppE, hCAD_YED⟩

  --------------------------------------------------------------------
  -- Re-orient both supplement witnesses so that the base angles are
  -- CAD and YED respectively.
  --------------------------------------------------------------------

  have hCAX :
      Geo.Between C A X :=
    (HilbertOrder.between_incidence
      X A C hSuppA.2).2.2.2.2

  have hSuppARev :
      BookZeroSupplement Geo
        C A D
        D X :=
    ⟨hSuppA.1, hCAX⟩

  have hYEC :
      Geo.Between Y E C :=
    (HilbertOrder.between_incidence
      C E Y hSuppE.2).2.2.2.2

  have hSuppERev :
      BookZeroSupplement Geo
        Y E D
        D C :=
    ⟨hSuppE.1, hYEC⟩

  --------------------------------------------------------------------
  -- Nondegeneracy required by Book Zero supplement transport.
  --------------------------------------------------------------------

  have hCAD :
      Not (PrimCollinear Geo C A D) := by
    intro h
    have hCDA :
        PrimCollinear Geo C D A :=
      PrimCollinearRotate
        Geo C A D h
    exact
      (hilbert_not_collinear_of_off_line
        Geo
        C D A
        chord
        hCD
        hCchord
        hDchord
        hOppAB.1)
        hCDA

  have hCEYdata :=
    HilbertOrder.between_incidence
      C E Y hSuppE.2

  have hCE :
      Ne C E :=
    hCEYdata.1

  have hEY :
      Ne E Y :=
    hCEYdata.2.1

  have hCEYcol :
      PrimCollinear Geo C E Y :=
    hCEYdata.2.2.2.1

  have hYline :
      H.OnLine Y lineCB :=
    hilbert_collinear_on_line
      Geo
      C E Y
      lineCB
      hCE
      hCline
      hEline
      hCEYcol

  have hEY_D :
      Not (PrimCollinear Geo E Y D) :=
    hilbert_not_collinear_of_off_line
      Geo
      E Y D
      lineCB
      hEY
      hEline
      hYline
      hDnotLineCB

  have hYED :
      Not (PrimCollinear Geo Y E D) := by
    intro h
    exact
      hEY_D
        (PrimCollinearSwap
          Geo Y E D h)

  --------------------------------------------------------------------
  -- Supplements of congruent angles are congruent:
  -- DAX ~= DEC, hence XAD ~= CED.
  --------------------------------------------------------------------

  have hDAX_DEC :
      Geo.AngleCongruent
        D A X
        D E C :=
    bookZero_43_supplements
      Geo
      C A D D X
      Y E D D C
      hCAD_YED
      hSuppARev
      hSuppERev
      hCAD
      hYED

  have hXAD_DEC :
      Geo.AngleCongruent
        X A D
        D E C :=
    (Geo.angle_congruent_reverse_first
      D A X
      D E C).mp
      hDAX_DEC

  have hXAD_CED :
      Geo.AngleCongruent
        X A D
        C E D :=
    (Geo.angle_congruent_reverse_second
      X A D
      D E C).mp
      hXAD_DEC

  have hCED_XAD :
      Geo.AngleCongruent
        C E D
        X A D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X A D
      C E D
      hXAD_CED

  have hCED_CBD :
      Geo.AngleCongruent
        C E D
        C B D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C E D
      X A D
      C B D
      hCED_XAD
      hAngle

  --------------------------------------------------------------------
  -- Same secant ray + equal angles -> E=B.
  --------------------------------------------------------------------

  have hEoff :
      Not (H.OnLine E chord) :=
    hSameBE.2.1

  have hCDE :
      Not (PrimCollinear Geo C D E) :=
    hilbert_not_collinear_of_off_line
      Geo
      C D E
      chord
      hCD
      hCchord
      hDchord
      hEoff

  have hCED :
      Not (PrimCollinear Geo C E D) := by
    intro h
    exact
      hCDE
        (PrimCollinearRotate
          Geo C E D h)

  have hRayCEB :
      HilbertSameRay Geo C E B :=
    hilbert_sameRay_symm
      Geo C B E hRayCBE

  exact
    hilbert_equal_angles_same_secant_unique_stage5
      Geo
      C E B D
      hCED
      hRayCEB
      hCED_CBD
/- END folded proof support: Crossing_circle_stage7_forder20_secant_sameRay_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage7_forder20_secant_oppositeRay_v1.lean -/
/-!
# Forder IV.20 -- stage 7, opposite-ray secant branch

The same-ray secant branch was closed in
`Crossing_circle_stage7_forder20_secant_sameRay_v2`.

This file first proves the full plane-separation parity fact needed
below: if Q and R are both on the opposite side of a line from P,
then Q and R are on the same side.  Unlike an older local helper, the
proof also handles the collinear case.

It then closes the remaining secant branch B-C-E in Forder IV.20.

No new axiom is introduced.
-/

------------------------------------------------------------------------
-- 1. Plane-separation parity, including the collinear case.
------------------------------------------------------------------------

/--
If Q and R are both opposite P across l, then Q and R are on the same
side of l.

For a noncollinear triangle, a line cannot meet all three open sides.
For a collinear triple, the two crossing witnesses belonging to the
two adjacent intervals are distinct; otherwise two endpoints that are
separated by the middle point would lie on one ray from that middle
point.  Two distinct common points would then force the carrier to
equal l, contradicting that P is off l.
-/
theorem hilbert_two_oppositeSides_sameSide_full_stage7
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H]
    (P Q R : Geo.Point)
    (l : Geo.Line)
    (hPQ : HilbertOppositeSide Geo P Q l)
    (hPR : HilbertOppositeSide Geo P R l) :
    HilbertSameSide Geo Q R l := by

  by_contra hNotSame

  have hQR :
      HilbertOppositeSide Geo Q R l :=
    hilbert_oppositeSide_of_not_sameSide
      Geo
      Q R
      l
      hPQ.2.1
      hPR.2.1
      hNotSame

  rcases hPQ.2.2 with
    ⟨X, hPXQ, hXl⟩

  rcases hPR.2.2 with
    ⟨Y, hPYR, hYl⟩

  rcases hQR.2.2 with
    ⟨Z, hQZR, hZl⟩

  have hPQne :
      Ne P Q :=
    (HilbertOrder.between_incidence
      P X Q hPXQ).2.2.1

  have hPRne :
      Ne P R :=
    (HilbertOrder.between_incidence
      P Y R hPYR).2.2.1

  have hQRne :
      Ne Q R :=
    (HilbertOrder.between_incidence
      Q Z R hQZR).2.2.1

  by_cases hPQR :
      PrimCollinear Geo P Q R

  --------------------------------------------------------------------
  -- Collinear case.
  --------------------------------------------------------------------

  · rcases hPQR with
      ⟨carrier, hPcar, hQcar, hRcar⟩

    have hCol :
        PrimCollinear Geo P Q R :=
      ⟨carrier, hPcar, hQcar, hRcar⟩

    rcases
        hilbert_between_trichotomy
          Geo
          P Q R
          hPQne
          hQRne
          hPRne
          hCol
      with
      hPQRord | hQPRord | hPRQord

    --------------------------------------------------------------
    -- P-Q-R.  Use the crossing witnesses on PQ and QR.
    --------------------------------------------------------------

    · have hXcar :
          H.OnLine X carrier :=
        hilbert_between_on_line
          Geo P X Q carrier
          hPcar hQcar hPXQ

      have hZcar :
          H.OnLine Z carrier :=
        hilbert_between_on_line
          Geo Q Z R carrier
          hQcar hRcar hQZR

      have hXZ :
          Ne X Z := by
        intro hXZeq
        subst Z

        have hQXP :
            Geo.Between Q X P :=
          (HilbertOrder.between_incidence
            P X Q hPXQ).2.2.2.2

        have hRayQXP :
            HilbertSameRay Geo Q X P :=
          hilbert_sameRay_of_between
            Geo Q X P hQXP

        have hRayQXR :
            HilbertSameRay Geo Q X R :=
          hilbert_sameRay_of_between
            Geo Q X R hQZR

        have hRayQPR :
            HilbertSameRay Geo Q P R :=
          hilbert_sameRay_of_common
            Geo Q X P R
            hRayQXP hRayQXR

        exact
          (hilbert_not_sameRay_of_between_origin
            Geo P Q R hPQRord)
            hRayQPR

      have hEq :
          carrier = l :=
        HilbertPlaneIncidence.line_unique
          X Z hXZ
          carrier l
          hXcar hZcar
          hXl hZl

      have hPl :
          H.OnLine P l := by
        rw [← hEq]
        exact hPcar

      exact hPQ.1 hPl

    --------------------------------------------------------------
    -- Q-P-R.  Use the crossing witnesses on PQ and PR.
    --------------------------------------------------------------

    · have hXcar :
          H.OnLine X carrier :=
        hilbert_between_on_line
          Geo P X Q carrier
          hPcar hQcar hPXQ

      have hYcar :
          H.OnLine Y carrier :=
        hilbert_between_on_line
          Geo P Y R carrier
          hPcar hRcar hPYR

      have hXY :
          Ne X Y := by
        intro hXYeq
        subst Y

        have hRayPXQ :
            HilbertSameRay Geo P X Q :=
          hilbert_sameRay_of_between
            Geo P X Q hPXQ

        have hRayPXR :
            HilbertSameRay Geo P X R :=
          hilbert_sameRay_of_between
            Geo P X R hPYR

        have hRayPQR :
            HilbertSameRay Geo P Q R :=
          hilbert_sameRay_of_common
            Geo P X Q R
            hRayPXQ hRayPXR

        exact
          (hilbert_not_sameRay_of_between_origin
            Geo Q P R hQPRord)
            hRayPQR

      have hEq :
          carrier = l :=
        HilbertPlaneIncidence.line_unique
          X Y hXY
          carrier l
          hXcar hYcar
          hXl hYl

      have hPl :
          H.OnLine P l := by
        rw [← hEq]
        exact hPcar

      exact hPQ.1 hPl

    --------------------------------------------------------------
    -- P-R-Q.  Use the crossing witnesses on PR and QR.
    --------------------------------------------------------------

    · have hYcar :
          H.OnLine Y carrier :=
        hilbert_between_on_line
          Geo P Y R carrier
          hPcar hRcar hPYR

      have hZcar :
          H.OnLine Z carrier :=
        hilbert_between_on_line
          Geo Q Z R carrier
          hQcar hRcar hQZR

      have hYZ :
          Ne Y Z := by
        intro hYZeq
        subst Z

        have hRYP :
            Geo.Between R Y P :=
          (HilbertOrder.between_incidence
            P Y R hPYR).2.2.2.2

        have hRYQ :
            Geo.Between R Y Q :=
          (HilbertOrder.between_incidence
            Q Y R hQZR).2.2.2.2

        have hRayRYP :
            HilbertSameRay Geo R Y P :=
          hilbert_sameRay_of_between
            Geo R Y P hRYP

        have hRayRYQ :
            HilbertSameRay Geo R Y Q :=
          hilbert_sameRay_of_between
            Geo R Y Q hRYQ

        have hRayRPQ :
            HilbertSameRay Geo R P Q :=
          hilbert_sameRay_of_common
            Geo R Y P Q
            hRayRYP hRayRYQ

        exact
          (hilbert_not_sameRay_of_between_origin
            Geo P R Q hPRQord)
            hRayRPQ

      have hEq :
          carrier = l :=
        HilbertPlaneIncidence.line_unique
          Y Z hYZ
          carrier l
          hYcar hZcar
          hYl hZl

      have hPl :
          H.OnLine P l := by
        rw [← hEq]
        exact hPcar

      exact hPQ.1 hPl

  --------------------------------------------------------------------
  -- Noncollinear case: a line cannot cross all three open sides.
  --------------------------------------------------------------------

  · have hNoQR :
        Not (HilbertSegmentMeetsLine Geo Q R l) :=
      hilbert_line_avoids_third_triangle_side
        Geo
        P Q R
        X Y
        l
        hPQR
        hPXQ
        hPYR
        hXl
        hYl

    exact
      hNoQR
        ⟨Z, hQZR, hZl⟩


------------------------------------------------------------------------
-- 2. Forder IV.20: the B-C-E secant branch is impossible.
------------------------------------------------------------------------

/--
The opposite-ray secant alternative B-C-E in Forder IV.20 is
impossible.

B and E are opposite across chord CD because their open segment meets
the chord at C.  Since A and B are also opposite, plane-separation
parity puts A and E on the same side of CD.  Forder IV.16 then gives

  angle CAD ~= angle CED.

Transporting the supplements of these congruent angles gives an
exterior angle DEY at E congruent to XAD.  The IV.20 hypothesis makes
DEY congruent to CBD, and B-C-E identifies CBD with EBD.  Thus an
exterior angle of triangle EBD is congruent to the remote interior
angle EBD, contradicting Hilbert's exterior-angle theorem.
-/
theorem hilbert_forder_IV20_secant_oppositeRay_impossible_stage7
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (K R C D A B E X : Geo.Point)
    (chord lineCB : Geo.Line)
    (hCD : Ne C D)
    (hCchord : H.OnLine C chord)
    (hDchord : H.OnLine D chord)
    (hCline : H.OnLine C lineCB)
    (hBline : H.OnLine B lineCB)
    (hEline : H.OnLine E lineCB)
    (hDnotLineCB : Not (H.OnLine D lineCB))
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hAcircle : HilbertCircle Geo K R A)
    (hEcircle : HilbertCircle Geo K R E)
    (hOppAB : HilbertOppositeSide Geo A B chord)
    (hBCE : Geo.Between B C E)
    (hSuppA :
      BookZeroSupplement Geo
        X A D
        D C)
    (hAngle :
      Geo.AngleCongruent
        X A D
        C B D) :
    False := by

  have hBCEdata :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBC :
      Ne B C :=
    hBCEdata.1

  have hCE :
      Ne C E :=
    hBCEdata.2.1

  have hBE :
      Ne B E :=
    hBCEdata.2.2.1

  --------------------------------------------------------------------
  -- E is off chord CD.
  --------------------------------------------------------------------

  have hEoff :
      Not (H.OnLine E chord) := by
    intro hEchord

    have hEq :
        chord = lineCB :=
      HilbertPlaneIncidence.line_unique
        C E hCE
        chord lineCB
        hCchord hEchord
        hCline hEline

    have hDline :
        H.OnLine D lineCB := by
      rw [← hEq]
      exact hDchord

    exact hDnotLineCB hDline

  --------------------------------------------------------------------
  -- B and E are opposite across CD, with crossing point C.
  --------------------------------------------------------------------

  have hOppBE :
      HilbertOppositeSide Geo B E chord :=
    ⟨hOppAB.2.1,
      hEoff,
      ⟨C, hBCE, hCchord⟩⟩

  have hOppBA :
      HilbertOppositeSide Geo B A chord :=
    hilbert_oppositeSide_symm
      Geo A B chord hOppAB

  have hSameAE :
      HilbertSameSide Geo A E chord :=
    hilbert_two_oppositeSides_sameSide_full_stage7
      Geo
      B A E
      chord
      hOppBA
      hOppBE

  --------------------------------------------------------------------
  -- Forder IV.16 same-side half: CAD ~= CED.
  --------------------------------------------------------------------

  have hCAD_CED :
      Geo.AngleCongruent
        C A D
        C E D :=
    hIV16Same
      K R C D A E
      chord
      hCD
      hCchord
      hDchord
      hCcircle
      hDcircle
      hAcircle
      hEcircle
      hSameAE

  --------------------------------------------------------------------
  -- Construct the supplement of CED by extending CE through E.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        C E hCE
    with
    ⟨Y, hCEY⟩

  have hEY :
      Ne E Y :=
    (HilbertOrder.between_incidence
      C E Y hCEY).2.1

  have hSuppE :
      BookZeroSupplement Geo
        C E D
        D Y :=
    ⟨hilbert_sameRay_refl
        Geo E D
        (by
          intro hDE
          subst D
          exact hDnotLineCB hEline),
      hCEY⟩

  --------------------------------------------------------------------
  -- Re-orient the given supplement so that CAD is the base angle.
  --------------------------------------------------------------------

  have hCAX :
      Geo.Between C A X :=
    (HilbertOrder.between_incidence
      X A C hSuppA.2).2.2.2.2

  have hSuppARev :
      BookZeroSupplement Geo
        C A D
        D X :=
    ⟨hSuppA.1, hCAX⟩

  --------------------------------------------------------------------
  -- Proper-angle hypotheses for supplement transport.
  --------------------------------------------------------------------

  have hCAD :
      Not (PrimCollinear Geo C A D) := by
    intro h
    have hCDA :
        PrimCollinear Geo C D A :=
      PrimCollinearRotate
        Geo C A D h
    exact
      (hilbert_not_collinear_of_off_line
        Geo
        C D A
        chord
        hCD
        hCchord
        hDchord
        hOppAB.1)
        hCDA

  have hCED :
      Not (PrimCollinear Geo C E D) := by
    intro h
    have hCDE :
        PrimCollinear Geo C D E :=
      PrimCollinearRotate
        Geo C E D h
    exact
      (hilbert_not_collinear_of_off_line
        Geo
        C D E
        chord
        hCD
        hCchord
        hDchord
        hEoff)
        hCDE

  --------------------------------------------------------------------
  -- Supplements of CAD ~= CED:
  -- DAX ~= DEY, hence XAD ~= DEY.
  --------------------------------------------------------------------

  have hDAX_DEY :
      Geo.AngleCongruent
        D A X
        D E Y :=
    bookZero_43_supplements
      Geo
      C A D D X
      C E D D Y
      hCAD_CED
      hSuppARev
      hSuppE
      hCAD
      hCED

  have hXAD_DEY :
      Geo.AngleCongruent
        X A D
        D E Y :=
    (Geo.angle_congruent_reverse_first
      D A X
      D E Y).mp
      hDAX_DEY

  have hDEY_XAD :
      Geo.AngleCongruent
        D E Y
        X A D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X A D
      D E Y
      hXAD_DEY

  have hDEY_CBD :
      Geo.AngleCongruent
        D E Y
        C B D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D E Y
      X A D
      C B D
      hDEY_XAD
      hAngle

  --------------------------------------------------------------------
  -- Because B-C-E, rays BC and BE coincide.
  --------------------------------------------------------------------

  have hRayBCE :
      HilbertSameRay Geo B C E :=
    hilbert_sameRay_of_between
      Geo B C E hBCE

  have hAtB :
      Geo.Angle C B D =
      Geo.Angle E B D :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      B C E D
      hRayBCE

  have hDEY_EBD :
      Geo.AngleCongruent
        D E Y
        E B D := by
    unfold Geometry.Geo.AngleCongruent
      at hDEY_CBD ⊢
    rw [← hAtB]
    exact hDEY_CBD

  --------------------------------------------------------------------
  -- DEY is an exterior angle of triangle EBD, since B-E-Y.
  --------------------------------------------------------------------

  have hBEY :
      Geo.Between B E Y :=
    (hilbert_between_outer_trans
      Geo
      B C E Y
      hBCE hCEY).1

  have hEBD :
      Not (PrimCollinear Geo E B D) :=
    hilbert_not_collinear_of_off_line
      Geo
      E B D
      lineCB
      hBE.symm
      hEline
      hBline
      hDnotLineCB

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      E B D Y
      hEBD
      hBEY)
      hDEY_EBD
/- END folded proof support: Crossing_circle_stage7_forder20_secant_oppositeRay_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage7_forder20_tangent_v1.lean -/
/-!
# Forder IV.20 -- stage 7, tangent branch

Both secant branches of Forder IV.20 are now closed.

This file eliminates the remaining tangent alternative.  The proof is
source-faithful:

* Forder IV.18 gives the tangent-chord angle;
* Book Zero transports supplementary angles;
* Hilbert's exterior-angle theorem gives the contradiction.

No numerical angle measure and no new axiom are introduced.
-/

/--
The tangent alternative in Forder IV.20 is impossible.

Let line CB be tangent at C to the circumcircle through C,D,A, while
A and B lie on opposite sides of chord CD.  Forder IV.18 gives

  angle DCB ~= angle DAC.

The IV.20 data say that XAD is supplementary to DAC and

  angle XAD ~= angle CBD.

Extend CB through B to Z.  Then CBD and DBZ are supplementary.
Book Zero transport therefore gives

  angle DAC ~= angle DBZ.

Hence DCB ~= DBZ.  Since DCB is the same unoriented angle as BCD,
the exterior angle DBZ of triangle BCD is congruent to the remote
interior angle BCD, contradicting Hilbert's exterior-angle theorem.
-/
theorem hilbert_forder_IV20_tangent_impossible_stage7
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo))
    (K R C D A B X : Geo.Point)
    (chord lineCB : Geo.Line)
    (hCD : Ne C D)
    (hCchord : H.OnLine C chord)
    (hDchord : H.OnLine D chord)
    (hCline : H.OnLine C lineCB)
    (hBline : H.OnLine B lineCB)
    (hDnotLineCB : Not (H.OnLine D lineCB))
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hAcircle : HilbertCircle Geo K R A)
    (hOppAB : HilbertOppositeSide Geo A B chord)
    (hTan :
      HilbertCircleTangentAtStage4
        (Geo := Geo) K C lineCB)
    (hSuppA :
      BookZeroSupplement Geo
        X A D
        D C)
    (hAngle :
      Geo.AngleCongruent
        X A D
        C B D) :
    False := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy on the tangent line.
  --------------------------------------------------------------------

  have hBoff :
      Not (H.OnLine B chord) :=
    hOppAB.2.1

  have hBC :
      Ne B C := by
    intro hBCeq
    subst B
    exact hBoff hCchord

  have hCB :
      Ne C B :=
    hBC.symm

  --------------------------------------------------------------------
  -- Forder IV.18 at the tangent point C:
  -- angle DCB ~= angle DAC.
  --------------------------------------------------------------------

  have hOppBA :
      HilbertOppositeSide Geo B A chord :=
    hilbert_oppositeSide_symm
      Geo A B chord hOppAB

  have hDCB_DAC :
      Geo.AngleCongruent
        D C B
        D A C :=
    hIV18
      K R D C A B
      chord lineCB
      hCD.symm
      hDchord
      hCchord
      hCline
      hBline
      hBC
      hDcircle
      hCcircle
      hAcircle
      hTan
      hOppBA

  --------------------------------------------------------------------
  -- Extend CB through B: C-B-Z.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        C B hCB
    with
    ⟨Z, hCBZ⟩

  have hBZ :
      Ne B Z :=
    (HilbertOrder.between_incidence
      C B Z hCBZ).2.1

  have hSuppB :
      BookZeroSupplement Geo
        C B D
        D Z :=
    ⟨hilbert_sameRay_refl
        Geo B D
        (by
          intro hDB
          subst D
          exact hDnotLineCB hBline),
      hCBZ⟩

  --------------------------------------------------------------------
  -- XAD is a genuine angle.
  --------------------------------------------------------------------

  have hXACdata :=
    HilbertOrder.between_incidence
      X A C hSuppA.2

  have hXA :
      Ne X A :=
    hXACdata.1

  have hAC :
      Ne A C :=
    hXACdata.2.1

  rcases hXACdata.2.2.2.1 with
    ⟨lineAC, hXlineAC, hAlineAC, hClineAC⟩

  have hDoffAC :
      Not (H.OnLine D lineAC) := by
    intro hDlineAC

    have hEq :
        lineAC = chord :=
      HilbertPlaneIncidence.line_unique
        C D hCD
        lineAC chord
        hClineAC hDlineAC
        hCchord hDchord

    have hAchord' :
        H.OnLine A chord := by
      rw [← hEq]
      exact hAlineAC

    exact hOppAB.1 hAchord'

  have hXAD :
      Not (PrimCollinear Geo X A D) :=
    hilbert_not_collinear_of_off_line
      Geo
      X A D
      lineAC
      hXA
      hXlineAC
      hAlineAC
      hDoffAC

  --------------------------------------------------------------------
  -- CBD is a genuine angle.
  --------------------------------------------------------------------

  have hCBD :
      Not (PrimCollinear Geo C B D) :=
    hilbert_not_collinear_of_off_line
      Geo
      C B D
      lineCB
      hCB
      hCline
      hBline
      hDnotLineCB

  --------------------------------------------------------------------
  -- Supplements of congruent angles:
  -- DAC ~= DBZ.
  --------------------------------------------------------------------

  have hDAC_DBZ :
      Geo.AngleCongruent
        D A C
        D B Z :=
    bookZero_43_supplements
      Geo
      X A D D C
      C B D D Z
      hAngle
      hSuppA
      hSuppB
      hXAD
      hCBD

  have hDCB_DBZ :
      Geo.AngleCongruent
        D C B
        D B Z :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D C B
      D A C
      D B Z
      hDCB_DAC
      hDAC_DBZ

  --------------------------------------------------------------------
  -- Reorient DCB as BCD and reverse the congruence.
  --------------------------------------------------------------------

  have hDBZ_DCB :
      Geo.AngleCongruent
        D B Z
        D C B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D C B
      D B Z
      hDCB_DBZ

  have hDBZ_BCD :
      Geo.AngleCongruent
        D B Z
        B C D := by
    have hAtC :
        Geo.Angle D C B =
        Geo.Angle B C D :=
      Geo.angle_swap D C B
    unfold Geometry.Geo.AngleCongruent
      at hDBZ_DCB ⊢
    rw [← hAtC]
    exact hDBZ_DCB

  --------------------------------------------------------------------
  -- DBZ is an exterior angle of triangle BCD.
  --------------------------------------------------------------------

  have hBCD :
      Not (PrimCollinear Geo B C D) := by
    intro h
    exact
      hCBD
        (PrimCollinearSwap
          Geo B C D h)

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      B C D Z
      hBCD
      hCBZ)
      hDBZ_BCD
/- END folded proof support: Crossing_circle_stage7_forder20_tangent_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage8_forder20_complete_v1.lean -/
/-!
# Forder IV.20 -- stage 8, complete converse

Stage 7 closed all local alternatives needed for Forder IV.20:

* same-ray secant;
* opposite-ray secant;
* tangent.

This file only composes those results with the stage-4
secant/tangent dichotomy.

No new axiom is introduced.
-/

/--
Complete Forder IV.20.

If A and B lie on opposite sides of chord CD, XAD is a supplement of
CAD, and

  angle XAD ~= angle CBD,

then A,C,D,B are concyclic.

The proof constructs the circumcircle through C,D,A.  If B is already
on the circle, we are done.  Otherwise apply the stage-4
secant/tangent dichotomy to the line CB.

The secant point E is split by the stage-5 order theorem into:

* E on the same ray CB as B -- stage 7 forces E=B;
* B-C-E -- stage 7 gives a contradiction.

The tangent alternative is also impossible by the stage-7 tangent
lemma.
-/
theorem hilbert_forder_IV20_circle_converse_stage8
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo)) :
    HilbertForderIV20CircleConverse
      (Geo := Geo) := by

  intro C D A B X chord hCD hCchord hDchord hOppAB hSuppA hAngle

  --------------------------------------------------------------------
  -- A is off chord CD, hence C,D,A form a genuine triangle.
  --------------------------------------------------------------------

  have hAoff :
      Not (H.OnLine A chord) :=
    hOppAB.1

  have hBoff :
      Not (H.OnLine B chord) :=
    hOppAB.2.1

  have hCDA :
      Not (PrimCollinear Geo C D A) :=
    hilbert_not_collinear_of_off_line
      Geo
      C D A
      chord
      hCD
      hCchord
      hDchord
      hAoff

  --------------------------------------------------------------------
  -- Circumcircle through C,D,A, with reference radius KC.
  --------------------------------------------------------------------

  rcases
      hilbert_triangle_circumcenter_exists_XI
        Geo
        C D A
        hCDA
    with
    ⟨K, hKC_KD, hKC_KA⟩

  have hCcircle :
      HilbertCircle Geo K C C :=
    hilbert_circle_reference_mem
      Geo K C

  have hDcircle :
      HilbertCircle Geo K C D := by
    unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K C
        K D
        hKC_KD

  have hAcircle :
      HilbertCircle Geo K C A := by
    unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K C
        K A
        hKC_KA

  --------------------------------------------------------------------
  -- If B is already on the circumcircle, we are done.
  --------------------------------------------------------------------

  by_cases hBcircle :
      HilbertCircle Geo K C B

  · exact
      hilbert_concyclic4_of_circle
        Geo
        K C
        A C D B
        hAcircle
        hCcircle
        hDcircle
        hBcircle

  --------------------------------------------------------------------
  -- Otherwise analyze line CB through the circle point C.
  --------------------------------------------------------------------

  · have hCB :
        Ne C B := by
      intro hCB
      subst B
      exact hBoff hCchord

    rcases
        HilbertPlaneIncidence.line_through
          C B hCB
      with
      ⟨lineCB, hCline, hBline⟩

    have hCDB :
        Not (PrimCollinear Geo C D B) :=
      hilbert_not_collinear_of_off_line
        Geo
        C D B
        chord
        hCD
        hCchord
        hDchord
        hBoff

    have hDnotLineCB :
        Not (H.OnLine D lineCB) := by
      intro hDline
      exact
        hCDB
          ⟨lineCB,
            hCline,
            hDline,
            hBline⟩

    ------------------------------------------------------------------
    -- The center differs from C.
    ------------------------------------------------------------------

    have hKC :
        Ne K C := by
      intro hKCeq
      subst K

      have hCDnull :
          Geo.Congruent C D C C :=
        hilbert_congruent_symmetry
          Geo
          C C
          C D
          hKC_KD

      have hEq :
          C = D :=
        bookZero_nullSegment1
          Geo C D C hCDnull

      exact hCD hEq

    rcases
        hilbert_circle_line_second_or_tangent_stage4
          Geo
          K C
          C B
          lineCB
          hCcircle
          hKC
          hCB
          hCline
          hBline
      with
      hSecant | hTangent

    ------------------------------------------------------------------
    -- Secant branch.
    ------------------------------------------------------------------

    · rcases hSecant with
        ⟨E, hEC, hEline, hEcircle⟩

      have hBE :
          Ne B E := by
        intro hBE
        subst E
        exact hBcircle hEcircle

      rcases
          hilbert_forder_IV19_secant_order_split_stage5
            Geo
            C B E
            lineCB
            hCB
            hBE
            hEC.symm
            hCline
            hBline
            hEline
        with
        hRayCBE | hBCE

      --------------------------------------------------------------
      -- E lies on the same ray CB as B.
      --------------------------------------------------------------

      · have hEq :
            E = B :=
          hilbert_forder_IV20_secant_sameRay_stage7
            Geo
            hIV16Opp
            K C
            C D A B E X
            chord lineCB
            hCD
            hCB
            hCchord
            hDchord
            hCline
            hBline
            hEline
            hDnotLineCB
            hCcircle
            hDcircle
            hAcircle
            hEcircle
            hOppAB
            hRayCBE
            hSuppA
            hAngle

        exact
          False.elim
            (hBE hEq.symm)

      --------------------------------------------------------------
      -- B-C-E: opposite-ray secant branch.
      --------------------------------------------------------------

      · exact
          False.elim
            (hilbert_forder_IV20_secant_oppositeRay_impossible_stage7
              Geo
              hIV16Same
              K C
              C D A B E X
              chord lineCB
              hCD
              hCchord
              hDchord
              hCline
              hBline
              hEline
              hDnotLineCB
              hCcircle
              hDcircle
              hAcircle
              hEcircle
              hOppAB
              hBCE
              hSuppA
              hAngle)

    ------------------------------------------------------------------
    -- Tangent branch.
    ------------------------------------------------------------------

    · exact
        False.elim
          (hilbert_forder_IV20_tangent_impossible_stage7
            Geo
            hIV18
            K C
            C D A B X
            chord lineCB
            hCD
            hCchord
            hDchord
            hCline
            hBline
            hDnotLineCB
            hCcircle
            hDcircle
            hAcircle
            hOppAB
            hTangent
            hSuppA
            hAngle)
/- END folded proof support: Crossing_circle_stage8_forder20_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage9_integrated_concyclic_v1.lean -/
/-!
# Crossing circle -- stage 9

Forder IV.19 and IV.20 are now proved from the lower circle lemmas.

This file removes them as external inputs from the crossing-chords
concyclicity theorem.  The only remaining circle-theoretic inputs are:

* Forder IV.16, same-side half;
* Forder IV.16, opposite-side half;
* Forder IV.18, tangent-chord theorem.

No new axiom is introduced.
-/

/--
Crossing-rays concyclicity with IV.19 and IV.20 discharged internally.

The theorem is the old stage-3 crossing result, but the two converse
circle theorems are now supplied by their actual stage-6 and stage-8
proofs.
-/
theorem hilbert_crossing_chords_concyclic_stage9
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo))
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    HilbertConcyclic4 Geo A C D B := by

  have hIV19 :
      HilbertForderIV19CircleConverse
        (Geo := Geo) :=
    hilbert_forder_IV19_circle_converse_stage6
      Geo
      hIV16Same
      hIV16Opp
      hIV18

  have hIV20 :
      HilbertForderIV20CircleConverse
        (Geo := Geo) :=
    hilbert_forder_IV20_circle_converse_stage8
      Geo
      hIV16Same
      hIV16Opp
      hIV18

  exact
    hilbert_crossing_chords_concyclic_of_forder_stage3
      Geo
      hIV19
      hIV20
      O A C B D
      hAOB
      hRayAC
      hRayBD
      hAngle
/- END folded proof support: Crossing_circle_stage9_integrated_concyclic_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage10_forward_angle_nondegenerate_v2.lean -/
/-!
# Crossing circle -- stage 10, forward circle-angle theorem

Stage 9 gives the required concyclicity.  This file proves the forward
angle consequence in the nondegenerate crossing configuration.

The proof applies Forder IV.16 to chord BC.  The four ray-order cases
have the exact parity expected geometrically:

* outer/outer and inner/inner: D and A are on opposite sides of BC;
* the two mixed cases: D and A are on the same side of BC.

Book Zero supplement transport converts the IV.16 angle statement to
the requested rays through O.

No new axiom is introduced.
-/

/--
Nondegenerate forward crossing-angle theorem.

Assume A != C and B != D.  If A,C,D,B are concyclic in the crossing
configuration, then

  angle ODC ~= angle OAB.

Only the two halves of Forder IV.16 are used.
-/
theorem hilbert_crossing_chords_angle_nondegenerate_stage10
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : Ne A C)
    (hBD : Ne B D)
    (hCyclic :
      HilbertConcyclic4 Geo A C D B) :
    Geo.AngleCongruent
      O D C
      O A B := by

  --------------------------------------------------------------------
  -- Put the cyclic quadruple on one explicit circle.
  --------------------------------------------------------------------

  rcases
      hilbert_concyclic4_circle
        Geo A C D B hCyclic
    with
    ⟨K, hAcircle, hCcircle, hDcircle, hBcircle⟩

  --------------------------------------------------------------------
  -- Nondegenerate crossing data and the two strict ray orders.
  --------------------------------------------------------------------

  rcases
      hilbert_crossing_nondegenerate_data_stage1
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨_hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  have hOA :
      Ne O A :=
    hRayAC.1.symm

  have hOB :
      Ne O B :=
    hRayBD.1.symm

  have hAB :
      Ne A B := by
    intro hEq
    subst B
    rcases
        HilbertPlaneIncidence.line_through
          A O hOA.symm
      with
      ⟨l, hAl, hOl⟩
    exact
      hAOB
        ⟨l, hAl, hOl, hAl⟩

  have hBC :
      Ne B C := by
    intro hEq
    subst C
    rcases
        HilbertPlaneIncidence.line_through
          O B hOB
      with
      ⟨l, hOl, hBl⟩
    exact
      hOBC
        ⟨l, hOl, hBl, hBl⟩

  have hCB :
      Ne C B :=
    hBC.symm

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAC.1

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      Ne C D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hDOA :
      Not (PrimCollinear Geo D O A) :=
    hilbert_noncollinear_of_sameRays
      Geo
      B O A
      D A
      hBOA
      hRayBD
      hRayAA

  --------------------------------------------------------------------
  -- The four strict order cases.
  --------------------------------------------------------------------

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- I. O-A-C.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    ------------------------------------------------------------------
    -- I.a O-A-C and O-B-D.
    --
    -- For chord BC, D and A are on opposite sides.
    -- IV.16 says BDC is congruent to a supplement of BAC.
    -- OAB is also a supplement of CAB, while ODC = BDC.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_inner_outer_oppositeSide_chord_stage2
            Geo
            O D B A C
            hDOA
            hOBD
            hOAC
        with
        ⟨chordBC, hBchord, hCchord, hOppDA⟩

      rcases
          hIV16Opp
            K A
            B C D A
            chordBC
            hBC
            hBchord
            hCchord
            hBcircle
            hCcircle
            hDcircle
            hAcircle
            hOppDA
        with
        ⟨X, hSuppX, hBDC_XAC⟩

      have hCAO :
          Geo.Between C A O :=
        (HilbertOrder.between_incidence
          O A C hOAC).2.2.2.2

      have hSuppO :
          BookZeroSupplement Geo
            C A B
            B O :=
        ⟨hilbert_sameRay_refl
            Geo A B hAB.symm,
          hCAO⟩

      have hBCA :
          Not (PrimCollinear Geo B C A) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C A
          chordBC
          hBC
          hBchord
          hCchord
          hOppDA.2.1

      have hBAC :
          Not (PrimCollinear Geo B A C) := by
        intro h
        exact
          hBCA
            (PrimCollinearRotate
              Geo B A C h)

      have hCAB :
          Not (PrimCollinear Geo C A B) := by
        intro h
        exact
          hBCA
            (PrimCollinearCycle
              Geo A B C
              (PrimCollinearCycle
                Geo C A B h))

      have hBAC_CAB :
          Geo.AngleCongruent
            B A C
            C A B := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        unfold Geometry.Geo.AngleCongruent
        rw [← hAtA]
        exact
          Geometry.Geo.angle_congruent_reflexive
            Geo B A C

      have hCAX_BAO :
          Geo.AngleCongruent
            C A X
            B A O :=
        bookZero_43_supplements
          Geo
          B A C C X
          C A B B O
          hBAC_CAB
          hSuppX
          hSuppO
          hBAC
          hCAB

      have hBDC_CAX :
          Geo.AngleCongruent
            B D C
            C A X := by
        have hAtA :
            Geo.Angle X A C =
            Geo.Angle C A X :=
          Geo.angle_swap X A C
        unfold Geometry.Geo.AngleCongruent
          at hBDC_XAC ⊢
        rw [← hAtA]
        exact hBDC_XAC

      have hBDC_BAO :
          Geo.AngleCongruent
            B D C
            B A O :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          B D C
          C A X
          B A O
          hBDC_CAX
          hCAX_BAO

      have hBDC_OAB :
          Geo.AngleCongruent
            B D C
            O A B := by
        have hAtA :
            Geo.Angle B A O =
            Geo.Angle O A B :=
          Geo.angle_swap B A O
        unfold Geometry.Geo.AngleCongruent
          at hBDC_BAO ⊢
        rw [← hAtA]
        exact hBDC_BAO

      have hDBO :
          Geo.Between D B O :=
        (HilbertOrder.between_incidence
          O B D hOBD).2.2.2.2

      have hRayDBO :
          HilbertSameRay Geo D B O :=
        hilbert_sameRay_of_between
          Geo D B O hDBO

      have hRayDOB :
          HilbertSameRay Geo D O B :=
        hilbert_sameRay_symm
          Geo D B O hRayDBO

      have hAtD :
          Geo.Angle O D C =
          Geo.Angle B D C :=
        hilbert_angle_eq_of_sameRay_first
          Geo D O B C hRayDOB

      unfold Geometry.Geo.AngleCongruent
        at hBDC_OAB ⊢
      rw [hAtD]
      exact hBDC_OAB

    ------------------------------------------------------------------
    -- I.b O-A-C and O-D-B.
    --
    -- Both requested angles are supplements of the equal same-segment
    -- angles supplied by IV.16.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_outer_outer_sameSide_chord_stage2
            Geo
            O D B A C
            hDOA
            hODB
            hOAC
        with
        ⟨chordBC, hBchord, hCchord, hSameDA⟩

      have hBDC_BAC :
          Geo.AngleCongruent
            B D C
            B A C :=
        hIV16Same
          K A
          B C D A
          chordBC
          hBC
          hBchord
          hCchord
          hBcircle
          hCcircle
          hDcircle
          hAcircle
          hSameDA

      have hBDC_CAB :
          Geo.AngleCongruent
            B D C
            C A B := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        unfold Geometry.Geo.AngleCongruent
          at hBDC_BAC ⊢
        rw [← hAtA]
        exact hBDC_BAC

      have hBDO :
          Geo.Between B D O :=
        (HilbertOrder.between_incidence
          O D B hODB).2.2.2.2

      have hCAO :
          Geo.Between C A O :=
        (HilbertOrder.between_incidence
          O A C hOAC).2.2.2.2

      have hSuppD :
          BookZeroSupplement Geo
            B D C
            C O :=
        ⟨hilbert_sameRay_refl
            Geo D C hCD,
          hBDO⟩

      have hSuppA :
          BookZeroSupplement Geo
            C A B
            B O :=
        ⟨hilbert_sameRay_refl
            Geo A B hAB.symm,
          hCAO⟩

      have hDoff :
          Not (H.OnLine D chordBC) :=
        hSameDA.1

      have hAoff :
          Not (H.OnLine A chordBC) :=
        hSameDA.2.1

      have hBCD :
          Not (PrimCollinear Geo B C D) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C D
          chordBC
          hBC
          hBchord
          hCchord
          hDoff

      have hBDC :
          Not (PrimCollinear Geo B D C) := by
        intro h
        exact
          hBCD
            (PrimCollinearRotate
              Geo B D C h)

      have hBCA :
          Not (PrimCollinear Geo B C A) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C A
          chordBC
          hBC
          hBchord
          hCchord
          hAoff

      have hCAB :
          Not (PrimCollinear Geo C A B) := by
        intro h
        exact
          hBCA
            (PrimCollinearCycle
              Geo A B C
              (PrimCollinearCycle
                Geo C A B h))

      have hCDO_BAO :
          Geo.AngleCongruent
            C D O
            B A O :=
        bookZero_43_supplements
          Geo
          B D C C O
          C A B B O
          hBDC_CAB
          hSuppD
          hSuppA
          hBDC
          hCAB

      have hODC_OAB :
          Geo.AngleCongruent
            O D C
            O A B := by
        have hAtD :
            Geo.Angle C D O =
            Geo.Angle O D C :=
          Geo.angle_swap C D O
        have hAtA :
            Geo.Angle B A O =
            Geo.Angle O A B :=
          Geo.angle_swap B A O
        unfold Geometry.Geo.AngleCongruent
          at hCDO_BAO ⊢
        rw [← hAtD, ← hAtA]
        exact hCDO_BAO

      exact hODC_OAB

  --------------------------------------------------------------------
  -- II. O-C-A.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    ------------------------------------------------------------------
    -- II.a O-C-A and O-B-D.
    --
    -- Both requested rays agree directly with the corresponding
    -- inscribed-angle rays.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_inner_inner_sameSide_chord_stage2
            Geo
            O D B A C
            hDOA
            hOBD
            hOCA
        with
        ⟨chordBC, hBchord, hCchord, hSameDA⟩

      have hBDC_BAC :
          Geo.AngleCongruent
            B D C
            B A C :=
        hIV16Same
          K A
          B C D A
          chordBC
          hBC
          hBchord
          hCchord
          hBcircle
          hCcircle
          hDcircle
          hAcircle
          hSameDA

      have hBDC_CAB :
          Geo.AngleCongruent
            B D C
            C A B := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        unfold Geometry.Geo.AngleCongruent
          at hBDC_BAC ⊢
        rw [← hAtA]
        exact hBDC_BAC

      have hDBO :
          Geo.Between D B O :=
        (HilbertOrder.between_incidence
          O B D hOBD).2.2.2.2

      have hRayDOB :
          HilbertSameRay Geo D O B :=
        hilbert_sameRay_symm
          Geo D B O
          (hilbert_sameRay_of_between
            Geo D B O hDBO)

      have hACO :
          Geo.Between A C O :=
        (HilbertOrder.between_incidence
          O C A hOCA).2.2.2.2

      have hRayAOC :
          HilbertSameRay Geo A O C :=
        hilbert_sameRay_symm
          Geo A C O
          (hilbert_sameRay_of_between
            Geo A C O hACO)

      have hAtD :
          Geo.Angle O D C =
          Geo.Angle B D C :=
        hilbert_angle_eq_of_sameRay_first
          Geo D O B C hRayDOB

      have hAtA :
          Geo.Angle O A B =
          Geo.Angle C A B :=
        hilbert_angle_eq_of_sameRay_first
          Geo A O C B hRayAOC

      unfold Geometry.Geo.AngleCongruent
        at hBDC_CAB ⊢
      rw [hAtD, hAtA]
      exact hBDC_CAB

    ------------------------------------------------------------------
    -- II.b O-C-A and O-D-B.
    --
    -- A is direct; the D-angle is the supplement required by IV.16.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_outer_inner_oppositeSide_chord_stage2
            Geo
            O D B A C
            hDOA
            hODB
            hOCA
        with
        ⟨chordBC, hBchord, hCchord, hOppDA⟩

      have hOppAD :
          HilbertOppositeSide Geo A D chordBC :=
        hilbert_oppositeSide_symm
          Geo D A chordBC hOppDA

      rcases
          hIV16Opp
            K A
            B C A D
            chordBC
            hBC
            hBchord
            hCchord
            hBcircle
            hCcircle
            hAcircle
            hDcircle
            hOppAD
        with
        ⟨X, hSuppX, hBAC_XDC⟩

      have hBDO :
          Geo.Between B D O :=
        (HilbertOrder.between_incidence
          O D B hODB).2.2.2.2

      have hSuppO :
          BookZeroSupplement Geo
            B D C
            C O :=
        ⟨hilbert_sameRay_refl
            Geo D C hCD,
          hBDO⟩

      have hDoff :
          Not (H.OnLine D chordBC) :=
        hOppAD.2.1

      have hBCD :
          Not (PrimCollinear Geo B C D) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C D
          chordBC
          hBC
          hBchord
          hCchord
          hDoff

      have hBDC :
          Not (PrimCollinear Geo B D C) := by
        intro h
        exact
          hBCD
            (PrimCollinearRotate
              Geo B D C h)

      have hRef :
          Geo.AngleCongruent
            B D C
            B D C :=
        Geometry.Geo.angle_congruent_reflexive
          Geo B D C

      have hCDX_CDO :
          Geo.AngleCongruent
            C D X
            C D O :=
        bookZero_43_supplements
          Geo
          B D C C X
          B D C C O
          hRef
          hSuppX
          hSuppO
          hBDC
          hBDC

      have hBAC_CDX :
          Geo.AngleCongruent
            B A C
            C D X := by
        have hAtD :
            Geo.Angle X D C =
            Geo.Angle C D X :=
          Geo.angle_swap X D C
        unfold Geometry.Geo.AngleCongruent
          at hBAC_XDC ⊢
        rw [← hAtD]
        exact hBAC_XDC

      have hBAC_CDO :
          Geo.AngleCongruent
            B A C
            C D O :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          B A C
          C D X
          C D O
          hBAC_CDX
          hCDX_CDO

      have hCAB_ODC :
          Geo.AngleCongruent
            C A B
            O D C := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        have hAtD :
            Geo.Angle C D O =
            Geo.Angle O D C :=
          Geo.angle_swap C D O
        unfold Geometry.Geo.AngleCongruent
          at hBAC_CDO ⊢
        rw [← hAtA, ← hAtD]
        exact hBAC_CDO

      have hODC_CAB :
          Geo.AngleCongruent
            O D C
            C A B :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C A B
          O D C
          hCAB_ODC

      have hACO :
          Geo.Between A C O :=
        (HilbertOrder.between_incidence
          O C A hOCA).2.2.2.2

      have hRayAOC :
          HilbertSameRay Geo A O C :=
        hilbert_sameRay_symm
          Geo A C O
          (hilbert_sameRay_of_between
            Geo A C O hACO)

      have hAtA :
          Geo.Angle O A B =
          Geo.Angle C A B :=
        hilbert_angle_eq_of_sameRay_first
          Geo A O C B hRayAOC

      unfold Geometry.Geo.AngleCongruent
        at hODC_CAB ⊢
      rw [hAtA]
      exact hODC_CAB
/- END folded proof support: Crossing_circle_stage10_forward_angle_nondegenerate_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage11_full_transfer_v2.lean -/
/-!
# Crossing circle -- stage 11, degenerate completion

Stage 10 proves the forward crossing-angle theorem when both secants
are proper:

  A != C,  B != D.

To package the full `HilbertCrossingRaysTransfer`, only the degenerate
cases remain.

The case B=D is immediate by symmetry of angle congruence.

The case A=C is the genuine residual case.  It is an AA situation for
the two triangles OAD and OBA.  We therefore first prove, from the
already production-clean Euclid I.32 together with Hilbert Theorems
14 and 15, that two corresponding angle congruences imply congruence
of the third angles.

No angle measure, similarity arithmetic, or new axiom is introduced.
-/

------------------------------------------------------------------------
-- 1. Two equal angles determine the third angle.
------------------------------------------------------------------------

/--
Euclidean AA third-angle theorem.

If triangles ABC and A'B'C' have two corresponding angles congruent,

  angle BAC ~= angle B'A'C',
  angle ABC ~= angle A'B'C',

then their third angles are congruent:

  angle ACB ~= angle A'C'B'.

The proof uses Euclid I.32 on both triangles.  The two exterior angles
are decomposed into the two remote interior angles.  Hilbert Theorem 15
adds the corresponding pieces, and Hilbert Theorem 14 transports the
result back across the two straight-line extensions.
-/
theorem hilbert_AA_third_angle_stage11
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (A B C A' B' C' : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hA'B'C' : Not (PrimCollinear Geo A' B' C'))
    (hAngleA :
      Geo.AngleCongruent
        B A C
        B' A' C')
    (hAngleB :
      Geo.AngleCongruent
        A B C
        A' B' C') :
    Geo.AngleCongruent
      A C B
      A' C' B' := by

  --------------------------------------------------------------------
  -- Extend BC and B'C' beyond C and C'.
  --------------------------------------------------------------------

  have hBC :
      Ne B C :=
    hilbert_noncollinear_ne_first
      Geo B C A
      (by
        intro h
        exact
          hABC
            (PrimCollinearCycle
              Geo C A B
              (PrimCollinearCycle
                Geo B C A h)))

  have hB'C' :
      Ne B' C' :=
    hilbert_noncollinear_ne_first
      Geo B' C' A'
      (by
        intro h
        exact
          hA'B'C'
            (PrimCollinearCycle
              Geo C' A' B'
              (PrimCollinearCycle
                Geo B' C' A' h)))

  rcases
      HilbertOrder.between_extension
        B C hBC
    with
    ⟨D, hBCD⟩

  rcases
      HilbertOrder.between_extension
        B' C' hB'C'
    with
    ⟨D', hB'C'D'⟩

  --------------------------------------------------------------------
  -- Euclid I.32 decomposes the two exterior angles.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A B C D
        hABC
        hBCD
    with
    ⟨R, hARD, hBAC_ACR, hABC_RCD⟩

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A' B' C' D'
        hA'B'C'
        hB'C'D'
    with
    ⟨R', hA'R'D', hB'A'C'_A'C'R', hA'B'C'_R'C'D'⟩

  --------------------------------------------------------------------
  -- Corresponding pieces of the two exterior angles are congruent.
  --------------------------------------------------------------------

  have hACR_BAC :
      Geo.AngleCongruent
        A C R
        B A C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B A C
      A C R
      hBAC_ACR

  have hACR_B'A'C' :
      Geo.AngleCongruent
        A C R
        B' A' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C R
      B A C
      B' A' C'
      hACR_BAC
      hAngleA

  have hACR_A'C'R' :
      Geo.AngleCongruent
        A C R
        A' C' R' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C R
      B' A' C'
      A' C' R'
      hACR_B'A'C'
      hB'A'C'_A'C'R'

  have hRCD_ABC :
      Geo.AngleCongruent
        R C D
        A B C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B C
      R C D
      hABC_RCD

  have hRCD_A'B'C' :
      Geo.AngleCongruent
        R C D
        A' B' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      R C D
      A B C
      A' B' C'
      hRCD_ABC
      hAngleB

  have hRCD_R'C'D' :
      Geo.AngleCongruent
        R C D
        R' C' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      R C D
      A' B' C'
      R' C' D'
      hRCD_A'B'C'
      hA'B'C'_R'C'D'

  --------------------------------------------------------------------
  -- A,C,D and A',C',D' are genuine noncollinear triples.
  --------------------------------------------------------------------

  have hBCDdata :=
    HilbertOrder.between_incidence
      B C D hBCD

  have hCD :
      Ne C D :=
    hBCDdata.2.1

  have hBCDcol :
      PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  rcases hBCDcol with
    ⟨lineBC, hBlineBC, hClineBC, hDlineBC⟩

  have hAoffBC :
      Not (H.OnLine A lineBC) := by
    intro hAlineBC
    exact
      hABC
        ⟨lineBC,
          hAlineBC,
          hBlineBC,
          hClineBC⟩

  have hCDA :
      Not (PrimCollinear Geo C D A) :=
    hilbert_not_collinear_of_off_line
      Geo
      C D A
      lineBC
      hCD
      hClineBC
      hDlineBC
      hAoffBC

  have hACD :
      Not (PrimCollinear Geo A C D) := by
    intro h
    exact
      hCDA
        (PrimCollinearCycle
          Geo A C D h)

  have hB'C'D'data :=
    HilbertOrder.between_incidence
      B' C' D' hB'C'D'

  have hC'D' :
      Ne C' D' :=
    hB'C'D'data.2.1

  have hB'C'D'col :
      PrimCollinear Geo B' C' D' :=
    hB'C'D'data.2.2.2.1

  rcases hB'C'D'col with
    ⟨lineB'C', hB'line, hC'line, hD'line⟩

  have hA'off :
      Not (H.OnLine A' lineB'C') := by
    intro hA'line
    exact
      hA'B'C'
        ⟨lineB'C',
          hA'line,
          hB'line,
          hC'line⟩

  have hC'D'A' :
      Not (PrimCollinear Geo C' D' A') :=
    hilbert_not_collinear_of_off_line
      Geo
      C' D' A'
      lineB'C'
      hC'D'
      hC'line
      hD'line
      hA'off

  have hA'C'D' :
      Not (PrimCollinear Geo A' C' D') := by
    intro h
    exact
      hC'D'A'
        (PrimCollinearCycle
          Geo A' C' D' h)

  --------------------------------------------------------------------
  -- The I.32 divider rays CR and C'R' are genuine.
  --------------------------------------------------------------------

  have hARDdata :=
    HilbertOrder.between_incidence
      A R D hARD

  have hAR :
      Ne A R :=
    hARDdata.1

  have hRD :
      Ne R D :=
    hARDdata.2.1

  have hARDcol :
      PrimCollinear Geo A R D :=
    hARDdata.2.2.2.1

  have hCR :
      Ne C R := by
    intro hCR
    subst R
    exact hACD hARDcol

  rcases
      HilbertPlaneIncidence.line_through
        C R hCR
    with
    ⟨lineCR, hClineCR, hRlineCR⟩

  have hAoffCR :
      Not (H.OnLine A lineCR) := by
    intro hAlineCR

    have hDlineCR :
        H.OnLine D lineCR :=
      hilbert_collinear_on_line
        Geo
        A R D
        lineCR
        hAR
        hAlineCR
        hRlineCR
        hARDcol

    exact
      hACD
        ⟨lineCR,
          hAlineCR,
          hClineCR,
          hDlineCR⟩

  have hDoffCR :
      Not (H.OnLine D lineCR) := by
    intro hDlineCR

    have hRDA :
        PrimCollinear Geo R D A :=
      PrimCollinearCycle
        Geo A R D hARDcol

    have hAlineCR :
        H.OnLine A lineCR :=
      hilbert_collinear_on_line
        Geo
        R D A
        lineCR
        hRD
        hRlineCR
        hDlineCR
        hRDA

    exact
      hACD
        ⟨lineCR,
          hAlineCR,
          hClineCR,
          hDlineCR⟩

  have hA'R'D'data :=
    HilbertOrder.between_incidence
      A' R' D' hA'R'D'

  have hA'R' :
      Ne A' R' :=
    hA'R'D'data.1

  have hR'D' :
      Ne R' D' :=
    hA'R'D'data.2.1

  have hA'R'D'col :
      PrimCollinear Geo A' R' D' :=
    hA'R'D'data.2.2.2.1

  have hC'R' :
      Ne C' R' := by
    intro hC'R'
    subst R'
    exact hA'C'D' hA'R'D'col

  rcases
      HilbertPlaneIncidence.line_through
        C' R' hC'R'
    with
    ⟨lineC'R', hC'lineC'R', hR'lineC'R'⟩

  have hA'offC'R' :
      Not (H.OnLine A' lineC'R') := by
    intro hA'lineC'R'

    have hD'lineC'R' :
        H.OnLine D' lineC'R' :=
      hilbert_collinear_on_line
        Geo
        A' R' D'
        lineC'R'
        hA'R'
        hA'lineC'R'
        hR'lineC'R'
        hA'R'D'col

    exact
      hA'C'D'
        ⟨lineC'R',
          hA'lineC'R',
          hC'lineC'R',
          hD'lineC'R'⟩

  have hD'offC'R' :
      Not (H.OnLine D' lineC'R') := by
    intro hD'lineC'R'

    have hR'D'A' :
        PrimCollinear Geo R' D' A' :=
      PrimCollinearCycle
        Geo A' R' D' hA'R'D'col

    have hA'lineC'R' :
        H.OnLine A' lineC'R' :=
      hilbert_collinear_on_line
        Geo
        R' D' A'
        lineC'R'
        hR'D'
        hR'lineC'R'
        hD'lineC'R'
        hR'D'A'

    exact
      hA'C'D'
        ⟨lineC'R',
          hA'lineC'R',
          hC'lineC'R',
          hD'lineC'R'⟩

  --------------------------------------------------------------------
  -- In both triangles the exterior endpoints lie on opposite sides
  -- of the divider ray.  Hence the side configurations match.
  --------------------------------------------------------------------

  have hOppAD :
      HilbertOppositeSide Geo A D lineCR :=
    ⟨hAoffCR,
      hDoffCR,
      ⟨R, hARD, hRlineCR⟩⟩

  have hOppA'D' :
      HilbertOppositeSide Geo A' D' lineC'R' :=
    ⟨hA'offC'R',
      hD'offC'R',
      ⟨R', hA'R'D', hR'lineC'R'⟩⟩

  have hNotSameAD :
      Not (HilbertSameSide Geo A D lineCR) :=
    hilbert_oppositeSide_not_sameSide
      Geo A D lineCR hOppAD

  have hNotSameA'D' :
      Not (HilbertSameSide Geo A' D' lineC'R') :=
    hilbert_oppositeSide_not_sameSide
      Geo A' D' lineC'R' hOppA'D'

  have hSideConfiguration :
      HilbertSameSide Geo A D lineCR ↔
      HilbertSameSide Geo A' D' lineC'R' := by
    constructor
    · intro hSame
      exact False.elim (hNotSameAD hSame)
    · intro hSame
      exact False.elim (hNotSameA'D' hSame)

  --------------------------------------------------------------------
  -- Hilbert Theorem 15 adds the corresponding I.32 pieces:
  -- angle ACD ~= angle A'C'D'.
  --------------------------------------------------------------------

  have hACD_A'C'D' :
      Geo.AngleCongruent
        A C D
        A' C' D' :=
    hilbert_angle_addition
      Geo
      A C R D
      A' C' R' D'
      lineCR lineC'R'
      hCR
      hC'R'
      hClineCR
      hRlineCR
      hC'lineC'R'
      hR'lineC'R'
      hAoffCR
      hDoffCR
      hA'offC'R'
      hD'offC'R'
      hSideConfiguration
      hACD
      hA'C'D'
      hACR_A'C'R'
      hRCD_R'C'D'

  --------------------------------------------------------------------
  -- Reverse both exterior angles and use Hilbert Theorem 14 to pass
  -- from D,D' back to B,B'.
  --------------------------------------------------------------------

  have hDCA_D'C'A' :
      Geo.AngleCongruent
        D C A
        D' C' A' :=
    (Geo.angle_congruent_reverse_second
      D C A
      A' C' D').mp
      ((Geo.angle_congruent_reverse_first
        A C D
        A' C' D').mp
        hACD_A'C'D')

  have hDCB :
      Geo.Between D C B :=
    (HilbertOrder.between_incidence
      B C D hBCD).2.2.2.2

  have hD'C'B' :
      Geo.Between D' C' B' :=
    (HilbertOrder.between_incidence
      B' C' D' hB'C'D').2.2.2.2

  have hDCA :
      Not (PrimCollinear Geo D C A) := by
    intro h
    exact
      hACD
        (PrimCollinearSymm
          Geo D C A h)

  have hD'C'A' :
      Not (PrimCollinear Geo D' C' A') := by
    intro h
    exact
      hA'C'D'
        (PrimCollinearSymm
          Geo D' C' A' h)

  exact
    hilbert_adjacent_angles_congruent
      Geo
      D C A B
      D' C' A' B'
      hDCB
      hD'C'B'
      hDCA
      hD'C'A'
      hDCA_D'C'A'


------------------------------------------------------------------------
-- 2. Complete crossing-rays transfer.
------------------------------------------------------------------------

/--
The complete planar crossing-rays theorem.

The proper-secant case is stage 10.
If B=D, the conclusion is simply symmetry of the given angle
congruence.
If A=C and B!=D, compare triangles OAD and OBA.  The angle at O is
the same because A,C and B,D lie on the same respective rays; the
second angle is the hypothesis; `hilbert_AA_third_angle_stage11`
supplies the target third angle.
-/
theorem hilbert_crossing_rays_transfer_stage11
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo)) :
    HilbertCrossingRaysTransfer
      (Geo := Geo) := by

  intro O A C B D hAOB hRayAC hRayBD hAngle

  --------------------------------------------------------------------
  -- Degenerate second secant: B=D.
  --------------------------------------------------------------------

  by_cases hBD :
      B = D

  · subst D

    exact
      Geometry.Geo.angle_congruent_symmetry
        Geo
        O A B
        O B C
        hAngle

  --------------------------------------------------------------------
  -- From now on B!=D.
  --------------------------------------------------------------------

  · by_cases hAC :
        A = C

    ------------------------------------------------------------------
    -- Degenerate first secant: A=C.
    ------------------------------------------------------------------

    · subst C

      have hRayAA :
          HilbertSameRay Geo O A A :=
        hilbert_sameRay_refl
          Geo O A hRayAC.1

      have hAOD :
          Not (PrimCollinear Geo A O D) :=
        hilbert_noncollinear_of_sameRays
          Geo
          A O B
          A D
          hAOB
          hRayAA
          hRayBD

      have hOAD :
          Not (PrimCollinear Geo O A D) := by
        intro h
        exact
          hAOD
            (PrimCollinearSwap
              Geo O A D h)

      have hOBA :
          Not (PrimCollinear Geo O B A) := by
        intro h
        exact
          hAOB
            (PrimCollinearCycle
              Geo B A O
              (PrimCollinearCycle
                Geo O B A h))

      have hAtO :
          Geo.AngleCongruent
            A O D
            B O A :=
        hilbert_crossing_angle_at_O_stage1
          Geo
          O A A B D
          hRayAA
          hRayBD

      exact
        hilbert_AA_third_angle_stage11
          Geo
          O A D
          O B A
          hOAD
          hOBA
          hAtO
          hAngle

    ------------------------------------------------------------------
    -- Proper crossing: invoke stages 9 and 10.
    ------------------------------------------------------------------

    · have hCyclic :
          HilbertConcyclic4 Geo A C D B :=
        hilbert_crossing_chords_concyclic_stage9
          Geo
          hIV16Same
          hIV16Opp
          hIV18
          O A C B D
          hAOB
          hRayAC
          hRayBD
          hAngle

      exact
        hilbert_crossing_chords_angle_nondegenerate_stage10
          Geo
          hIV16Same
          hIV16Opp
          O A C B D
          hAOB
          hRayAC
          hRayBD
          hAC
          hBD
          hCyclic
/- END folded proof support: Crossing_circle_stage11_full_transfer_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage13_forder15_to_IV16Opp_v2.lean -/
/-!
# Forder IV.15 -> IV.16 opposite-side half

The remaining lower circle layer contains Forder IV.16 in two halves.
The opposite-side half is not an independent circle theorem.

Forder's source derives it immediately from IV.15:

  opposite angles of a cyclic quadrilateral are supplementary.

This file isolates IV.15 in the exact synthetic Book Zero language and
derives the already used `HilbertForderIV16OppositeSide` interface from
it.

No new axiom is declared.
-/

------------------------------------------------------------------------
-- 2. IV.15 gives the opposite-side half of IV.16.
------------------------------------------------------------------------

/--
Forder IV.16, opposite-side half, derived directly from IV.15.

For circle points A,B,C,E with C and E on opposite sides of chord AB,
consider the cyclic quadrilateral

  C-A-E-B.

Its opposite angles are exactly

  angle ACB
  angle AEB.

IV.15 therefore supplies an extension A-E-X such that

  angle ACB ~= angle XEB,

which is precisely `HilbertForderIV16OppositeSide`.
-/
theorem hilbert_forder_IV16_opposite_of_IV15_stage13
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV15 :
      HilbertForderIV15CyclicSupplement
        (Geo := Geo)) :
    HilbertForderIV16OppositeSide
      (Geo := Geo) := by

  intro K R A B C E chord
    hAB hAchord hBchord
    hAcircle hBcircle hCcircle hEcircle
    hOppCE

  have hCoff :
      Not (H.OnLine C chord) :=
    hOppCE.1

  have hEoff :
      Not (H.OnLine E chord) :=
    hOppCE.2.1

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hABE :
      Not (PrimCollinear Geo A B E) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B E
      chord
      hAB
      hAchord
      hBchord
      hEoff

  have hAEB :
      Not (PrimCollinear Geo A E B) := by
    intro h
    exact
      hABE
        (PrimCollinearRotate
          Geo A E B h)

  have hCyclic :
      HilbertConcyclic4 Geo C A E B :=
    hilbert_concyclic4_of_circle
      Geo
      K R
      C A E B
      hCcircle
      hAcircle
      hEcircle
      hBcircle

  exact
    hIV15
      C A E B
      chord
      hAB
      hAchord
      hBchord
      hCyclic
      hOppCE
      hACB
      hAEB
/- END folded proof support: Crossing_circle_stage13_forder15_to_IV16Opp_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage14_antipode_v1.lean -/
/-!
# Circle infrastructure -- stage 14, antipodal point

Forder IV.16 uses the point X on the given circle such that

  C-K-X,

where K is the center.

The construction is already implicit in the secant/tangent machinery
of stage 4.  Here it is isolated as a reusable circle lemma.

No continuity principle and no new axiom are used.
-/

------------------------------------------------------------------------
-- 1. A genuine circle determined by two distinct points has nonzero
--    radius; hence its center is distinct from every point on it.
------------------------------------------------------------------------

theorem hilbert_circle_center_ne_point_of_two_distinct_stage14
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K R A B C : Geo.Point)
    (hAB : Ne A B)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C) :
    Ne K C := by

  intro hKC
  subst C

  have hKA_KK :
      Geo.Congruent K A K K :=
    hilbert_circle_center_congruent
      Geo
      K R
      A K
      hA hC

  have hKB_KK :
      Geo.Congruent K B K K :=
    hilbert_circle_center_congruent
      Geo
      K R
      B K
      hB hC

  have hKA :
      K = A :=
    bookZero_nullSegment1
      Geo K A K hKA_KK

  have hKB :
      K = B :=
    bookZero_nullSegment1
      Geo K B K hKB_KK

  exact
    hAB
      (hKA.symm.trans hKB)


------------------------------------------------------------------------
-- 2. Antipodal extension through the center.
------------------------------------------------------------------------

/--
For every point C on a nondegenerate Hilbert circle there is a point X
on the same circle with the center K strictly between C and X.

This is the synthetic antipodal-point construction needed in Forder
IV.16.
-/
theorem hilbert_circle_antipode_stage14
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K R A B C : Geo.Point)
    (hAB : Ne A B)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C) :
    exists X : Geo.Point,
      Geo.Between C K X /\
      HilbertCircle Geo K R X := by

  have hKC :
      Ne K C :=
    hilbert_circle_center_ne_point_of_two_distinct_stage14
      Geo
      K R A B C
      hAB
      hA hB hC

  rcases
      hilbert_extend_segment_beyond
        Geo C K hKC.symm
    with
    ⟨X, hCKX, hCK_KX⟩

  have hKX_CK :
      Geo.Congruent K X C K :=
    hilbert_congruent_symmetry
      Geo
      C K
      K X
      hCK_KX

  have hKX_KC :
      Geo.Congruent K X K C :=
    (Geo.congruent_reverse_second
      K X
      C K).mp
      hKX_CK

  have hKC_KR :
      Geo.Congruent K C K R := by
    simpa [HilbertCircle] using hC

  have hKX_KR :
      Geo.Congruent K X K R :=
    hilbert_congruent_transitivity
      Geo
      K X
      K C
      K R
      hKX_KC
      hKC_KR

  have hX :
      HilbertCircle Geo K R X := by
    simpa [HilbertCircle] using hKX_KR

  exact
    ⟨X, hCKX, hX⟩
/- END folded proof support: Crossing_circle_stage14_antipode_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage15_IV16_same_reduction_v1.lean -/
/-!
# Forder IV.16 same-side -- stage 15 reduction

The source proof of the same-side half of Forder IV.16 has three
geometrically distinct cases according to the position of the center K
relative to chord AB.

1. K lies on AB:
   AB is a diameter, so both inscribed angles are right (Forder IV.13).

2. C,D,K lie on the same side of AB:
   apply Forder IV.12.1 directly.

3. C,D lie on one side of AB and K on the other:
   take X antipodal to C, so C-K-X.
   Then C,X and D,X are opposite-side pairs.  The already reduced
   opposite-side half of IV.16 says that both ACB and ADB are
   supplements of AXB; hence they are congruent.

This file formalizes exactly that reduction.  It does not yet prove
IV.12.1 or IV.13.
-/

------------------------------------------------------------------------
-- 1. The two lower source theorems still needed.
------------------------------------------------------------------------

/--
Forder IV.12.1.

If A,B,C,D lie on one circle with center K and C,D,K all lie in the
same half-plane determined by chord AB, then the two inscribed angles
subtending AB are congruent.
-/
theorem hilbert_forder_IV16_same_of_IV12_1_IV13_IV15_stage15
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV12_1 :
      HilbertForderIV12_1SameSegment
        (Geo := Geo))
    (hIV13 :
      HilbertForderIV13DiameterRightAngle
        (Geo := Geo))
    (hIV15 :
      HilbertForderIV15CyclicSupplement
        (Geo := Geo)) :
    HilbertForderIV16SameSide
      (Geo := Geo) := by

  intro K R A B C D chord
    hAB hAchord hBchord
    hAcircle hBcircle hCcircle hDcircle
    hSameCD

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCD.1

  have hDoff :
      Not (H.OnLine D chord) :=
    hSameCD.2.1

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    have hABC :
        Not (PrimCollinear Geo A B C) :=
      hilbert_not_collinear_of_off_line
        Geo
        A B C
        chord
        hAB
        hAchord
        hBchord
        hCoff
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hADB :
      Not (PrimCollinear Geo A D B) := by
    have hABD :
        Not (PrimCollinear Geo A B D) :=
      hilbert_not_collinear_of_off_line
        Geo
        A B D
        chord
        hAB
        hAchord
        hBchord
        hDoff
    intro h
    exact
      hABD
        (PrimCollinearRotate
          Geo A D B h)

  --------------------------------------------------------------------
  -- Case 1: the center lies on chord AB.  Both angles are right.
  --------------------------------------------------------------------

  by_cases hKchord :
      H.OnLine K chord

  · have hRightC :
        HilbertRightAngle Geo A C B :=
      hIV13
        K R A B C
        chord
        hAB
        hAchord
        hBchord
        hKchord
        hAcircle
        hBcircle
        hCcircle
        hCoff

    have hRightD :
        HilbertRightAngle Geo A D B :=
      hIV13
        K R A B D
        chord
        hAB
        hAchord
        hBchord
        hKchord
        hAcircle
        hBcircle
        hDcircle
        hDoff

    exact
      hilbert_all_right_angles_congruent
        Geo
        A C B
        A D B
        hACB
        hADB
        hRightC
        hRightD

  --------------------------------------------------------------------
  -- From now on the center is off chord AB.
  --------------------------------------------------------------------

  · by_cases hSameCK :
        HilbertSameSide Geo C K chord

    ------------------------------------------------------------------
    -- Case 2: C,D,K are in one half-plane.  This is IV.12.1.
    ------------------------------------------------------------------

    · have hSameDC :
          HilbertSameSide Geo D C chord :=
        hilbert_sameSide_symm
          Geo C D chord hSameCD

      have hSameDK :
          HilbertSameSide Geo D K chord :=
        hilbert_sameSide_trans
          Geo
          D C K
          chord
          hSameDC
          hSameCK

      exact
        hIV12_1
          K R A B C D
          chord
          hAB
          hAchord
          hBchord
          hAcircle
          hBcircle
          hCcircle
          hDcircle
          hSameCK
          hSameDK

    ------------------------------------------------------------------
    -- Case 3: K is opposite C (and therefore opposite D).
    ------------------------------------------------------------------

    · have hOppCK :
          HilbertOppositeSide Geo C K chord :=
        hilbert_oppositeSide_of_not_sameSide
          Geo
          C K
          chord
          hCoff
          hKchord
          hSameCK

      have hOppKC :
          HilbertOppositeSide Geo K C chord :=
        hilbert_oppositeSide_symm
          Geo C K chord hOppCK

      have hOppKD :
          HilbertOppositeSide Geo K D chord :=
        hilbert_oppositeSide_transport_right
          Geo
          K C D
          chord
          hOppKC
          hSameCD

      have hOppDK :
          HilbertOppositeSide Geo D K chord :=
        hilbert_oppositeSide_symm
          Geo K D chord hOppKD

      --------------------------------------------------------------
      -- Antipode X of C: C-K-X and X is on the same circle.
      --------------------------------------------------------------

      rcases
          hilbert_circle_antipode_stage14
            Geo
            K R A B C
            hAB
            hAcircle
            hBcircle
            hCcircle
        with
        ⟨X, hCKX, hXcircle⟩

      --------------------------------------------------------------
      -- The crossing witness for C-K extends to a crossing witness
      -- for C-X.
      --------------------------------------------------------------

      rcases hOppCK.2.2 with
        ⟨Y, hCYK, hYchord⟩

      have hCYX :
          Geo.Between C Y X :=
        (hilbert_between_inner_trans
          Geo
          C Y K X
          hCYK
          hCKX).2

      have hXoff :
          Not (H.OnLine X chord) := by
        intro hXchord

        have hCYXdata :=
          HilbertOrder.between_incidence
            C Y X hCYX

        have hYX :
            Ne Y X :=
          hCYXdata.2.1

        have hCX :
            Ne C X :=
          hCYXdata.2.2.1

        rcases
            HilbertPlaneIncidence.line_through
              C X hCX
          with
          ⟨lineCX, hClineCX, hXlineCX⟩

        have hYlineCX :
            H.OnLine Y lineCX :=
          hilbert_between_on_line
            Geo
            C Y X
            lineCX
            hClineCX
            hXlineCX
            hCYX

        have hEq :
            lineCX = chord :=
          HilbertPlaneIncidence.line_unique
            Y X hYX
            lineCX chord
            hYlineCX
            hXlineCX
            hYchord
            hXchord

        exact
          hCoff
            (hEq ▸ hClineCX)

      have hOppCX :
          HilbertOppositeSide Geo C X chord :=
        ⟨hCoff,
          hXoff,
          ⟨Y, hCYX, hYchord⟩⟩

      --------------------------------------------------------------
      -- Since D is on the same side as C, D and X are also opposite.
      --------------------------------------------------------------

      have hOppXC :
          HilbertOppositeSide Geo X C chord :=
        hilbert_oppositeSide_symm
          Geo C X chord hOppCX

      have hOppXD :
          HilbertOppositeSide Geo X D chord :=
        hilbert_oppositeSide_transport_right
          Geo
          X C D
          chord
          hOppXC
          hSameCD

      have hOppDX :
          HilbertOppositeSide Geo D X chord :=
        hilbert_oppositeSide_symm
          Geo X D chord hOppXD

      --------------------------------------------------------------
      -- IV.15 supplies the already-reduced opposite-side half IV.16.
      --------------------------------------------------------------

      have hIV16Opp :
          HilbertForderIV16OppositeSide
            (Geo := Geo) :=
        hilbert_forder_IV16_opposite_of_IV15_stage13
          Geo
          hIV15

      rcases
          hIV16Opp
            K R A B C X
            chord
            hAB
            hAchord
            hBchord
            hAcircle
            hBcircle
            hCcircle
            hXcircle
            hOppCX
        with
        ⟨U, hSuppU, hACB_UXB⟩

      rcases
          hIV16Opp
            K R A B D X
            chord
            hAB
            hAchord
            hBchord
            hAcircle
            hBcircle
            hDcircle
            hXcircle
            hOppDX
        with
        ⟨V, hSuppV, hADB_VXB⟩

      --------------------------------------------------------------
      -- UXB and VXB are two supplements of the same angle AXB.
      --------------------------------------------------------------

      have hAXB :
          Not (PrimCollinear Geo A X B) := by
        have hABX :
            Not (PrimCollinear Geo A B X) :=
          hilbert_not_collinear_of_off_line
            Geo
            A B X
            chord
            hAB
            hAchord
            hBchord
            hXoff
        intro h
        exact
          hABX
            (PrimCollinearRotate
              Geo A X B h)

      have hRefAXB :
          Geo.AngleCongruent
            A X B
            A X B :=
        Geometry.Geo.angle_congruent_reflexive
          Geo A X B

      have hBXU_BXV :
          Geo.AngleCongruent
            B X U
            B X V :=
        bookZero_43_supplements
          Geo
          A X B B U
          A X B B V
          hRefAXB
          hSuppU
          hSuppV
          hAXB
          hAXB

      have hUXB_VXB :
          Geo.AngleCongruent
            U X B
            V X B := by
        exact
          (Geo.angle_congruent_reverse_second
            U X B
            B X V).mp
            ((Geo.angle_congruent_reverse_first
              B X U
              B X V).mp
              hBXU_BXV)

      have hUXB_ADB :
          Geo.AngleCongruent
            U X B
            A D B :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          U X B
          V X B
          A D B
          hUXB_VXB
          (Geometry.Geo.angle_congruent_symmetry
            Geo
            A D B
            V X B
            hADB_VXB)

      exact
        Geometry.Geo.angle_congruent_transitivity
          Geo
          A C B
          U X B
          A D B
          hACB_UXB
          hUXB_ADB
/- END folded proof support: Crossing_circle_stage15_IV16_same_reduction_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage16_diameter_midpoint_v1.lean -/
/-!
# Circle infrastructure -- stage 16, center of a diameter

If two distinct points A,B lie on one circle centered at K and K lies
on their carrier, then K is the strict midpoint of AB.

This is the order-theoretic fact needed before proving Forder IV.13.

No new axiom is introduced.
-/

/--
A circle center lying on a chord through two distinct circle points is
the midpoint of that chord.

The only possible collinear orders are

  A-K-B,  K-A-B,  A-B-K.

The latter two would make one radius a proper subsegment of the other,
contradicting congruence of the radii.
-/
theorem hilbert_circle_center_midpoint_of_chord_stage16
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K R A B : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKchord : H.OnLine K chord)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B) :
    HilbertIsMidpoint Geo K A B := by

  have hKA :
      Ne K A :=
    hilbert_circle_center_ne_point_of_two_distinct_stage14
      Geo
      K R A B A
      hAB
      hA hB hA

  have hKB :
      Ne K B :=
    hilbert_circle_center_ne_point_of_two_distinct_stage14
      Geo
      K R A B B
      hAB
      hA hB hB

  have hAK :
      Ne A K :=
    hKA.symm

  have hKA_KB :
      Geo.Congruent K A K B :=
    hilbert_circle_center_congruent
      Geo
      K R
      A B
      hA hB

  have hAKBcol :
      PrimCollinear Geo A K B :=
    ⟨chord,
      hAchord,
      hKchord,
      hBchord⟩

  rcases
      hilbert_between_trichotomy
        Geo
        A K B
        hAK
        hKB
        hAB
        hAKBcol
    with
    hAKB | hKAB | hABK

  --------------------------------------------------------------------
  -- The required order A-K-B.
  --------------------------------------------------------------------

  · have hAK_KB :
        Geo.Congruent A K K B :=
      CongruentReverseFirst
        Geo
        K A
        K B
        hKA_KB

    exact
      ⟨hAKB, hAK_KB⟩

  --------------------------------------------------------------------
  -- K-A-B would give KA < KB, contradicting equal radii.
  --------------------------------------------------------------------

  · have hKA_lt_KB :
        HilbertSegmentLess Geo K A K B :=
      hilbert_segmentLess_of_between
        Geo
        K A B
        hKAB

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
            Geo
            K A
            K B
            hKA_lt_KB)
          hKA_KB)

  --------------------------------------------------------------------
  -- A-B-K gives KB < KA, again contradicting equal radii.
  --------------------------------------------------------------------

  · have hKBA :
        Geo.Between K B A :=
      (HilbertOrder.between_incidence
        A B K hABK).2.2.2.2

    have hKB_lt_KA :
        HilbertSegmentLess Geo K B K A :=
      hilbert_segmentLess_of_between
        Geo
        K B A
        hKBA

    have hKB_KA :
        Geo.Congruent K B K A :=
      hilbert_congruent_symmetry
        Geo
        K A
        K B
        hKA_KB

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
            Geo
            K B
            K A
            hKB_lt_KA)
          hKB_KA)
/- END folded proof support: Crossing_circle_stage16_diameter_midpoint_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage17_forder13_v3.lean -/
/-!
# Forder IV.13 -- stage 17

If AB is a diameter of a Hilbert circle and C is another point of the
circle, then angle ACB is right.

The proof is purely synthetic.

* stage 16 gives A-K-B, where K is the circle center;
* KA ~= KC and KB ~= KC make KAC and KBC isosceles;
* extend AC through C to X;
* Euclid I.32 applied to triangle BAC decomposes the exterior angle
  BCX into the two remote interior angles;
* Hilbert Theorem 15 adds the corresponding congruent angle parts,
  proving angle ACB ~= angle BCX.

This is exactly the adjacent-angle definition of a right angle.
No numerical angle measure and no new axiom are used.
-/

theorem hilbert_forder_IV13_diameter_right_angle_stage17
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV13DiameterRightAngle
      (Geo := Geo) := by

  intro K R A B C chord
    hAB hAchord hBchord hKchord
    hAcircle hBcircle hCcircle hCoff

  --------------------------------------------------------------------
  -- K is the strict midpoint of the diameter AB.
  --------------------------------------------------------------------

  have hMidK :
      HilbertIsMidpoint Geo K A B :=
    hilbert_circle_center_midpoint_of_chord_stage16
      Geo
      K R A B
      chord
      hAB
      hAchord
      hBchord
      hKchord
      hAcircle
      hBcircle

  have hAKB :
      Geo.Between A K B :=
    hMidK.1

  have hAKBdata :=
    HilbertOrder.between_incidence
      A K B hAKB

  have hAK :
      Ne A K :=
    hAKBdata.1

  have hKB :
      Ne K B :=
    hAKBdata.2.1

  have hKA :
      Ne K A :=
    hAK.symm

  have hBK :
      Ne B K :=
    hKB.symm

  have hABcol :
      PrimCollinear Geo A K B :=
    hAKBdata.2.2.2.1

  --------------------------------------------------------------------
  -- C is off the diameter, so all triangles below are genuine.
  --------------------------------------------------------------------

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    have hABC :
        Not (PrimCollinear Geo A B C) :=
      hilbert_not_collinear_of_off_line
        Geo
        A B C
        chord
        hAB
        hAchord
        hBchord
        hCoff
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hACB
        (PrimCollinearCycle
          Geo B A C h)

  have hAC :
      Ne A C :=
    hilbert_noncollinear_ne_first
      Geo
      A C B
      hACB

  have hCA :
      Ne C A :=
    hAC.symm

  have hBC :
      Ne B C :=
    hilbert_noncollinear_ne_first
      Geo
      B C A
      (by
        intro h
        exact
          hBAC
            (PrimCollinearRotate
              Geo B C A h))

  have hCB :
      Ne C B :=
    hBC.symm

  --------------------------------------------------------------------
  -- The two radius triangles KAC and KBC are isosceles.
  --------------------------------------------------------------------

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      A C
      hAcircle
      hCcircle

  have hKB_KC :
      Geo.Congruent K B K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      B C
      hBcircle
      hCcircle

  have hAKC :
      Not (PrimCollinear Geo K A C) :=
    hilbert_not_collinear_of_off_line
      Geo
      K A C
      chord
      hKA
      hKchord
      hAchord
      hCoff

  have hBKC :
      Not (PrimCollinear Geo K B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      K B C
      chord
      hKB
      hKchord
      hBchord
      hCoff


  have hIsoA :
      Geo.AngleCongruent
        K A C
        K C A :=
    hilbert_isosceles_base_angles
      Geo
      K A C
      hAKC
      hKA_KC

  have hIsoB :
      Geo.AngleCongruent
        K B C
        K C B :=
    hilbert_isosceles_base_angles
      Geo
      K B C
      hBKC
      hKB_KC

  --------------------------------------------------------------------
  -- K and B determine the same ray from A; K and A determine the
  -- same ray from B.
  --------------------------------------------------------------------

  have hRayAKB :
      HilbertSameRay Geo A K B :=
    hilbert_sameRay_of_between
      Geo A K B hAKB

  have hBKA :
      Geo.Between B K A :=
    hAKBdata.2.2.2.2

  have hRayBKA :
      HilbertSameRay Geo B K A :=
    hilbert_sameRay_of_between
      Geo B K A hBKA

  have hKAC_BAC :
      Geo.Angle K A C =
      Geo.Angle B A C :=
    hilbert_angle_eq_of_sameRay_first
      Geo A K B C hRayAKB

  have hKBC_ABC :
      Geo.Angle K B C =
      Geo.Angle A B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B K A C hRayBKA

  have hBAC_KCA :
      Geo.AngleCongruent
        B A C
        K C A := by
    unfold Geometry.Geo.AngleCongruent at hIsoA ⊢
    rw [← hKAC_BAC]
    exact hIsoA

  have hABC_KCB :
      Geo.AngleCongruent
        A B C
        K C B := by
    unfold Geometry.Geo.AngleCongruent at hIsoB ⊢
    rw [← hKBC_ABC]
    exact hIsoB

  --------------------------------------------------------------------
  -- Extend AC through C to X.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A C hAC
    with
    ⟨X, hACX⟩

  have hACXdata :=
    HilbertOrder.between_incidence
      A C X hACX

  have hCX :
      Ne C X :=
    hACXdata.2.1

  have hAX :
      Ne A X :=
    hACXdata.2.2.1

  have hACXcol :
      PrimCollinear Geo A C X :=
    hACXdata.2.2.2.1

  --------------------------------------------------------------------
  -- The carrier AC will also be used to show B,C,X noncollinear.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC
    with
    ⟨lineAC, hAlineAC, hClineAC⟩

  have hXlineAC :
      H.OnLine X lineAC :=
    hilbert_collinear_on_line
      Geo
      A C X
      lineAC
      hAC
      hAlineAC
      hClineAC
      hACXcol

  have hBoffAC :
      Not (H.OnLine B lineAC) := by
    intro hBlineAC
    exact
      hBAC
        ⟨lineAC,
          hBlineAC,
          hAlineAC,
          hClineAC⟩

  have hBCX :
      Not (PrimCollinear Geo B C X) := by
    intro h
    have hBlineAC :
        H.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo
        C X B
        lineAC
        hCX
        hClineAC
        hXlineAC
        (PrimCollinearCycle
          Geo B C X h)
    exact hBoffAC hBlineAC

  have hXCB :
      Not (PrimCollinear Geo X C B) := by
    intro h
    exact
      hBCX
        (PrimCollinearSymm
          Geo X C B h)

  --------------------------------------------------------------------
  -- Euclid I.32 for triangle BAC with AC produced through C to X.
  --
  -- It supplies P on BX such that
  --
  --   angle ABC ~= angle BCP
  --   angle BAC ~= angle PCX.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B A C X
        hBAC
        hACX
    with
    ⟨P, hBPX, hABC_BCP, hBAC_PCX⟩

  have hBPXdata :=
    HilbertOrder.between_incidence
      B P X hBPX

  have hBP :
      Ne B P :=
    hBPXdata.1

  have hPX :
      Ne P X :=
    hBPXdata.2.1

  have hBX :
      Ne B X :=
    hBPXdata.2.2.1

  have hBPXcol :
      PrimCollinear Geo B P X :=
    hBPXdata.2.2.2.1

  --------------------------------------------------------------------
  -- P is distinct from C.
  --------------------------------------------------------------------

  have hCP :
      Ne C P := by
    intro hCP
    subst P

    have hBCXbetween :
        Geo.Between B C X :=
      hBPX

    have hBlineAC :
        H.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo
        C X B
        lineAC
        hCX
        hClineAC
        hXlineAC
        (PrimCollinearCycle
          Geo
          B C X
          (HilbertOrder.between_incidence
            B C X hBCXbetween).2.2.2.1)

    exact hBoffAC hBlineAC

  --------------------------------------------------------------------
  -- Construct the two splitting carriers CK and CP.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        C K
        (hilbert_circle_center_ne_point_of_two_distinct_stage14
          Geo
          K R A B C
          hAB
          hAcircle
          hBcircle
          hCcircle).symm
    with
    ⟨lineCK, hClineCK, hKlineCK⟩

  rcases
      HilbertPlaneIncidence.line_through
        C P hCP
    with
    ⟨lineCP, hClineCP, hPlineCP⟩

  --------------------------------------------------------------------
  -- A and B are off CK.
  --------------------------------------------------------------------

  have hAoffCK :
      Not (H.OnLine A lineCK) := by
    intro hAlineCK

    have hEq :
        lineCK = chord :=
      HilbertPlaneIncidence.line_unique
        K A
        hKA
        lineCK chord
        hKlineCK
        hAlineCK
        hKchord
        hAchord

    have hCchord :
        H.OnLine C chord := by
      rw [← hEq]
      exact hClineCK

    exact hCoff hCchord

  have hBoffCK :
      Not (H.OnLine B lineCK) := by
    intro hBlineCK

    have hEq :
        lineCK = chord :=
      HilbertPlaneIncidence.line_unique
        K B
        hKB
        lineCK chord
        hKlineCK
        hBlineCK
        hKchord
        hBchord

    have hCchord :
        H.OnLine C chord := by
      rw [← hEq]
      exact hClineCK

    exact hCoff hCchord

  have hOppAB_CK :
      HilbertOppositeSide Geo A B lineCK :=
    ⟨hAoffCK,
      hBoffCK,
      ⟨K, hAKB, hKlineCK⟩⟩

  have hNotSameAB_CK :
      Not (HilbertSameSide Geo A B lineCK) :=
    hilbert_oppositeSide_not_sameSide
      Geo
      A B
      lineCK
      hOppAB_CK

  --------------------------------------------------------------------
  -- B and X are off CP.  Since B-P-X, they are opposite sides of CP.
  --------------------------------------------------------------------

  have hBoffCP :
      Not (H.OnLine B lineCP) := by
    intro hBlineCP

    have hXlineCP :
        H.OnLine X lineCP :=
      hilbert_collinear_on_line
        Geo
        B P X
        lineCP
        hBP
        hBlineCP
        hPlineCP
        hBPXcol

    exact
      hBCX
        ⟨lineCP,
          hBlineCP,
          hClineCP,
          hXlineCP⟩

  have hXoffCP :
      Not (H.OnLine X lineCP) := by
    intro hXlineCP

    have hPXcol :
        PrimCollinear Geo P X B :=
      PrimCollinearCycle
        Geo B P X hBPXcol

    have hBlineCP :
        H.OnLine B lineCP :=
      hilbert_collinear_on_line
        Geo
        P X B
        lineCP
        hPX
        hPlineCP
        hXlineCP
        hPXcol

    exact hBoffCP hBlineCP

  have hXPB :
      Geo.Between X P B :=
    hBPXdata.2.2.2.2

  have hOppXB_CP :
      HilbertOppositeSide Geo X B lineCP :=
    ⟨hXoffCP,
      hBoffCP,
      ⟨P, hXPB, hPlineCP⟩⟩

  have hNotSameXB_CP :
      Not (HilbertSameSide Geo X B lineCP) :=
    hilbert_oppositeSide_not_sameSide
      Geo
      X B
      lineCP
      hOppXB_CP

  have hSideConfiguration :
      HilbertSameSide Geo A B lineCK ↔
      HilbertSameSide Geo X B lineCP := by
    constructor
    · intro hSame
      exact False.elim (hNotSameAB_CK hSame)
    · intro hSame
      exact False.elim (hNotSameXB_CP hSame)

  --------------------------------------------------------------------
  -- Match the two component angles.
  --
  -- First component:
  --
  --   ACK ~= XCP.
  --------------------------------------------------------------------

  have hKCA_PCX :
      Geo.AngleCongruent
        K C A
        P C X :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K C A
      B A C
      P C X
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B A C
        K C A
        hBAC_KCA)
      hBAC_PCX

  have hACK_XCP :
      Geo.AngleCongruent
        A C K
        X C P :=
    (Geo.angle_congruent_reverse_second
      A C K
      P C X).mp
      ((Geo.angle_congruent_reverse_first
        K C A
        P C X).mp
        hKCA_PCX)

  --------------------------------------------------------------------
  -- Second component:
  --
  --   KCB ~= PCB.
  --------------------------------------------------------------------

  have hKCB_BCP :
      Geo.AngleCongruent
        K C B
        B C P :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K C B
      A B C
      B C P
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        A B C
        K C B
        hABC_KCB)
      hABC_BCP

  have hKCB_PCB :
      Geo.AngleCongruent
        K C B
        P C B :=
    (Geo.angle_congruent_reverse_second
      K C B
      B C P).mp
      hKCB_BCP

  --------------------------------------------------------------------
  -- Add corresponding angle parts.
  --------------------------------------------------------------------

  have hACB_XCB :
      Geo.AngleCongruent
        A C B
        X C B :=
    hilbert_angle_addition
      Geo
      A C K B
      X C P B
      lineCK lineCP
      (hilbert_circle_center_ne_point_of_two_distinct_stage14
        Geo
        K R A B C
        hAB
        hAcircle
        hBcircle
        hCcircle).symm
      hCP
      hClineCK
      hKlineCK
      hClineCP
      hPlineCP
      hAoffCK
      hBoffCK
      hXoffCP
      hBoffCP
      hSideConfiguration
      hACB
      hXCB
      hACK_XCP
      hKCB_PCB

  have hACB_BCX :
      Geo.AngleCongruent
        A C B
        B C X :=
    (Geo.angle_congruent_reverse_second
      A C B
      X C B).mp
      hACB_XCB

  exact
    ⟨X, hACX, hACB_BCX⟩
/- END folded proof support: Crossing_circle_stage17_forder13_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage18_IV12_to_IV12_1_v1.lean -/
/-!
# Forder IV.12 -> IV.12.1 -- stage 18

Forder IV.12 states, synthetically, that if A,B,C lie on a circle
with center K and K,C are on the same side of chord AB, then the
inscribed angle ACB is one half of the central angle AKB.

Rather than introduce numerical angle measure, we encode "one half"
by an actual interior bisector ray KT of angle AKB:

  angle AKT ~= angle BKT,
  angle ACB ~= angle AKT.

The production file `HilbertAngleDecomposition` already contains the
synthetic analogue of Forder IV.46.2: halves of the same (or congruent)
angles are congruent.

Thus IV.12.1 becomes a short corollary of IV.12.
-/

------------------------------------------------------------------------
-- 1. Source-faithful synthetic interface for Forder IV.12.
------------------------------------------------------------------------

/--
Forder IV.12 in witness form.

For A,B,C on a circle centered at K, with C and K on the same side
of chord AB, there is an interior bisector KT of the central angle
AKB whose half is congruent to the inscribed angle ACB.

This is exactly the non-numerical meaning of

  angle ACB = one half angle AKB.
-/
theorem hilbert_forder_IV12_1_of_IV12_stage18
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV12 :
      HilbertForderIV12CentralHalf
        (Geo := Geo)) :
    HilbertForderIV12_1SameSegment
      (Geo := Geo) := by

  intro K R A B C D chord
    hAB hAchord hBchord
    hAcircle hBcircle hCcircle hDcircle
    hSameCK hSameDK

  --------------------------------------------------------------------
  -- Since K is off chord AB, the central angle AKB is genuine.
  --------------------------------------------------------------------

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hABK :
      Not (PrimCollinear Geo A B K) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B K
      chord
      hAB
      hAchord
      hBchord
      hKoff

  have hAKB :
      Not (PrimCollinear Geo A K B) := by
    intro h
    exact
      hABK
        (PrimCollinearRotate
          Geo A K B h)

  --------------------------------------------------------------------
  -- Apply IV.12 to C and D.
  --------------------------------------------------------------------

  rcases
      hIV12
        K R A B C
        chord
        hAB
        hAchord
        hBchord
        hAcircle
        hBcircle
        hCcircle
        hSameCK
    with
    ⟨T,
      hInsideT,
      hBisectT,
      hACB_AKT⟩

  rcases
      hIV12
        K R A B D
        chord
        hAB
        hAchord
        hBchord
        hAcircle
        hBcircle
        hDcircle
        hSameDK
    with
    ⟨U,
      hInsideU,
      hBisectU,
      hADB_AKU⟩

  --------------------------------------------------------------------
  -- T and U bisect the same nondegenerate central angle AKB.
  -- Uniqueness of angle halves gives AKT ~= AKU.
  --------------------------------------------------------------------

  have hAKT_AKU :
      Geo.AngleCongruent
        A K T
        A K U :=
    hilbert_angleDecomposition_angle_half_unique
      Geo
      K A B T U
      hAKB
      hInsideT
      hInsideU
      hBisectT
      hBisectU

  --------------------------------------------------------------------
  -- Transport the two inscribed angles through the common half.
  --------------------------------------------------------------------

  have hAKU_ADB :
      Geo.AngleCongruent
        A K U
        A D B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A D B
      A K U
      hADB_AKU

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C B
      A K T
      A D B
      hACB_AKT
      (Geometry.Geo.angle_congruent_transitivity
        Geo
        A K T
        A K U
        A D B
        hAKT_AKU
        hAKU_ADB)
/- END folded proof support: Crossing_circle_stage18_IV12_to_IV12_1_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage19_exterior_central_half_v2.lean -/
/-!
# Forder IV.12 -- stage 19, one exterior doubling block

This isolates the local construction used twice in Forder IV.12.

Let A and C lie on a circle centered at K, and extend CK through K
to X:

  C-K-X.

If A,K,C are noncollinear, Euclid I.32 applied to triangle A-C-K
produces an interior ray KT of the exterior angle AKX.  Since

  KA ~= KC,

triangle KAC is isosceles, so the two remote interior angles in I.32
are congruent.  Hence KT bisects AKX, and its half is congruent to
the angle ACK.

This is the synthetic content of

  angle AKX = 2 angle ACK,

with no numerical angle measure.
-/

/--
One-radius exterior-angle doubling lemma for a circle.

The conclusion packages the statement "ACK is half of AKX" as an
actual interior bisector KT.
-/
theorem hilbert_circle_exterior_central_half_stage19
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A C X : Geo.Point)
    (hAcircle : HilbertCircle Geo K R A)
    (hCcircle : HilbertCircle Geo K R C)
    (hAKC : Not (PrimCollinear Geo A K C))
    (hCKX : Geo.Between C K X) :
    exists T : Geo.Point,
      HilbertRayMeetsSegment Geo K T A X /\
      Geo.AngleCongruent
        A K T
        X K T /\
      Geo.AngleCongruent
        A C K
        A K T := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy.
  --------------------------------------------------------------------

  have hKAC :
      Not (PrimCollinear Geo K A C) := by
    intro h
    exact
      hAKC
        (PrimCollinearSwap
          Geo K A C h)

  have hACK :
      Not (PrimCollinear Geo A C K) := by
    intro h
    exact
      hAKC
        (PrimCollinearRotate
          Geo A C K h)

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  have hAKX :
      Not (PrimCollinear Geo A K X) := by
    intro hAKXcol

    have hKXC :
        PrimCollinear Geo K X C :=
      PrimCollinearCycle
        Geo C K X hCKXcol

    have hAKC' :
        PrimCollinear Geo A K C :=
      hilbert_primCollinear_trans
        Geo
        A K X C
        hKX
        hAKXcol
        hKXC

    exact hAKC hAKC'

  --------------------------------------------------------------------
  -- Triangle KAC is isosceles.
  --------------------------------------------------------------------

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      A C
      hAcircle
      hCcircle

  have hIso :
      Geo.AngleCongruent
        K A C
        K C A :=
    hilbert_isosceles_base_angles
      Geo
      K A C
      hKAC
      hKA_KC

  have hKAC_ACK :
      Geo.AngleCongruent
        K A C
        A C K :=
    (Geo.angle_congruent_reverse_second
      K A C
      K C A).mp
      hIso

  --------------------------------------------------------------------
  -- I.32 on triangle A-C-K, with CK extended through K to X.
  --
  -- It decomposes the exterior angle AKX into
  --
  --   angle CAK  and  angle ACK.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A C K X
        hACK
        hCKX
    with
    ⟨T,
      hATX,
      hCAK_AKT,
      hACK_TKX⟩

  have hATXdata :=
    HilbertOrder.between_incidence
      A T X hATX

  have hAT :
      Ne A T :=
    hATXdata.1

  have hTX :
      Ne T X :=
    hATXdata.2.1

  have hATXcol :
      PrimCollinear Geo A T X :=
    hATXdata.2.2.2.1

  have hKT :
      Ne K T := by
    intro hKT
    subst T

    have hAKXcol :
        PrimCollinear Geo A K X :=
      hATXcol

    exact hAKX hAKXcol

  have hInside :
      HilbertRayMeetsSegment Geo K T A X :=
    ⟨T,
      hATX,
      hilbert_sameRay_refl
        Geo K T hKT.symm⟩

  --------------------------------------------------------------------
  -- Reverse the first remote angle from CAK to KAC.
  --------------------------------------------------------------------

  have hKAC_AKT :
      Geo.AngleCongruent
        K A C
        A K T :=
    (Geo.angle_congruent_reverse_first
      C A K
      A K T).mp
      hCAK_AKT

  --------------------------------------------------------------------
  -- Therefore AKT is congruent to ACK.
  --------------------------------------------------------------------

  have hAKT_KAC :
      Geo.AngleCongruent
        A K T
        K A C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      K A C
      A K T
      hKAC_AKT

  have hAKT_ACK :
      Geo.AngleCongruent
        A K T
        A C K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A K T
      K A C
      A C K
      hAKT_KAC
      hKAC_ACK

  --------------------------------------------------------------------
  -- The second I.32 component is ACK ~= TKX.
  -- Reverse the second angle to obtain ACK ~= XKT.
  --------------------------------------------------------------------

  have hACK_XKT :
      Geo.AngleCongruent
        A C K
        X K T :=
    (Geo.angle_congruent_reverse_second
      A C K
      T K X).mp
      hACK_TKX

  --------------------------------------------------------------------
  -- Hence the two halves of exterior angle AKX are congruent.
  --------------------------------------------------------------------

  have hAKT_XKT :
      Geo.AngleCongruent
        A K T
        X K T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A K T
      A C K
      X K T
      hAKT_ACK
      hACK_XKT

  have hACK_AKT :
      Geo.AngleCongruent
        A C K
        A K T :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K T
      A C K
      hAKT_ACK

  exact
    ⟨T,
      hInside,
      hAKT_XKT,
      hACK_AKT⟩
/- END folded proof support: Crossing_circle_stage19_exterior_central_half_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage20_chord_inner_point_v1.lean -/
/-!
# Forder IV.12 -- stage 20, interior point of a chord

The next order fact in Forder IV.12 is the strict inequality

  KY < KC,

where Y is an interior point of a chord AB and A,B,C lie on a circle
centered at K.

The geometric core is a neutral Book-I theorem:

  an interior point of the base of an isosceles triangle is strictly
  closer to the apex than either endpoint.

This theorem had already appeared later in the XI development.  It is
reproved here independently so the circle theory does not depend on
Book XI.
-/

------------------------------------------------------------------------
-- 1. Neutral Book-I lemma.
------------------------------------------------------------------------

/--
An interior point of the base of an isosceles triangle is strictly
closer to the apex than either endpoint.

If C-H-D and UC ~= UD, then UH < UC.
-/
theorem hilbert_isosceles_base_inner_point_closer_stage20
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (U C Hpt D : Geo.Point)
    (hUCD : Not (PrimCollinear Geo U C D))
    (hCHD : Geo.Between C Hpt D)
    (hUC_UD : Geo.Congruent U C U D) :
    HilbertSegmentLess Geo U Hpt U C := by

  have hCHDdata :=
    HilbertOrder.between_incidence
      C Hpt D hCHD

  have hCH :
      Ne C Hpt :=
    hCHDdata.1

  have hHD :
      Ne Hpt D :=
    hCHDdata.2.1

  have hDH :
      Ne D Hpt :=
    hHD.symm

  have hDHC :
      Geo.Between D Hpt C :=
    hCHDdata.2.2.2.2

  have hCHDcol :
      PrimCollinear Geo C Hpt D :=
    hCHDdata.2.2.2.1

  have hDHCcol :
      PrimCollinear Geo D Hpt C :=
    PrimCollinearSymm
      Geo C Hpt D hCHDcol

  --------------------------------------------------------------------
  -- Triangles U-D-H and U-C-H are nondegenerate.
  --------------------------------------------------------------------

  have hUDH :
      Not (PrimCollinear Geo U D Hpt) := by
    intro hUDHcol

    have hUDC :
        PrimCollinear Geo U D C :=
      hilbert_primCollinear_trans
        Geo
        U D Hpt C
        hDH
        hUDHcol
        hDHCcol

    exact
      hUCD
        (PrimCollinearRotate
          Geo U D C hUDC)

  have hUCH :
      Not (PrimCollinear Geo U C Hpt) := by
    intro hUCHcol

    have hUCDcol :
        PrimCollinear Geo U C D :=
      hilbert_primCollinear_trans
        Geo
        U C Hpt D
        hCH
        hUCHcol
        hCHDcol

    exact hUCD hUCDcol

  have hUHC :
      Not (PrimCollinear Geo U Hpt C) := by
    intro h
    exact
      hUCH
        (PrimCollinearRotate
          Geo U Hpt C h)

  --------------------------------------------------------------------
  -- I.16 in triangle U-D-H, with DH extended through H to C.
  --------------------------------------------------------------------

  have hUDH_UHC :
      HilbertAngleLess Geo
        U D Hpt
        U Hpt C :=
    euclid_proposition_16_second
      Geo
      U D Hpt C
      hUDH
      hDHC

  --------------------------------------------------------------------
  -- I.5 in U-C-D and transport H along the base CD.
  --------------------------------------------------------------------

  have hBase :
      Geo.AngleCongruent
        U C D
        U D C :=
    hilbert_isosceles_base_angles
      Geo
      U C D
      hUCD
      hUC_UD

  have hBaseSymm :
      Geo.AngleCongruent
        U D C
        U C D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      U C D
      U D C
      hBase

  have hRayDHC :
      HilbertSameRay Geo D Hpt C :=
    hilbert_sameRay_of_between
      Geo D Hpt C hDHC

  have hRayCHD :
      HilbertSameRay Geo C Hpt D :=
    hilbert_sameRay_of_between
      Geo C Hpt D hCHD

  have hUDH_eq_UDC :
      Geo.Angle U D Hpt =
      Geo.Angle U D C :=
    hilbert_angle_eq_of_sameRay_second
      Geo D U Hpt C hRayDHC

  have hUCH_eq_UCD :
      Geo.Angle U C Hpt =
      Geo.Angle U C D :=
    hilbert_angle_eq_of_sameRay_second
      Geo C U Hpt D hRayCHD

  have hUCH_UDH :
      Geo.AngleCongruent
        U C Hpt
        U D Hpt := by

    have hUDH_UCH :
        Geo.AngleCongruent
          U D Hpt
          U C Hpt := by
      unfold Geometry.Geo.AngleCongruent
        at hBaseSymm ⊢
      rw [hUDH_eq_UDC, hUCH_eq_UCD]
      exact hBaseSymm

    exact
      Geometry.Geo.angle_congruent_symmetry
        Geo
        U D Hpt
        U C Hpt
        hUDH_UCH

  have hUCH_UHC :
      HilbertAngleLess Geo
        U C Hpt
        U Hpt C :=
    hilbert_angleLess_transport_left
      Geo
      U D Hpt
      U C Hpt
      U Hpt C
      hUDH_UHC
      hUCH
      hUCH_UDH

  --------------------------------------------------------------------
  -- I.19 in triangle U-H-C.
  --------------------------------------------------------------------

  exact
    euclid_proposition_19
      Geo
      U Hpt C
      hUHC
      hUCH_UHC


------------------------------------------------------------------------
-- 2. Interior points of a chord are strictly inside the circle.
------------------------------------------------------------------------

/--
If A and B are distinct points of a circle centered at K, Y lies
strictly between A and B, and K is off the chord AB, then

  KY < KA.

Since KA is a radius, this is the exact synthetic content needed in
Forder IV.12 for "Y is inside the circle".
-/
theorem hilbert_circle_chord_inner_point_inside_stage20
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B Y : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKoff : Not (H.OnLine K chord))
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hAYB : Geo.Between A Y B) :
    HilbertSegmentLess Geo K Y K A := by

  have hKAB :
      Not (PrimCollinear Geo K A B) := by
    intro h

    have hKline :
        H.OnLine K chord :=
      hilbert_collinear_on_line
        Geo
        A B K
        chord
        hAB
        hAchord
        hBchord
        (PrimCollinearCycle
          Geo K A B h)

    exact hKoff hKline

  have hKA_KB :
      Geo.Congruent K A K B :=
    hilbert_circle_center_congruent
      Geo
      K R
      A B
      hAcircle
      hBcircle

  exact
    hilbert_isosceles_base_inner_point_closer_stage20
      Geo
      K A Y B
      hKAB
      hAYB
      hKA_KB
/- END folded proof support: Crossing_circle_stage20_chord_inner_point_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage21_axis_chord_order_v1.lean -/
/-!
# Forder IV.12 -- stage 21, axis/chord intersection order

This is the order step written almost verbatim in Forder's proof.

Suppose C and K lie on the same side of chord AB, while Y lies on
that chord and C,K,Y are collinear.  If

  KY < KC,

then the only possible collinear order is

  C-K-Y.

Indeed:

* K-C-Y would imply KC < KY, contradicting KY < KC;
* C-Y-K would make segment CK meet the chord at Y, contradicting
  that C and K are on the same side of the chord.

No circle-specific axiom is used here beyond the strict segment
comparison supplied by the previous stage.
-/

/--
If C,K are on the same side of a line, Y lies on that line,
C,K,Y are collinear, and KY < KC, then K lies strictly between C,Y.
-/
theorem hilbert_sameSide_intersection_order_stage21
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K C Y : Geo.Point)
    (chord : Geo.Line)
    (hKC : Ne K C)
    (hYchord : H.OnLine Y chord)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKYcol : PrimCollinear Geo C K Y)
    (hKY_KC : HilbertSegmentLess Geo K Y K C) :
    Geo.Between C K Y := by

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hCY :
      Ne C Y := by
    intro hCY
    subst Y
    exact hCoff hYchord

  have hKY :
      Ne K Y := by
    intro hKY
    subst Y
    exact hKoff hYchord

  rcases
      hilbert_between_trichotomy
        Geo
        C K Y
        hKC.symm
        hKY
        hCY
        hCKYcol
    with
    hCKY | hKCY | hCYK

  --------------------------------------------------------------------
  -- Desired order.
  --------------------------------------------------------------------

  · exact hCKY

  --------------------------------------------------------------------
  -- K-C-Y would force KC < KY, contradicting KY < KC.
  --------------------------------------------------------------------

  · have hKC_KY :
        HilbertSegmentLess Geo K C K Y :=
      hilbert_segmentLess_of_between
        Geo
        K C Y
        hKCY

    exact
      False.elim
        ((hilbert_segmentLess_asymm
            Geo
            K Y
            K C
            hKY_KC)
          hKC_KY)

  --------------------------------------------------------------------
  -- C-Y-K would make C and K opposite sides of the chord.
  --------------------------------------------------------------------

  · have hOppCK :
        HilbertOppositeSide Geo C K chord :=
      ⟨hCoff,
       hKoff,
       ⟨Y,
        hCYK,
        hYchord⟩⟩

    exact
      False.elim
        ((hilbert_oppositeSide_not_sameSide
            Geo
            C K
            chord
            hOppCK)
          hSameCK)


------------------------------------------------------------------------
-- Circle-specialized wrapper used in IV.12.
------------------------------------------------------------------------

/--
If Y is an interior point of chord AB and is collinear with the center
K and a circle point C lying on the same side of AB as K, then

  C-K-Y.

The strict inequality KY < KC comes from stage 20.
-/
theorem hilbert_circle_chord_axis_order_stage21
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C Y : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hAYB : Geo.Between A Y B)
    (hCKYcol : PrimCollinear Geo C K Y) :
    Geo.Between C K Y := by

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hYchord :
      H.OnLine Y chord :=
    hilbert_between_on_line
      Geo
      A Y B
      chord
      hAchord
      hBchord
      hAYB

  have hKC :
      Ne K C :=
    hilbert_circle_center_ne_point_of_two_distinct_stage14
      Geo
      K R A B C
      hAB
      hAcircle
      hBcircle
      hCcircle

  have hKY_KA :
      HilbertSegmentLess Geo K Y K A :=
    hilbert_circle_chord_inner_point_inside_stage20
      Geo
      K R A B Y
      chord
      hAB
      hAchord
      hBchord
      hKoff
      hAcircle
      hBcircle
      hAYB

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      A C
      hAcircle
      hCcircle

  have hKY_KC :
      HilbertSegmentLess Geo K Y K C :=
    hilbert_segmentLess_congruent_right
      Geo
      K Y
      K A
      K C
      hKY_KA
      hKA_KC

  exact
    hilbert_sameSide_intersection_order_stage21
      Geo
      K C Y
      chord
      hKC
      hYchord
      hSameCK
      hCKYcol
      hKY_KC
/- END folded proof support: Crossing_circle_stage21_axis_chord_order_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage22_IV12_addition_configuration_v3.lean -/
/-!
# Forder IV.12 -- stage 22, addition-case geometry

This file isolates the incidence/order geometry of Forder IV.12 in the
case where A and B lie on opposite sides of the axis KX.

Assume

  C-K-X

and the line KX meets the chord AB at Y.

Since C and K are on the same side of AB and Y is an interior point of
AB, stage 21 gives

  C-K-Y.

Therefore X and Y lie on the same ray from K, while K and Y lie on the
same ray from C.  Consequently the same intersection point Y proves

  ray KX is interior to angle AKB,
  ray CK is interior to angle ACB.

No angle congruence is proved here; this is only the exact order
configuration needed by the next stage.
-/

------------------------------------------------------------------------
-- 1. Two points beyond the same middle point determine the same ray.
------------------------------------------------------------------------

/--
If C-K-X and C-K-Y, then X and Y lie on the same ray from K.
-/
theorem hilbert_sameRay_beyond_common_middle_stage22
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (C K X Y : Geo.Point)
    (hCKX : Geo.Between C K X)
    (hCKY : Geo.Between C K Y) :
    HilbertSameRay Geo K X Y := by

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKYdata :=
    HilbertOrder.between_incidence
      C K Y hCKY

  have hKY :
      Ne K Y :=
    hCKYdata.2.1

  have hRayCKX :
      HilbertSameRay Geo C K X :=
    hilbert_sameRay_of_between
      Geo C K X hCKX

  have hRayCKY :
      HilbertSameRay Geo C K Y :=
    hilbert_sameRay_of_between
      Geo C K Y hCKY

  have hRayCXY :
      HilbertSameRay Geo C X Y :=
    bookZero_36_ray3
      Geo
      C K X Y
      hRayCKX
      hRayCKY

  rcases
      hilbert_sameRay_cases
        Geo
        C X Y
        hRayCXY
    with
    hXY | hOrder

  --------------------------------------------------------------------
  -- X = Y.
  --------------------------------------------------------------------

  · subst Y
    exact
      hilbert_sameRay_refl
        Geo K X hKX.symm

  --------------------------------------------------------------------
  -- C-X-Y or C-Y-X.
  --------------------------------------------------------------------

  · rcases hOrder with hCXY | hCYX

    · have hKXY :
          Geo.Between K X Y :=
        (hilbert_between_inner_trans
          Geo
          C K X Y
          hCKX
          hCXY).1

      exact
        hilbert_sameRay_of_between
          Geo K X Y hKXY

    · have hKYX :
          Geo.Between K Y X :=
        (hilbert_between_inner_trans
          Geo
          C K Y X
          hCKY
          hCYX).1

      exact
        hilbert_sameRay_symm
          Geo
          K Y X
          (hilbert_sameRay_of_between
            Geo K Y X hKYX)


------------------------------------------------------------------------
-- 2. Forder IV.12, opposite-side axis configuration.
------------------------------------------------------------------------

/--
Addition-case geometry for Forder IV.12.

The axis through K and X separates A and B.  Its intersection Y with
AB lies beyond K from C, hence:

* ray KX meets the open segment AB;
* ray CK meets the open segment AB.

These are exactly the two interior-ray witnesses needed to decompose
the central angle AKB and the inscribed angle ACB.
-/
theorem hilbert_forder_IV12_addition_configuration_stage22
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (chord axis : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKX : Geo.Between C K X)
    (hOppAB : HilbertOppositeSide Geo A B axis) :
    exists Y : Geo.Point,
      Geo.Between A Y B /\
      Geo.Between C K Y /\
      HilbertRayMeetsSegment Geo K X A B /\
      HilbertRayMeetsSegment Geo C K A B := by

  --------------------------------------------------------------------
  -- The axis meets the open chord AB at Y.
  --------------------------------------------------------------------

  rcases hOppAB.2.2 with
    ⟨Y, hAYB, hYaxis⟩

  --------------------------------------------------------------------
  -- C lies on the same axis because C-K-X.
  --------------------------------------------------------------------

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX, hCline, hKline, hXline⟩

  have hEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hEq]
    exact hCline

  have hCKYcol :
      PrimCollinear Geo C K Y :=
    ⟨axis,
      hCaxis,
      hKaxis,
      hYaxis⟩

  --------------------------------------------------------------------
  -- Stage 21 gives the decisive order C-K-Y.
  --------------------------------------------------------------------

  have hCKY :
      Geo.Between C K Y :=
    hilbert_circle_chord_axis_order_stage21
      Geo
      K R A B C Y
      chord
      hAB
      hAchord
      hBchord
      hAcircle
      hBcircle
      hCcircle
      hSameCK
      hAYB
      hCKYcol

  --------------------------------------------------------------------
  -- Hence X and Y lie on the same ray from K.
  --------------------------------------------------------------------

  have hRayKXY :
      HilbertSameRay Geo K X Y :=
    hilbert_sameRay_beyond_common_middle_stage22
      Geo
      C K X Y
      hCKX
      hCKY

  have hInsideCentral :
      HilbertRayMeetsSegment Geo K X A B :=
    ⟨Y,
      hAYB,
      hRayKXY⟩

  --------------------------------------------------------------------
  -- And K and Y lie on the same ray from C.
  --------------------------------------------------------------------

  have hRayCKY :
      HilbertSameRay Geo C K Y :=
    hilbert_sameRay_of_between
      Geo C K Y hCKY

  have hInsideInscribed :
      HilbertRayMeetsSegment Geo C K A B :=
    ⟨Y,
      hAYB,
      hRayCKY⟩

  exact
    ⟨Y,
      hAYB,
      hCKY,
      hInsideCentral,
      hInsideInscribed⟩
/- END folded proof support: Crossing_circle_stage22_IV12_addition_configuration_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage23_angle_bisector_interior_v2.lean -/
/-!
# Forder IV.12 -- stage 23, interior angle bisector

The ordinary production Proposition I.9 returns a point on a bisecting
ray, but its public conclusion does not retain the fact that this ray is
strictly interior to the original angle.

For IV.12 we need both pieces of data at once:

* the two half-angles are congruent;
* the bisecting ray meets the open segment joining the two boundary
  points.

The proof below is the neutral Hilbert reconstruction already used
elsewhere in the project: segment construction, midpoint existence, SSS,
and same-ray transport.  It introduces no new axiom and no numerical
angle measure.
-/

/--
Every nondegenerate angle has a bisecting ray which meets the open
segment joining one point on each boundary ray.
-/
theorem hilbert_angle_bisector_with_interior_stage23
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O X Y : Geo.Point)
    (hXOY : Not (PrimCollinear Geo X O Y)) :
    exists M : Geo.Point,
      HilbertRayMeetsSegment Geo O M X Y /\
      Geo.AngleCongruent X O M M O Y := by

  have hOXY :
      Not (PrimCollinear Geo O X Y) := by
    intro h
    exact
      hXOY
        (PrimCollinearSwap
          Geo O X Y h)

  have hOX :
      Ne O X :=
    hilbert_noncollinear_ne_first
      Geo O X Y hOXY

  --------------------------------------------------------------------
  -- Lay off OD ~= OY on ray OX.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O Y
        O X
        hOX
    with
    ⟨D, hRayXD, hOD_OY⟩

  have hOD :
      Ne O D :=
    hRayXD.2.1.symm

  have hOXD :
      PrimCollinear Geo O X D :=
    hRayXD.2.2.1

  have hODY :
      Not (PrimCollinear Geo O D Y) := by
    intro hODY

    have hXOD :
        PrimCollinear Geo X O D :=
      PrimCollinearSwap
        Geo O X D hOXD

    have hXOY' :
        PrimCollinear Geo X O Y :=
      hilbert_primCollinear_trans
        Geo
        X O D Y
        hOD
        hXOD
        hODY

    exact hXOY hXOY'

  have hDY :
      Ne D Y := by
    intro h
    subst D
    exact hOXY hOXD

  --------------------------------------------------------------------
  -- Let M be the midpoint of DY.
  --------------------------------------------------------------------

  rcases
      HilbertMidpointExists
        Geo D Y hDY
    with
    ⟨M, hMid⟩

  have hDMY :
      Geo.Between D M Y :=
    hMid.1

  have hDM_MY :
      Geo.Congruent D M M Y :=
    hMid.2

  have hDM :
      Ne D M :=
    (HilbertOrder.between_incidence
      D M Y hDMY).1

  have hDMYcol :
      PrimCollinear Geo D M Y :=
    (HilbertOrder.between_incidence
      D M Y hDMY).2.2.2.1

  have hODM :
      Not (PrimCollinear Geo O D M) := by
    intro hODM

    have hODY' :
        PrimCollinear Geo O D Y :=
      hilbert_primCollinear_trans
        Geo
        O D M Y
        hDM
        hODM
        hDMYcol

    exact hODY hODY'

  have hMO :
      Ne M O := by
    intro h
    subst M

    exact
      hODY
        (PrimCollinearSwap
          Geo D O Y hDMYcol)

  --------------------------------------------------------------------
  -- SSS on ODM and OYM.
  --------------------------------------------------------------------

  have hDM_YM :
      Geo.Congruent D M Y M :=
    (Geo.congruent_reverse_second
      D M M Y).mp hDM_MY

  have hOM :
      Geo.Congruent O M O M :=
    hilbert_congruent_reflexive
      Geo O M

  have hSSS :=
    HilbertSSS
      Geo
      O D M
      O Y M
      hODM
      hOD_OY
      hDM_YM
      hOM

  have hAngleDOM_YOM :
      Geo.AngleCongruent D O M Y O M :=
    hSSS.2.angleA

  have hAngleDOM_MOY :
      Geo.AngleCongruent D O M M O Y :=
    (Geo.angle_congruent_reverse_second
      D O M Y O M).mp
      hAngleDOM_YOM

  --------------------------------------------------------------------
  -- Replace the constructed ray OD by the original ray OX.
  --------------------------------------------------------------------

  have hRayDX :
      HilbertSameRay Geo O D X :=
    hilbert_sameRay_symm
      Geo O X D hRayXD

  have hAngleEq :
      Geo.Angle D O M =
      Geo.Angle X O M :=
    hilbert_angle_eq_of_sameRay_first
      Geo O D X M hRayDX

  have hBisect :
      Geo.AngleCongruent X O M M O Y := by
    unfold Geometry.Geo.AngleCongruent at hAngleDOM_MOY
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleEq]
    exact hAngleDOM_MOY

  --------------------------------------------------------------------
  -- Retain the interior-ray information.
  --------------------------------------------------------------------

  have hYOX :
      Not (PrimCollinear Geo Y O X) := by
    intro h

    have hOXY' :
        PrimCollinear Geo O X Y :=
      PrimCollinearCycle
        Geo Y O X h

    exact hOXY hOXY'

  have hYO :
      Ne Y O :=
    hilbert_noncollinear_ne_first
      Geo Y O X hYOX

  have hYY :
      HilbertSameRay Geo O Y Y :=
    hilbert_sameRay_refl
      Geo O Y hYO

  have hMeetDY :
      HilbertRayMeetsSegment Geo O M D Y :=
    ⟨M,
      hDMY,
      hilbert_sameRay_refl
        Geo O M hMO⟩

  have hDOY :
      Not (PrimCollinear Geo D O Y) := by
    intro h
    exact
      hODY
        (PrimCollinearSwap
          Geo D O Y h)

  have hMeetXY :
      HilbertRayMeetsSegment Geo O M X Y :=
    hilbert_ray_meets_segment_sameRays
      Geo
      O M
      D Y
      X Y
      hMeetDY
      hRayDX
      hYY
      hDOY
      hXOY

  exact
    ⟨M,
      hMeetXY,
      hBisect⟩
/- END folded proof support: Crossing_circle_stage23_angle_bisector_interior_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage24_angle_component_swap_v1.lean -/
/-!
# Forder IV.12 -- stage 24, swapping two adjacent angle components

Forder's proof of IV.12 uses commutativity of angle measure.

For the local configuration needed here, full angular-measure arithmetic
is unnecessary.  If OD is an interior ray of angle AOB, then the two
adjacent components

  angle AOD, angle DOB

can be realized in the opposite order inside the same whole angle.

The proof is entirely synthetic: reverse the whole angle to BOA,
transport its decomposition back into AOB, and read off the two
transported components.

This is the local replacement for the commutativity step used by
Forder.
-/

/--
Swap the two components of an interior-angle decomposition.

If OD is interior to angle AOB, there exists an interior ray OE such
that

  angle AOE ~= angle BOD,
  angle BOE ~= angle AOD.

Thus the same whole angle is decomposed with the two component
magnitudes in the opposite order.
-/
theorem hilbert_angleDecomposition_swap_components_stage24
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D A B) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      Geo.AngleCongruent
        A O E
        B O D /\
      Geo.AngleCongruent
        B O E
        A O D := by

  --------------------------------------------------------------------
  -- Reverse the whole angle and the crossed segment.
  --------------------------------------------------------------------

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D A B
      hInsideD

  --------------------------------------------------------------------
  -- BOA is congruent to AOB by reversal of the first angle.
  --------------------------------------------------------------------

  have hRefl :
      Geo.AngleCongruent
        A O B
        A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hWhole :
      Geo.AngleCongruent
        B O A
        A O B :=
    (Geo.angle_congruent_reverse_first
      A O B
      A O B).mp
      hRefl

  --------------------------------------------------------------------
  -- Transport the reversed decomposition back into the same whole
  -- angle.  The left and right components are thereby exchanged.
  --------------------------------------------------------------------

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        O B A D
        A O B
        hBOA
        hAOB
        hInsideDrev
        hWhole
    with
    ⟨E,
      hInsideE,
      hParts⟩

  have hAOD_BOE :
      Geo.AngleCongruent
        A O D
        B O E :=
    hParts.1

  have hBOD_AOE :
      Geo.AngleCongruent
        B O D
        A O E :=
    hParts.2

  have hAOE_BOD :
      Geo.AngleCongruent
        A O E
        B O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B O D
      A O E
      hBOD_AOE

  have hBOE_AOD :
      Geo.AngleCongruent
        B O E
        A O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O D
      B O E
      hAOD_BOE

  exact
    ⟨E,
      hInsideE,
      hAOE_BOD,
      hBOE_AOD⟩
/- END folded proof support: Crossing_circle_stage24_angle_component_swap_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage25_nested_interior_rays_v1.lean -/
/-!
# Forder IV.12 -- stage 25, nested interior rays

These are neutral angle-order lemmas needed to assemble the local
four-block decomposition

  alpha, alpha, beta, beta.

They were previously used in the Book XI development, but the circle
kernel must not depend on the Book XI interface.  We therefore record
the same neutral arguments here at the lower layer.
-/

------------------------------------------------------------------------
-- 1. Left-hand nesting.
------------------------------------------------------------------------

/--
If OE is interior to angle AOB and OT is interior to angle AOE,
then OT is interior to angle AOB.
-/
theorem hilbert_angleDecomposition_nested_inside_left_stage25
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B E T : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A E) :
    HilbertRayMeetsSegment Geo O T A B := by

  have hAOE_AOB :
      HilbertAngleLess Geo A O E A O B :=
    hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    hAOE_AOB.1

  have hAOT_AOE :
      HilbertAngleLess Geo A O T A O E :=
    hilbert_interior_angle_less
      Geo
      O T A E
      hAOE
      hInsideT

  have hAOT_AOB :
      HilbertAngleLess Geo A O T A O B :=
    hilbert_angleLess_trans
      Geo
      A O T
      A O E
      A O B
      hAOT_AOE
      hAOE_AOB

  have hAO :
      O ≠ A :=
    hilbert_noncollinear_ne_first
      Geo O A B
      (by
        intro h
        exact
          hAOB
            (PrimCollinearSwap
              Geo O A B h))

  rcases
      HilbertPlaneIncidence.line_through
        O A hAO
    with
    ⟨lineOA,
      hOlineOA,
      hAlineOA⟩

  have hEOA :
      Not (PrimCollinear Geo E O A) := by
    intro h
    exact
      hAOE
        (PrimCollinearSymm
          Geo E O A h)

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T E A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A E
      hInsideT

  have hTESameOA :
      HilbertSameSide Geo T E lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O T E A
      lineOA
      hOlineOA
      hAlineOA
      hEOA
      hInsideTrev

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hEBSameOA :
      HilbertSameSide Geo E B lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E B A
      lineOA
      hOlineOA
      hAlineOA
      hBOA
      hInsideErev

  have hTBSameOA :
      HilbertSameSide Geo T B lineOA :=
    hilbert_sameSide_trans
      Geo
      T E B
      lineOA
      hTESameOA
      hEBSameOA

  exact
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      T B O A
      lineOA
      hOlineOA
      hAlineOA
      hAO
      hTBSameOA
      hAOT_AOB


------------------------------------------------------------------------
-- 2. Right-hand nesting.
------------------------------------------------------------------------

/--
If OE is interior to angle AOB and OT is interior to angle EOB,
then OT is interior to angle AOB.
-/
theorem hilbert_angleDecomposition_nested_inside_right_stage25
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B E T : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T E B) :
    HilbertRayMeetsSegment Geo O T A B := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T B E :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T E B
      hInsideT

  have hNestedRev :
      HilbertRayMeetsSegment Geo O T B A :=
    hilbert_angleDecomposition_nested_inside_left_stage25
      Geo
      B O A E T
      hBOA
      hInsideErev
      hInsideTrev

  exact
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T B A
      hNestedRev
/- END folded proof support: Crossing_circle_stage25_nested_interior_rays_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage26_middle_divider_v1.lean -/
/-!
# Forder IV.12 -- stage 26, middle divider

This stage promotes two neutral angle-order facts to the lower circle
development:

1. complementary order reversal for two interior rays;
2. the nested parent-divider lemma.

The final corollary is exactly the order fact needed in the four-block
construction:

  T is inside A-O-E,
  E is inside A-O-B,
  U is inside E-O-B

implies

  E is inside T-O-U.

No circle-specific hypothesis occurs in these lemmas.
-/

------------------------------------------------------------------------
-- 1. Complementary order reversal.
------------------------------------------------------------------------

/--
For two interior rays of the same proper angle, strict order of the
left components forces the opposite strict order of the right
components.
-/
theorem hilbert_angleDecomposition_complement_order_reverse_stage26
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O X C D E : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideE : HilbertRayMeetsSegment Geo O E X C)
    (hLessFirst : HilbertAngleLess Geo X O D X O E) :
    HilbertAngleLess Geo C O E C O D := by

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo
      O D C X
      hCOX
      hInsideDrev).1

  have hCOE :
      Not (PrimCollinear Geo C O E) :=
    (hilbert_interior_angle_less
      Geo
      O E C X
      hCOX
      hInsideErev).1

  rcases
      angle_trichotomy
        Geo
        C O E
        C O D
        hCOE
        hCOD
    with hEq | hOrder

  · have hRight :
        Geo.AngleCongruent C O D C O E :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        C O E
        C O D
        hEq

    have hWhole :
        Geo.AngleCongruent X O C X O C :=
      Geometry.Geo.angle_congruent_reflexive
        Geo X O C

    have hLeftEq :
        Geo.AngleCongruent X O D X O E :=
      hilbert_angleDecomposition_angle_subtraction
        Geo
        O X C D
        X O C E
        hXOC
        hXOC
        hInsideD
        hInsideE
        hWhole
        hRight

    have hLeftEqSymm :
        Geo.AngleCongruent X O E X O D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        X O E
        hLeftEq

    have hCycle :
        HilbertAngleLess Geo X O D X O D :=
      hilbert_angleLess_transport_right
        Geo
        X O D
        X O E
        X O D
        hLessFirst
        hLessFirst.1
        hLeftEqSymm

    exact
      False.elim
        ((hilbert_angleLess_irrefl
          Geo X O D)
          hCycle)

  · rcases hOrder with hWanted | hForbidden

    · exact hWanted

    · exact
        False.elim
          (hilbert_angleDecomposition_two_component_less_impossible
            Geo
            O X C D E
            hXOC
            hInsideD
            hInsideE
            hLessFirst
            hForbidden)


------------------------------------------------------------------------
-- 2. Parent divider.
------------------------------------------------------------------------

/--
If OE is interior to angle XOC and OZ is interior to angle EOC,
then OE is interior to angle XOZ.
-/
theorem hilbert_angleDecomposition_nested_parent_divider_stage26
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (X O C E Z : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hInsideE : HilbertRayMeetsSegment Geo O E X C)
    (hInsideZ : HilbertRayMeetsSegment Geo O Z E C) :
    HilbertRayMeetsSegment Geo O E X Z := by

  have hInsideZwhole :
      HilbertRayMeetsSegment Geo O Z X C :=
    hilbert_angleDecomposition_nested_inside_right_stage25
      Geo
      X O C E Z
      hXOC
      hInsideE
      hInsideZ

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm Geo C O X h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hInsideZrev :
      HilbertRayMeetsSegment Geo O Z C E :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O Z E C
      hInsideZ

  have hCOE :
      Not (PrimCollinear Geo C O E) :=
    (hilbert_interior_angle_less
      Geo
      O E C X
      hCOX
      hInsideErev).1

  have hCOZ_COE :
      HilbertAngleLess Geo C O Z C O E :=
    hilbert_interior_angle_less
      Geo
      O Z C E
      hCOE
      hInsideZrev

  have hInsideZwholeRev :
      HilbertRayMeetsSegment Geo O Z C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O Z X C
      hInsideZwhole

  have hXOE_XOZ :
      HilbertAngleLess Geo X O E X O Z :=
    hilbert_angleDecomposition_complement_order_reverse_stage26
      Geo
      O C X Z E
      hCOX
      hInsideZwholeRev
      hInsideErev
      hCOZ_COE

  have hOX :
      O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo
      O X C
      (by
        intro h
        exact
          hXOC
            (PrimCollinearSwap
              Geo O X C h))

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX
    with
    ⟨lineOX,
      hOlineOX,
      hXlineOX⟩

  have hEDSame :
      HilbertSameSide Geo E C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideErev

  have hZCSame :
      HilbertSameSide Geo Z C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O Z C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideZwholeRev

  have hCZSame :
      HilbertSameSide Geo C Z lineOX :=
    hilbert_sameSide_symm
      Geo
      Z C
      lineOX
      hZCSame

  have hEZSame :
      HilbertSameSide Geo E Z lineOX :=
    hilbert_sameSide_trans
      Geo
      E C Z
      lineOX
      hEDSame
      hCZSame

  exact
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      E Z O X
      lineOX
      hOlineOX
      hXlineOX
      hOX
      hEZSame
      hXOE_XOZ


------------------------------------------------------------------------
-- 3. The middle-divider form needed for IV.12.
------------------------------------------------------------------------

/--
Suppose the rays occur in the nested configuration

  A ... T ... E ... U ... B

inside the proper angle AOB, expressed synthetically by

* OE interior to AOB,
* OT interior to AOE,
* OU interior to EOB.

Then OE is interior to angle TOU.
-/
theorem hilbert_angleDecomposition_middle_divider_stage26
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B E T U : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A E)
    (hInsideU : HilbertRayMeetsSegment Geo O U E B) :
    HilbertRayMeetsSegment Geo O E T U := by

  have hInsideE_AU :
      HilbertRayMeetsSegment Geo O E A U :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      A O B E U
      hAOB
      hInsideE
      hInsideU

  have hInsideE_UA :
      HilbertRayMeetsSegment Geo O E U A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A U
      hInsideE_AU

  have hInsideT_EA :
      HilbertRayMeetsSegment Geo O T E A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A E
      hInsideT

  have hInsideUwhole :
      HilbertRayMeetsSegment Geo O U A B :=
    hilbert_angleDecomposition_nested_inside_right_stage25
      Geo
      A O B E U
      hAOB
      hInsideE
      hInsideU

  have hAOU :
      Not (PrimCollinear Geo A O U) :=
    (hilbert_interior_angle_less
      Geo
      O U A B
      hAOB
      hInsideUwhole).1

  have hUOA :
      Not (PrimCollinear Geo U O A) := by
    intro h
    exact
      hAOU
        (PrimCollinearSymm
          Geo U O A h)

  have hInsideE_UT :
      HilbertRayMeetsSegment Geo O E U T :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      U O A E T
      hUOA
      hInsideE_UA
      hInsideT_EA

  exact
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E U T
      hInsideE_UT
/- END folded proof support: Crossing_circle_stage26_middle_divider_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage27_IV12_addition_case_v2.lean -/
/-!
# Forder IV.12 -- stage 27, complete addition case

This file closes the additive branch of Forder IV.12 synthetically.

The abstract core starts with an interior divider OX of angle AOB and
two local bisectors

  OT inside AOX,
  OU inside XOB,

with

  AOT ~= XOT,
  BOU ~= XOU.

The middle angle TOU is decomposed by OX. Stage 24 swaps its two
components and produces a ray OE. Stages 25--26 then recover the exact
nested-ray order needed to prove

  AOE ~= BOE.

The circle specialization applies this to the two local stage-19
constructions and finally compares the decomposition of ACB through CK
with the decomposition of AKE through KT.

No numerical angular measure is used.
-/

------------------------------------------------------------------------
-- 1. Abstract four-block rearrangement
------------------------------------------------------------------------

/--
Synthetic rearrangement

  alpha, alpha, beta, beta
      -> alpha, beta | alpha, beta.

The returned ray OE bisects the whole angle AOB.  The theorem also
returns the nesting data used later, and records that the second
component TOE is congruent to BOU.
-/
theorem hilbert_angleDecomposition_double_sum_bisector_stage27
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B X T U : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideX : HilbertRayMeetsSegment Geo O X A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A X)
    (hInsideU : HilbertRayMeetsSegment Geo O U X B)
    (hLeftHalf :
      Geo.AngleCongruent
        A O T
        X O T)
    (hRightHalf :
      Geo.AngleCongruent
        B O U
        X O U) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      HilbertRayMeetsSegment Geo O T A E /\
      HilbertRayMeetsSegment Geo O U E B /\
      Geo.AngleCongruent A O E B O E /\
      Geo.AngleCongruent T O E B O U := by

  --------------------------------------------------------------------
  -- Properness of the local left configuration.
  --------------------------------------------------------------------

  have hAOX :
      Not (PrimCollinear Geo A O X) :=
    (hilbert_interior_angle_less
      Geo
      O X A B
      hAOB
      hInsideX).1

  have hXOA :
      Not (PrimCollinear Geo X O A) := by
    intro h
    exact
      hAOX
        (PrimCollinearSymm
          Geo X O A h)

  have hInsideT_XA :
      HilbertRayMeetsSegment Geo O T X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A X
      hInsideT

  have hXOT :
      Not (PrimCollinear Geo X O T) :=
    (hilbert_interior_angle_less
      Geo
      O T X A
      hXOA
      hInsideT_XA).1

  have hTOX :
      Not (PrimCollinear Geo T O X) := by
    intro h
    exact
      hXOT
        (PrimCollinearSymm
          Geo T O X h)

  --------------------------------------------------------------------
  -- X is interior to the middle angle TOU.
  --------------------------------------------------------------------

  have hInsideX_TU :
      HilbertRayMeetsSegment Geo O X T U :=
    hilbert_angleDecomposition_middle_divider_stage26
      Geo
      A O B X T U
      hAOB
      hInsideX
      hInsideT
      hInsideU

  --------------------------------------------------------------------
  -- The middle angle TOU is proper.
  --
  -- If T,O,U were collinear, the witness line of the ray OX would
  -- meet the line TU both at O and at the interior intersection H.
  -- This would force T,O,X collinear, contradicting hTOX.
  --------------------------------------------------------------------

  have hTOU :
      Not (PrimCollinear Geo T O U) := by
    intro hTOUcol

    rcases hInsideX_TU with
      ⟨J,
        hTJU,
        hRayOXJ⟩

    have hTJUdata :=
      HilbertOrder.between_incidence
        T J U hTJU

    have hTU :
        Ne T U :=
      hTJUdata.2.2.1

    have hTJUcol :
        PrimCollinear Geo T J U :=
      hTJUdata.2.2.2.1

    have hOTU :
        PrimCollinear Geo O T U :=
      PrimCollinearSwap
        Geo T O U hTOUcol

    have hTUJ :
        PrimCollinear Geo T U J :=
      PrimCollinearRotate
        Geo T J U hTJUcol

    have hOTJ :
        PrimCollinear Geo O T J :=
      hilbert_primCollinear_trans
        Geo
        O T U J
        hTU
        hOTU
        hTUJ

    have hTOJ :
        PrimCollinear Geo T O J :=
      PrimCollinearSwap
        Geo O T J hOTJ

    have hOJ :
        Ne O J :=
      hRayOXJ.2.1.symm

    have hOJX :
        PrimCollinear Geo O J X :=
      PrimCollinearRotate
        Geo O X J hRayOXJ.2.2.1

    have hTOXcol :
        PrimCollinear Geo T O X :=
      hilbert_primCollinear_trans
        Geo
        T O J X
        hOJ
        hTOJ
        hOJX

    exact hTOX hTOXcol

  --------------------------------------------------------------------
  -- Swap the two components of TOU around X.
  --------------------------------------------------------------------

  rcases
      hilbert_angleDecomposition_swap_components_stage24
        Geo
        O T U X
        hTOU
        hInsideX_TU
    with
    ⟨E,
      hInsideE_TU,
      hTOE_UOX,
      hUOE_TOX⟩

  --------------------------------------------------------------------
  -- Promote U and T through the nested configurations.
  --------------------------------------------------------------------

  have hInsideU_AB :
      HilbertRayMeetsSegment Geo O U A B :=
    hilbert_angleDecomposition_nested_inside_right_stage25
      Geo
      A O B X U
      hAOB
      hInsideX
      hInsideU

  have hAOU :
      Not (PrimCollinear Geo A O U) :=
    (hilbert_interior_angle_less
      Geo
      O U A B
      hAOB
      hInsideU_AB).1

  have hInsideX_AU :
      HilbertRayMeetsSegment Geo O X A U :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      A O B X U
      hAOB
      hInsideX
      hInsideU

  have hInsideT_AU :
      HilbertRayMeetsSegment Geo O T A U :=
    hilbert_angleDecomposition_nested_inside_left_stage25
      Geo
      A O U X T
      hAOU
      hInsideX_AU
      hInsideT

  have hInsideE_AU :
      HilbertRayMeetsSegment Geo O E A U :=
    hilbert_angleDecomposition_nested_inside_right_stage25
      Geo
      A O U T E
      hAOU
      hInsideT_AU
      hInsideE_TU

  have hInsideE_AB :
      HilbertRayMeetsSegment Geo O E A B :=
    hilbert_angleDecomposition_nested_inside_left_stage25
      Geo
      A O B U E
      hAOB
      hInsideU_AB
      hInsideE_AU

  have hInsideT_AE :
      HilbertRayMeetsSegment Geo O T A E :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      A O U T E
      hAOU
      hInsideT_AU
      hInsideE_TU

  --------------------------------------------------------------------
  -- Symmetric nesting on the B side gives U inside EOB.
  --------------------------------------------------------------------

  have hInsideT_AB :
      HilbertRayMeetsSegment Geo O T A B :=
    hilbert_angleDecomposition_nested_inside_left_stage25
      Geo
      A O B X T
      hAOB
      hInsideX
      hInsideT

  have hInsideT_BA :
      HilbertRayMeetsSegment Geo O T B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A B
      hInsideT_AB

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hBOT :
      Not (PrimCollinear Geo B O T) :=
    (hilbert_interior_angle_less
      Geo
      O T B A
      hBOA
      hInsideT_BA).1

  have hTOB :
      Not (PrimCollinear Geo T O B) := by
    intro h
    exact
      hBOT
        (PrimCollinearSymm
          Geo T O B h)

  have hInsideX_BA :
      HilbertRayMeetsSegment Geo O X B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O X A B
      hInsideX

  have hInsideX_BT :
      HilbertRayMeetsSegment Geo O X B T :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      B O A X T
      hBOA
      hInsideX_BA
      hInsideT_XA

  have hInsideX_TB :
      HilbertRayMeetsSegment Geo O X T B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O X B T
      hInsideX_BT

  have hInsideU_TB :
      HilbertRayMeetsSegment Geo O U T B :=
    hilbert_angleDecomposition_nested_inside_right_stage25
      Geo
      T O B X U
      hTOB
      hInsideX_TB
      hInsideU

  have hInsideU_BT :
      HilbertRayMeetsSegment Geo O U B T :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O U T B
      hInsideU_TB

  have hInsideE_UT :
      HilbertRayMeetsSegment Geo O E U T :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E T U
      hInsideE_TU

  have hInsideU_BE :
      HilbertRayMeetsSegment Geo O U B E :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      B O T U E
      hBOT
      hInsideU_BT
      hInsideE_UT

  have hInsideU_EB :
      HilbertRayMeetsSegment Geo O U E B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O U B E
      hInsideU_BE

  --------------------------------------------------------------------
  -- Component congruences after the middle swap.
  --------------------------------------------------------------------

  have hEOU_TOX :
      Geo.AngleCongruent
        E O U
        T O X :=
    (Geo.angle_congruent_reverse_first
      U O E
      T O X).mp
      hUOE_TOX

  have hEOU_XOT :
      Geo.AngleCongruent
        E O U
        X O T :=
    (Geo.angle_congruent_reverse_second
      E O U
      T O X).mp
      hEOU_TOX

  have hXOT_EOU :
      Geo.AngleCongruent
        X O T
        E O U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E O U
      X O T
      hEOU_XOT

  have hAOT_EOU :
      Geo.AngleCongruent
        A O T
        E O U :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O T
      X O T
      E O U
      hLeftHalf
      hXOT_EOU

  have hTOE_XOU :
      Geo.AngleCongruent
        T O E
        X O U :=
    (Geo.angle_congruent_reverse_second
      T O E
      U O X).mp
      hTOE_UOX

  have hXOU_BOU :
      Geo.AngleCongruent
        X O U
        B O U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B O U
      X O U
      hRightHalf

  have hTOE_BOU :
      Geo.AngleCongruent
        T O E
        B O U :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      T O E
      X O U
      B O U
      hTOE_XOU
      hXOU_BOU

  have hTOE_UOB :
      Geo.AngleCongruent
        T O E
        U O B :=
    (Geo.angle_congruent_reverse_second
      T O E
      B O U).mp
      hTOE_BOU

  --------------------------------------------------------------------
  -- Add the matching alpha and beta components.
  --------------------------------------------------------------------

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    (hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE_AB).1

  have hInsideE_BA :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE_AB

  have hBOE :
      Not (PrimCollinear Geo B O E) :=
    (hilbert_interior_angle_less
      Geo
      O E B A
      hBOA
      hInsideE_BA).1

  have hEOB :
      Not (PrimCollinear Geo E O B) := by
    intro h
    exact
      hBOE
        (PrimCollinearSymm
          Geo E O B h)

  have hAOE_EOB :
      Geo.AngleCongruent
        A O E
        E O B :=
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      O A E T
      O E B U
      hAOE
      hEOB
      hInsideT_AE
      hInsideU_EB
      hAOT_EOU
      hTOE_UOB

  have hBisect :
      Geo.AngleCongruent
        A O E
        B O E :=
    (Geo.angle_congruent_reverse_second
      A O E
      E O B).mp
      hAOE_EOB

  exact
    ⟨E,
      hInsideE_AB,
      hInsideT_AE,
      hInsideU_EB,
      hBisect,
      hTOE_BOU⟩


------------------------------------------------------------------------
-- 2. Forder IV.12: additive branch
------------------------------------------------------------------------

/--
Forder IV.12, additive branch.

Let A,B,C lie on the circle centered at K. Assume C and K are on the
same side of chord AB. Extend CK through K to X. If A and B lie on
opposite sides of the axis KX, then there is an interior bisector KE of
the central angle AKB such that

  angle ACB ~= angle AKE.

This is the half-central-angle conclusion of IV.12 in the branch where
the axis KX crosses the chord AB.
-/
theorem hilbert_forder_IV12_addition_case_stage27
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (chord axis : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKX : Geo.Between C K X)
    (hOppAB : HilbertOppositeSide Geo A B axis) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hLineEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hLineEq]
    exact hCline

  --------------------------------------------------------------------
  -- A,K,C and B,K,C are noncollinear because A,B are off axis KX.
  --------------------------------------------------------------------

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    intro h

    have hKCA :
        PrimCollinear Geo K C A :=
      PrimCollinearCycle
        Geo A K C h

    have hAaxis :
        H.OnLine A axis :=
      hilbert_collinear_on_line
        Geo
        K C A
        axis
        hCK.symm
        hKaxis
        hCaxis
        hKCA

    exact hOppAB.1 hAaxis

  have hBKC :
      Not (PrimCollinear Geo B K C) := by
    intro h

    have hKCB :
        PrimCollinear Geo K C B :=
      PrimCollinearCycle
        Geo B K C h

    have hBaxis :
        H.OnLine B axis :=
      hilbert_collinear_on_line
        Geo
        K C B
        axis
        hCK.symm
        hKaxis
        hCaxis
        hKCB

    exact hOppAB.2.1 hBaxis

  --------------------------------------------------------------------
  -- The central angle AKB is proper because K is off chord AB.
  --------------------------------------------------------------------

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hAKB :
      Not (PrimCollinear Geo A K B) := by
    intro h

    have hABK :
        PrimCollinear Geo A B K :=
      PrimCollinearRotate
        Geo A K B h

    have hKchord :
        H.OnLine K chord :=
      hilbert_collinear_on_line
        Geo
        A B K
        chord
        hAB
        hAchord
        hBchord
        hABK

    exact hKoff hKchord

  --------------------------------------------------------------------
  -- Stage 22 supplies the two common interior dividers.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV12_addition_configuration_stage22
        Geo
        K R A B C X
        chord axis
        hAB
        hAchord
        hBchord
        hKaxis
        hXaxis
        hAcircle
        hBcircle
        hCcircle
        hSameCK
        hCKX
        hOppAB
    with
    ⟨_Y,
      _hAYB,
      _hCKY,
      hInsideX,
      hInsideK⟩

  --------------------------------------------------------------------
  -- Stage 19 supplies the two local doubled-angle blocks.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_exterior_central_half_stage19
        Geo
        K R A C X
        hAcircle
        hCcircle
        hAKC
        hCKX
    with
    ⟨T,
      hInsideT,
      hAKT_XKT,
      hACK_AKT⟩

  rcases
      hilbert_circle_exterior_central_half_stage19
        Geo
        K R B C X
        hBcircle
        hCcircle
        hBKC
        hCKX
    with
    ⟨U,
      hInsideU_BX,
      hBKU_XKU,
      hBCK_BKU⟩

  have hInsideU_XB :
      HilbertRayMeetsSegment Geo K U X B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K U B X
      hInsideU_BX

  --------------------------------------------------------------------
  -- Rearrange alpha,alpha,beta,beta into two equal alpha+beta halves.
  --------------------------------------------------------------------

  rcases
      hilbert_angleDecomposition_double_sum_bisector_stage27
        Geo
        A K B X T U
        hAKB
        hInsideX
        hInsideT
        hInsideU_XB
        hAKT_XKT
        hBKU_XKU
    with
    ⟨E,
      hInsideE,
      hInsideT_AE,
      _hInsideU_EB,
      hBisect,
      hTKE_BKU⟩

  --------------------------------------------------------------------
  -- ACB is proper because C is off chord AB.
  --------------------------------------------------------------------

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAKE :
      Not (PrimCollinear Geo A K E) :=
    (hilbert_interior_angle_less
      Geo
      K E A B
      hAKB
      hInsideE).1

  --------------------------------------------------------------------
  -- Match the two decompositions:
  --
  --   ACB = ACK + KCB
  --   AKE = AKT + TKE.
  --------------------------------------------------------------------

  have hKCB_BKU :
      Geo.AngleCongruent
        K C B
        B K U :=
    (Geo.angle_congruent_reverse_first
      B C K
      B K U).mp
      hBCK_BKU

  have hKCB_TKE :
      Geo.AngleCongruent
        K C B
        T K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K C B
      B K U
      T K E
      hKCB_BKU
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        T K E
        B K U
        hTKE_BKU)

  have hACB_AKE :
      Geo.AngleCongruent
        A C B
        A K E :=
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      C A B K
      K A E T
      hACB
      hAKE
      hInsideK
      hInsideT_AE
      hACK_AKT
      hKCB_TKE

  exact
    ⟨E,
      hInsideE,
      hBisect,
      hACB_AKE⟩
/- END folded proof support: Crossing_circle_stage27_IV12_addition_case_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage28_IV12_sameSide_ray_orders_v1.lean -/
/-!
# Forder IV.12 -- stage 28, same-side axis ray order

This stage isolates only the order geometry of the subtraction branch.

Let C-K-X and let A,B lie on the same side of the axis KX.

At K, one of the two radius rays lies inside the angle formed by the
other radius ray and KX:

  KA inside B-K-X
or
  KB inside A-K-X.

At C, the analogous statement holds with CK as the reference ray:

  CA inside B-C-K
or
  CB inside A-C-K.

The two choices are not yet synchronized here. Stage 29 will use the
stage-19 half-angle congruences to rule out the two crossed pairings.
-/

/--
Same-side ray-order classification at both K and C.
-/
theorem hilbert_forder_IV12_sameSide_ray_orders_stage28
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (K A B C X : Geo.Point)
    (axis : Geo.Line)
    (hCKX : Geo.Between C K X)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAoff : Not (H.OnLine A axis))
    (hBoff : Not (H.OnLine B axis))
    (hSameAB : HilbertSameSide Geo A B axis)
    (hAKB : Not (PrimCollinear Geo A K B))
    (hACB : Not (PrimCollinear Geo A C B)) :
    (HilbertRayMeetsSegment Geo K A B X \/
     HilbertRayMeetsSegment Geo K B A X) /\
    (HilbertRayMeetsSegment Geo C A B K \/
     HilbertRayMeetsSegment Geo C B A K) := by

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X
      hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hEq]
    exact hCline

  have hOrderK :
      HilbertRayMeetsSegment Geo K A B X \/
      HilbertRayMeetsSegment Geo K B A X :=
    hilbert_sameSide_rays_order
      Geo
      K A X B
      axis
      hKX
      hKaxis
      hXaxis
      hAoff
      hBoff
      hSameAB
      hAKB

  have hOrderC :
      HilbertRayMeetsSegment Geo C A B K \/
      HilbertRayMeetsSegment Geo C B A K :=
    hilbert_sameSide_rays_order
      Geo
      C A K B
      axis
      hCK
      hCaxis
      hKaxis
      hAoff
      hBoff
      hSameAB
      hACB

  exact
    ⟨hOrderK,
      hOrderC⟩
/- END folded proof support: Crossing_circle_stage28_IV12_sameSide_ray_orders_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage29_half_angle_monotone_v2.lean -/
/-!
# Forder IV.12 -- stage 29, strict monotonicity of angle halves

This file promotes one neutral angle-order theorem from the XI.23
workshop into the lower planar layer and derives the strict monotonicity
of angle bisection.

No circle-specific statement occurs here.
-/

------------------------------------------------------------------------
-- 1. Strict addition for interior angle decompositions.
------------------------------------------------------------------------

theorem hilbert_angleDecomposition_componentwise_less_whole_stage29
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hX'O'C' : Not (PrimCollinear Geo X' O' C'))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideD' : HilbertRayMeetsSegment Geo O' D' X' C')
    (hLeft : HilbertAngleLess Geo X O D X' O' D')
    (hRight : HilbertAngleLess Geo C O D C' O' D') :
    HilbertAngleLess Geo X O C X' O' C' := by

  --------------------------------------------------------------------
  -- Proper component angles used below.
  --------------------------------------------------------------------

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact hXOC
      (PrimCollinearSymm Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo O D X C hInsideD

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo O D C X hCOX hInsideDrev).1

  have hC'O'X' :
      Not (PrimCollinear Geo C' O' X') := by
    intro h
    exact hX'O'C'
      (PrimCollinearSymm Geo C' O' X' h)

  have hInsideD'rev :
      HilbertRayMeetsSegment Geo O' D' C' X' :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo O' D' X' C' hInsideD'

  have hC'O'D' :
      Not (PrimCollinear Geo C' O' D') :=
    (hilbert_interior_angle_less
      Geo O' D' C' X' hC'O'X' hInsideD'rev).1

  --------------------------------------------------------------------
  -- Trichotomy of the whole angles.
  --------------------------------------------------------------------

  rcases
      angle_trichotomy
        Geo
        X O C
        X' O' C'
        hXOC
        hX'O'C'
    with hWholeEq | hWholeOrder

  --------------------------------------------------------------------
  -- Case 1: the whole angles are congruent.
  --------------------------------------------------------------------

  · rcases
        hilbert_interior_subangle_transport_both
          Geo
          O X C D
          X' O' C'
          hXOC
          hX'O'C'
          hInsideD
          hWholeEq
      with
      ⟨E, hInsideE, hParts⟩

    have hX'O'E :
        Not (PrimCollinear Geo X' O' E) :=
      (hilbert_interior_angle_less
        Geo O' E X' C' hX'O'C' hInsideE).1

    have hInsideErev :
        HilbertRayMeetsSegment Geo O' E C' X' :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo O' E X' C' hInsideE

    have hC'O'E :
        Not (PrimCollinear Geo C' O' E) :=
      (hilbert_interior_angle_less
        Geo O' E C' X' hC'O'X' hInsideErev).1

    have hX'O'E_X'O'D' :
        HilbertAngleLess Geo X' O' E X' O' D' :=
      hilbert_angleLess_transport_left
        Geo
        X O D
        X' O' E
        X' O' D'
        hLeft
        hX'O'E
        (Geometry.Geo.angle_congruent_symmetry
          Geo X O D X' O' E hParts.2)

    have hC'O'E_C'O'D' :
        HilbertAngleLess Geo C' O' E C' O' D' :=
      hilbert_angleLess_transport_left
        Geo
        C O D
        C' O' E
        C' O' D'
        hRight
        hC'O'E
        (Geometry.Geo.angle_congruent_symmetry
          Geo C O D C' O' E hParts.1)

    exact
      False.elim
        (hilbert_angleDecomposition_two_component_less_impossible
          Geo
          O' X' C' E D'
          hX'O'C'
          hInsideE
          hInsideD'
          hX'O'E_X'O'D'
          hC'O'E_C'O'D')

  --------------------------------------------------------------------
  -- Case 2: one whole angle is strictly smaller than the other.
  --------------------------------------------------------------------

  · rcases hWholeOrder with hWanted | hReverse

    · exact hWanted

    ------------------------------------------------------------------
    -- Assume, for contradiction, that the target whole is smaller.
    ------------------------------------------------------------------

    · rcases hReverse with
        ⟨_hX'O'C', _hXOC, E, hInsideE, hWholeTarget⟩

      have hXOE_less_XOC :
          HilbertAngleLess Geo X O E X O C :=
        hilbert_interior_angle_less
          Geo O E X C hXOC hInsideE

      have hXOE :
          Not (PrimCollinear Geo X O E) :=
        hXOE_less_XOC.1

      rcases
          hilbert_interior_subangle_transport_both
            Geo
            O' X' C' D'
            X O E
            hX'O'C'
            hXOE
            hInsideD'
            hWholeTarget
        with
        ⟨F, hInsideF, hTargetParts⟩

      have hXOF_less_XOE :
          HilbertAngleLess Geo X O F X O E :=
        hilbert_interior_angle_less
          Geo O F X E hXOE hInsideF

      have hXOF :
          Not (PrimCollinear Geo X O F) :=
        hXOF_less_XOE.1

      have hXOD_XOF :
          HilbertAngleLess Geo X O D X O F :=
        hilbert_angleLess_transport_right
          Geo
          X O D
          X' O' D'
          X O F
          hLeft
          hXOF
          hTargetParts.2

      have hXOD_XOE :
          HilbertAngleLess Geo X O D X O E :=
        hilbert_angleLess_trans
          Geo
          X O D
          X O F
          X O E
          hXOD_XOF
          hXOF_less_XOE

      ----------------------------------------------------------------
      -- Promote D from the whole XOC to the embedded whole XOE.
      ----------------------------------------------------------------

      have hOX : O ≠ X :=
        hilbert_noncollinear_ne_first
          Geo O X C
          (by
            intro h
            exact hXOC
              (PrimCollinearSwap Geo O X C h))

      rcases
          HilbertPlaneIncidence.line_through
            O X hOX
        with
        ⟨lineOX, hOlineOX, hXlineOX⟩

      have hDCSameOX :
          HilbertSameSide Geo D C lineOX :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O D C X
          lineOX
          hOlineOX
          hXlineOX
          hCOX
          hInsideDrev

      have hInsideErevWhole :
          HilbertRayMeetsSegment Geo O E C X :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O E X C hInsideE

      have hECSameOX :
          HilbertSameSide Geo E C lineOX :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O E C X
          lineOX
          hOlineOX
          hXlineOX
          hCOX
          hInsideErevWhole

      have hCESameOX :
          HilbertSameSide Geo C E lineOX :=
        hilbert_sameSide_symm
          Geo E C lineOX hECSameOX

      have hDESameOX :
          HilbertSameSide Geo D E lineOX :=
        hilbert_sameSide_trans
          Geo D C E lineOX hDCSameOX hCESameOX

      have hInsideD_XE :
          HilbertRayMeetsSegment Geo O D X E :=
        hilbert_angleDecomposition_angle_less_ray_inside
          Geo
          D E O X
          lineOX
          hOlineOX
          hXlineOX
          hOX
          hDESameOX
          hXOD_XOE

      ----------------------------------------------------------------
      -- Inside XOE, D precedes F, so EOF < EOD.
      ----------------------------------------------------------------

      have hEOF_EOD :
          HilbertAngleLess Geo E O F E O D :=
        hilbert_angleDecomposition_complement_order_reverse_stage26
          Geo
          O X E D F
          hXOE
          hInsideD_XE
          hInsideF
          hXOD_XOF

      ----------------------------------------------------------------
      -- Inside XOC, D precedes E.  Therefore E lies inside DOC.
      ----------------------------------------------------------------

      have hCOE_COD :
          HilbertAngleLess Geo C O E C O D :=
        hilbert_angleDecomposition_complement_order_reverse_stage26
          Geo
          O X C D E
          hXOC
          hInsideD
          hInsideE
          hXOD_XOE

      have hOC : O ≠ C :=
        hilbert_noncollinear_ne_first
          Geo O C X
          (by
            intro h
            exact hXOC
              (PrimCollinearRotate
                Geo X C O
                (PrimCollinearSymm Geo O C X h)))

      rcases
          HilbertPlaneIncidence.line_through
            O C hOC
        with
        ⟨lineOC, hOlineOC, hClineOC⟩

      have hDXSameOC :
          HilbertSameSide Geo D X lineOC :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O D X C
          lineOC
          hOlineOC
          hClineOC
          hXOC
          hInsideD

      have hEXSameOC :
          HilbertSameSide Geo E X lineOC :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O E X C
          lineOC
          hOlineOC
          hClineOC
          hXOC
          hInsideE

      have hXDSameOC :
          HilbertSameSide Geo X D lineOC :=
        hilbert_sameSide_symm
          Geo D X lineOC hDXSameOC

      have hEDSameOC :
          HilbertSameSide Geo E D lineOC :=
        hilbert_sameSide_trans
          Geo E X D lineOC hEXSameOC hXDSameOC

      have hInsideE_CD :
          HilbertRayMeetsSegment Geo O E C D :=
        hilbert_angleDecomposition_angle_less_ray_inside
          Geo
          E D O C
          lineOC
          hOlineOC
          hClineOC
          hOC
          hEDSameOC
          hCOE_COD

      have hInsideE_DC :
          HilbertRayMeetsSegment Geo O E D C :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O E C D hInsideE_CD

      have hDOC :
          Not (PrimCollinear Geo D O C) := by
        intro h
        exact hCOD
          (PrimCollinearSymm Geo D O C h)

      have hDOE_DOC :
          HilbertAngleLess Geo D O E D O C :=
        hilbert_interior_angle_less
          Geo O E D C hDOC hInsideE_DC

      have hDOE :
          Not (PrimCollinear Geo D O E) :=
        hDOE_DOC.1

      have hEOD :
          Not (PrimCollinear Geo E O D) := by
        intro h
        exact hDOE
          (PrimCollinearSymm Geo E O D h)

      have hReflDOE :
          Geo.AngleCongruent D O E D O E :=
        Geometry.Geo.angle_congruent_reflexive
          Geo D O E

      have hEOD_DOE :
          Geo.AngleCongruent E O D D O E :=
        (Geometry.Geo.angle_congruent_reverse_first
          Geo D O E D O E).mp hReflDOE

      have hEOD_DOC :
          HilbertAngleLess Geo E O D D O C :=
        hilbert_angleLess_transport_left
          Geo
          D O E
          E O D
          D O C
          hDOE_DOC
          hEOD
          hEOD_DOE

      have hReflDOC :
          Geo.AngleCongruent D O C D O C :=
        Geometry.Geo.angle_congruent_reflexive
          Geo D O C

      have hDOC_COD :
          Geo.AngleCongruent D O C C O D :=
        (Geometry.Geo.angle_congruent_reverse_second
          Geo D O C D O C).mp hReflDOC

      have hEOD_COD :
          HilbertAngleLess Geo E O D C O D :=
        hilbert_angleLess_transport_right
          Geo
          E O D
          D O C
          C O D
          hEOD_DOC
          hCOD
          hDOC_COD

      have hEOF_COD :
          HilbertAngleLess Geo E O F C O D :=
        hilbert_angleLess_trans
          Geo
          E O F
          E O D
          C O D
          hEOF_EOD
          hEOD_COD

      ----------------------------------------------------------------
      -- But the assumed second component inequality says COD < EOF.
      ----------------------------------------------------------------

      have hEOX :
          Not (PrimCollinear Geo E O X) := by
        intro h
        exact hXOE
          (PrimCollinearSymm Geo E O X h)

      have hInsideFrev :
          HilbertRayMeetsSegment Geo O F E X :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O F X E hInsideF

      have hEOF :
          Not (PrimCollinear Geo E O F) :=
        (hilbert_interior_angle_less
          Geo O F E X hEOX hInsideFrev).1

      have hCOD_EOF :
          HilbertAngleLess Geo C O D E O F :=
        hilbert_angleLess_transport_right
          Geo
          C O D
          C' O' D'
          E O F
          hRight
          hEOF
          hTargetParts.1

      have hCycle :
          HilbertAngleLess Geo C O D C O D :=
        hilbert_angleLess_trans
          Geo
          C O D
          E O F
          C O D
          hCOD_EOF
          hEOF_COD

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo C O D)
            hCycle)




------------------------------------------------------------------------
-- 2. Strict monotonicity of angle halves.
------------------------------------------------------------------------

/--
Strict monotonicity of synthetic angle halves.

If two proper angles are bisected by interior rays and the first whole
angle is strictly smaller than the second whole angle, then the first
half is strictly smaller than the second half.

This is the non-numerical form of

  alpha < beta  ->  alpha/2 < beta/2.
-/
theorem hilbert_angleDecomposition_half_less_of_whole_less_stage29
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hX'O'C' : Not (PrimCollinear Geo X' O' C'))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideD' : HilbertRayMeetsSegment Geo O' D' X' C')
    (hBisect :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisect' :
      Geo.AngleCongruent
        X' O' D'
        C' O' D')
    (hWholeLess :
      HilbertAngleLess Geo
        X O C
        X' O' C') :
    HilbertAngleLess Geo
      X O D
      X' O' D' := by

  have hXOD :
      Not (PrimCollinear Geo X O D) :=
    (hilbert_interior_angle_less
      Geo
      O D X C
      hXOC
      hInsideD).1

  have hX'O'D' :
      Not (PrimCollinear Geo X' O' D') :=
    (hilbert_interior_angle_less
      Geo
      O' D' X' C'
      hX'O'C'
      hInsideD').1

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hC'O'X' :
      Not (PrimCollinear Geo C' O' X') := by
    intro h
    exact
      hX'O'C'
        (PrimCollinearSymm
          Geo C' O' X' h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideD'rev :
      HilbertRayMeetsSegment Geo O' D' C' X' :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O' D' X' C'
      hInsideD'

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo
      O D C X
      hCOX
      hInsideDrev).1

  have hC'O'D' :
      Not (PrimCollinear Geo C' O' D') :=
    (hilbert_interior_angle_less
      Geo
      O' D' C' X'
      hC'O'X'
      hInsideD'rev).1

  rcases
      angle_trichotomy
        Geo
        X O D
        X' O' D'
        hXOD
        hX'O'D'
    with hEq | hOrder

  --------------------------------------------------------------------
  -- Equal halves would force equal whole angles.
  --------------------------------------------------------------------

  · have hXOD_DOC :
        Geo.AngleCongruent
          X O D
          D O C :=
      (Geo.angle_congruent_reverse_second
        X O D
        C O D).mp
        hBisect

    have hX'O'D'_D'O'C' :
        Geo.AngleCongruent
          X' O' D'
          D' O' C' :=
      (Geo.angle_congruent_reverse_second
        X' O' D'
        C' O' D').mp
        hBisect'

    have hDOC_XOD :
        Geo.AngleCongruent
          D O C
          X O D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        D O C
        hXOD_DOC

    have hDOC_X'O'D' :
        Geo.AngleCongruent
          D O C
          X' O' D' :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        D O C
        X O D
        X' O' D'
        hDOC_XOD
        hEq

    have hDOC_D'O'C' :
        Geo.AngleCongruent
          D O C
          D' O' C' :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        D O C
        X' O' D'
        D' O' C'
        hDOC_X'O'D'
        hX'O'D'_D'O'C'

    have hWholeEq :
        Geo.AngleCongruent
          X O C
          X' O' C' :=
      hilbert_angleDecomposition_angle_addition_interior
        Geo
        O X C D
        O' X' C' D'
        hXOC
        hX'O'C'
        hInsideD
        hInsideD'
        hEq
        hDOC_D'O'C'

    have hWholeEqSymm :
        Geo.AngleCongruent
          X' O' C'
          X O C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O C
        X' O' C'
        hWholeEq

    have hCycle :
        HilbertAngleLess Geo
          X O C
          X O C :=
      hilbert_angleLess_transport_right
        Geo
        X O C
        X' O' C'
        X O C
        hWholeLess
        hXOC
        hWholeEqSymm

    exact
      False.elim
        ((hilbert_angleLess_irrefl
          Geo X O C)
          hCycle)

  --------------------------------------------------------------------
  -- Strict order of halves.
  --------------------------------------------------------------------

  · rcases hOrder with hWanted | hReverse

    · exact hWanted

    ------------------------------------------------------------------
    -- Reverse half order would force reverse whole order.
    ------------------------------------------------------------------

    · have hC'O'D'_X'O'D' :
          Geo.AngleCongruent
            C' O' D'
            X' O' D' :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          X' O' D'
          C' O' D'
          hBisect'

      have hC'O'D'_XOD :
          HilbertAngleLess Geo
            C' O' D'
            X O D :=
        hilbert_angleLess_transport_left
          Geo
          X' O' D'
          C' O' D'
          X O D
          hReverse
          hC'O'D'
          hC'O'D'_X'O'D'

      have hC'O'D'_COD :
          HilbertAngleLess Geo
            C' O' D'
            C O D :=
        hilbert_angleLess_transport_right
          Geo
          C' O' D'
          X O D
          C O D
          hC'O'D'_XOD
          hCOD
          hBisect

      have hWholeReverse :
          HilbertAngleLess Geo
            X' O' C'
            X O C :=
        hilbert_angleDecomposition_componentwise_less_whole_stage29
          Geo
          O' X' C' D'
          O X C D
          hX'O'C'
          hXOC
          hInsideD'
          hInsideD
          hReverse
          hC'O'D'_COD

      have hCycle :
          HilbertAngleLess Geo
            X O C
            X O C :=
        hilbert_angleLess_trans
          Geo
          X O C
          X' O' C'
          X O C
          hWholeLess
          hWholeReverse

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo X O C)
            hCycle)
/- END folded proof support: Crossing_circle_stage29_half_angle_monotone_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage30_IV12_sameSide_synchronized_v1.lean -/
/-!
# Forder IV.12 -- stage 30, synchronization of the subtraction branches

Stage 28 gives independent ray-order alternatives at K and C.

Stage 29 now lets us synchronize them.  The local stage-19
constructions identify

  angle ACK = half angle AKX,
  angle BCK = half angle BKX.

Hence the strict order of AKX and BKX is exactly the strict order of
ACK and BCK.  The crossed combinations of the two stage-28
classifications would therefore give a strict cycle of angles.

No numerical angle measure is used.
-/

/--
In the same-side-axis branch, the ray-order alternatives at K and C
have the same orientation.

Thus exactly one of the following two compatible configurations holds:

* KA is interior to BKX and CA is interior to BCK;
* KB is interior to AKX and CB is interior to ACK.
-/
theorem hilbert_forder_IV12_sameSide_orders_synchronized_stage30
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (axis : Geo.Line)
    (hCKX : Geo.Between C K X)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameAB : HilbertSameSide Geo A B axis)
    (hAKB : Not (PrimCollinear Geo A K B))
    (hACB : Not (PrimCollinear Geo A C B)) :
    (HilbertRayMeetsSegment Geo K A B X /\
     HilbertRayMeetsSegment Geo C A B K) \/
    (HilbertRayMeetsSegment Geo K B A X /\
     HilbertRayMeetsSegment Geo C B A K) := by

  have hAoff :
      Not (H.OnLine A axis) :=
    hSameAB.1

  have hBoff :
      Not (H.OnLine B axis) :=
    hSameAB.2.1

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hLineEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hLineEq]
    exact hCline

  --------------------------------------------------------------------
  -- Proper local radius angles.
  --------------------------------------------------------------------

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    rintro ⟨lineAKC,
      hAline,
      hKline',
      hCline'⟩

    have hEq :
        lineAKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineAKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hBKC :
      Not (PrimCollinear Geo B K C) := by
    rintro ⟨lineBKC,
      hBline,
      hKline',
      hCline'⟩

    have hEq :
        lineBKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineBKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hXKA :
      Not (PrimCollinear Geo X K A) := by
    rintro ⟨lineXKA,
      hXline',
      hKline',
      hAline⟩

    have hEq :
        lineXKA = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineXKA axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hXKB :
      Not (PrimCollinear Geo X K B) := by
    rintro ⟨lineXKB,
      hXline',
      hKline',
      hBline⟩

    have hEq :
        lineXKB = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineXKB axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hACK :
      Not (PrimCollinear Geo A C K) := by
    rintro ⟨lineACK,
      hAline,
      hCline',
      hKline'⟩
    exact
      hAKC
        ⟨lineACK,
          hAline,
          hKline',
          hCline'⟩

  have hBCK :
      Not (PrimCollinear Geo B C K) := by
    rintro ⟨lineBCK,
      hBline,
      hCline',
      hKline'⟩
    exact
      hBKC
        ⟨lineBCK,
          hBline,
          hKline',
          hCline'⟩

  have hKCA :
      Not (PrimCollinear Geo K C A) := by
    rintro ⟨lineKCA,
      hKline',
      hCline',
      hAline⟩
    exact
      hACK
        ⟨lineKCA,
          hAline,
          hCline',
          hKline'⟩

  have hKCB :
      Not (PrimCollinear Geo K C B) := by
    rintro ⟨lineKCB,
      hKline',
      hCline',
      hBline⟩
    exact
      hBCK
        ⟨lineKCB,
          hBline,
          hCline',
          hKline'⟩

  --------------------------------------------------------------------
  -- Stage 19: the two local half-angle identifications.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_exterior_central_half_stage19
        Geo
        K R A C X
        hAcircle
        hCcircle
        hAKC
        hCKX
    with
    ⟨T,
      hInsideT_AX,
      hAKT_XKT,
      hACK_AKT⟩

  rcases
      hilbert_circle_exterior_central_half_stage19
        Geo
        K R B C X
        hBcircle
        hCcircle
        hBKC
        hCKX
    with
    ⟨U,
      hInsideU_BX,
      hBKU_XKU,
      hBCK_BKU⟩

  have hInsideT_XA :
      HilbertRayMeetsSegment Geo K T X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K T A X
      hInsideT_AX

  have hInsideU_XB :
      HilbertRayMeetsSegment Geo K U X B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K U B X
      hInsideU_BX

  have hXKT_AKT :
      Geo.AngleCongruent
        X K T
        A K T :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K T
      X K T
      hAKT_XKT

  have hXKU_BKU :
      Geo.AngleCongruent
        X K U
        B K U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K U
      X K U
      hBKU_XKU

  have hACK_XKT :
      Geo.AngleCongruent
        A C K
        X K T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C K
      A K T
      X K T
      hACK_AKT
      hAKT_XKT

  have hBCK_XKU :
      Geo.AngleCongruent
        B C K
        X K U :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B C K
      B K U
      X K U
      hBCK_BKU
      hBKU_XKU

  have hXKT_ACK :
      Geo.AngleCongruent
        X K T
        A C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A C K
      X K T
      hACK_XKT

  have hXKU_BCK :
      Geo.AngleCongruent
        X K U
        B C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B C K
      X K U
      hBCK_XKU

  --------------------------------------------------------------------
  -- Stage 28: independent order classifications.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV12_sameSide_ray_orders_stage28
        Geo
        K A B C X
        axis
        hCKX
        hKaxis
        hXaxis
        hAoff
        hBoff
        hSameAB
        hAKB
        hACB
    with
    ⟨hOrderK,
      hOrderC⟩

  --------------------------------------------------------------------
  -- Helper: CA inside BCK gives ACK < BCK.
  --------------------------------------------------------------------

  have hLessC_left :
      HilbertRayMeetsSegment Geo C A B K ->
      HilbertAngleLess Geo A C K B C K := by
    intro hInsideA_BK

    have hInsideA_KB :
        HilbertRayMeetsSegment Geo C A K B :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        C A B K
        hInsideA_BK

    have hRaw :
        HilbertAngleLess Geo
          K C A
          K C B :=
      hilbert_interior_angle_less
        Geo
        C A K B
        hKCB
        hInsideA_KB

    have hKCArefl :
        Geo.AngleCongruent
          K C A
          K C A :=
      Geometry.Geo.angle_congruent_reflexive
        Geo K C A

    have hACK_KCA :
        Geo.AngleCongruent
          A C K
          K C A :=
      (Geo.angle_congruent_reverse_first
        K C A
        K C A).mp
        hKCArefl

    have hStep :
        HilbertAngleLess Geo
          A C K
          K C B :=
      hilbert_angleLess_transport_left
        Geo
        K C A
        A C K
        K C B
        hRaw
        hACK
        hACK_KCA

    have hBCKrefl :
        Geo.AngleCongruent
          B C K
          B C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B C K

    have hKCB_BCK :
        Geo.AngleCongruent
          K C B
          B C K :=
      (Geo.angle_congruent_reverse_first
        B C K
        B C K).mp
        hBCKrefl

    exact
      hilbert_angleLess_transport_right
        Geo
        A C K
        K C B
        B C K
        hStep
        hBCK
        hKCB_BCK

  --------------------------------------------------------------------
  -- Helper: CB inside ACK gives BCK < ACK.
  --------------------------------------------------------------------

  have hLessC_right :
      HilbertRayMeetsSegment Geo C B A K ->
      HilbertAngleLess Geo B C K A C K := by
    intro hInsideB_AK

    have hInsideB_KA :
        HilbertRayMeetsSegment Geo C B K A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        C B A K
        hInsideB_AK

    have hRaw :
        HilbertAngleLess Geo
          K C B
          K C A :=
      hilbert_interior_angle_less
        Geo
        C B K A
        hKCA
        hInsideB_KA

    have hKCBrefl :
        Geo.AngleCongruent
          K C B
          K C B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo K C B

    have hBCK_KCB :
        Geo.AngleCongruent
          B C K
          K C B :=
      (Geo.angle_congruent_reverse_first
        K C B
        K C B).mp
        hKCBrefl

    have hStep :
        HilbertAngleLess Geo
          B C K
          K C A :=
      hilbert_angleLess_transport_left
        Geo
        K C B
        B C K
        K C A
        hRaw
        hBCK
        hBCK_KCB

    have hACKrefl :
        Geo.AngleCongruent
          A C K
          A C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A C K

    have hKCA_ACK :
        Geo.AngleCongruent
          K C A
          A C K :=
      (Geo.angle_congruent_reverse_first
        A C K
        A C K).mp
        hACKrefl

    exact
      hilbert_angleLess_transport_right
        Geo
        B C K
        K C A
        A C K
        hStep
        hACK
        hKCA_ACK

  --------------------------------------------------------------------
  -- Synchronize.
  --------------------------------------------------------------------

  rcases hOrderK with hKA | hKB

  --------------------------------------------------------------------
  -- KA is inside BKX.
  --------------------------------------------------------------------

  · have hInsideA_XB :
        HilbertRayMeetsSegment Geo K A X B :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        K A B X
        hKA

    have hWholeLess :
        HilbertAngleLess Geo
          X K A
          X K B :=
      hilbert_interior_angle_less
        Geo
        K A X B
        hXKB
        hInsideA_XB

    have hHalfLess :
        HilbertAngleLess Geo
          X K T
          X K U :=
      hilbert_angleDecomposition_half_less_of_whole_less_stage29
        Geo
        K X A T
        K X B U
        hXKA
        hXKB
        hInsideT_XA
        hInsideU_XB
        hXKT_AKT
        hXKU_BKU
        hWholeLess

    have hACK_XKU :
        HilbertAngleLess Geo
          A C K
          X K U :=
      hilbert_angleLess_transport_left
        Geo
        X K T
        A C K
        X K U
        hHalfLess
        hACK
        hACK_XKT

    have hACK_BCK :
        HilbertAngleLess Geo
          A C K
          B C K :=
      hilbert_angleLess_transport_right
        Geo
        A C K
        X K U
        B C K
        hACK_XKU
        hBCK
        hXKU_BCK

    rcases hOrderC with hCA | hCB

    · exact
        Or.inl
          ⟨hKA,
            hCA⟩

    · have hBCK_ACK :
          HilbertAngleLess Geo
            B C K
            A C K :=
        hLessC_right hCB

      have hCycle :
          HilbertAngleLess Geo
            A C K
            A C K :=
        hilbert_angleLess_trans
          Geo
          A C K
          B C K
          A C K
          hACK_BCK
          hBCK_ACK

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo A C K)
            hCycle)

  --------------------------------------------------------------------
  -- KB is inside AKX.
  --------------------------------------------------------------------

  · have hInsideB_XA :
        HilbertRayMeetsSegment Geo K B X A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        K B A X
        hKB

    have hWholeLess :
        HilbertAngleLess Geo
          X K B
          X K A :=
      hilbert_interior_angle_less
        Geo
        K B X A
        hXKA
        hInsideB_XA

    have hHalfLess :
        HilbertAngleLess Geo
          X K U
          X K T :=
      hilbert_angleDecomposition_half_less_of_whole_less_stage29
        Geo
        K X B U
        K X A T
        hXKB
        hXKA
        hInsideU_XB
        hInsideT_XA
        hXKU_BKU
        hXKT_AKT
        hWholeLess

    have hBCK_XKT :
        HilbertAngleLess Geo
          B C K
          X K T :=
      hilbert_angleLess_transport_left
        Geo
        X K U
        B C K
        X K T
        hHalfLess
        hBCK
        hBCK_XKU

    have hBCK_ACK :
        HilbertAngleLess Geo
          B C K
          A C K :=
      hilbert_angleLess_transport_right
        Geo
        B C K
        X K T
        A C K
        hBCK_XKT
        hACK
        hXKT_ACK

    rcases hOrderC with hCA | hCB

    · have hACK_BCK :
          HilbertAngleLess Geo
            A C K
            B C K :=
        hLessC_left hCA

      have hCycle :
          HilbertAngleLess Geo
            B C K
            B C K :=
        hilbert_angleLess_trans
          Geo
          B C K
          A C K
          B C K
          hBCK_ACK
          hACK_BCK

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo B C K)
            hCycle)

    · exact
        Or.inr
          ⟨hKB,
            hCB⟩
/- END folded proof support: Crossing_circle_stage30_IV12_sameSide_synchronized_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage31_IV12_subtraction_case_v1.lean -/
/-!
# Forder IV.12 -- stage 31, complete subtraction case

This file closes the same-side-axis branch of Forder IV.12.

The key point is that no separate arithmetic of angle differences is
introduced.

After stage 30 synchronizes the ray order at K and C, choose an
ordinary bisector KE of the target central angle AKB.  In either
orientation, apply the stage-27 addition theorem to

  target angle + smaller exterior-central angle
      = larger exterior-central angle.

This constructs another bisector KW of the larger exterior-central
angle.  Uniqueness of angle halves identifies KW with the stage-19
bisector of that larger angle.  A single application of synthetic
angle subtraction then compares the corresponding remainders:

  angle ACB ~= angle AKE.

Thus Forder's subtraction step is recovered entirely inside the
existing incidence/order/congruence angle machinery.
-/

/--
Forder IV.12, subtraction branch.

Let A,B,C lie on the circle centered at K, let C-K-X, and suppose C and
K are on the same side of chord AB.  If A and B lie on the same side
of the axis KX, then there exists an interior bisector KE of angle AKB
whose half is congruent to the inscribed angle ACB.
-/
theorem hilbert_forder_IV12_subtraction_case_stage31
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (chord axis : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKX : Geo.Between C K X)
    (hSameAB : HilbertSameSide Geo A B axis) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  --------------------------------------------------------------------
  -- Axis data.
  --------------------------------------------------------------------

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hLineEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hLineEq]
    exact hCline

  have hAoff :
      Not (H.OnLine A axis) :=
    hSameAB.1

  have hBoff :
      Not (H.OnLine B axis) :=
    hSameAB.2.1

  --------------------------------------------------------------------
  -- Proper radius/axis angles.
  --------------------------------------------------------------------

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    rintro ⟨lineAKC,
      hAline,
      hKline',
      hCline'⟩

    have hEq :
        lineAKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineAKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hBKC :
      Not (PrimCollinear Geo B K C) := by
    rintro ⟨lineBKC,
      hBline,
      hKline',
      hCline'⟩

    have hEq :
        lineBKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineBKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hAKX :
      Not (PrimCollinear Geo A K X) := by
    rintro ⟨lineAKX,
      hAline,
      hKline',
      hXline'⟩

    have hEq :
        lineAKX = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineAKX axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hBKX :
      Not (PrimCollinear Geo B K X) := by
    rintro ⟨lineBKX,
      hBline,
      hKline',
      hXline'⟩

    have hEq :
        lineBKX = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineBKX axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hACK :
      Not (PrimCollinear Geo A C K) := by
    rintro ⟨lineACK,
      hAline,
      hCline',
      hKline'⟩
    exact
      hAKC
        ⟨lineACK,
          hAline,
          hKline',
          hCline'⟩

  have hBCK :
      Not (PrimCollinear Geo B C K) := by
    rintro ⟨lineBCK,
      hBline,
      hCline',
      hKline'⟩
    exact
      hBKC
        ⟨lineBCK,
          hBline,
          hKline',
          hCline'⟩

  --------------------------------------------------------------------
  -- Proper central and inscribed target angles from the chord.
  --------------------------------------------------------------------

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hAKB :
      Not (PrimCollinear Geo A K B) := by
    intro h

    have hABK :
        PrimCollinear Geo A B K :=
      PrimCollinearRotate
        Geo A K B h

    have hKchord :
        H.OnLine K chord :=
      hilbert_collinear_on_line
        Geo
        A B K
        chord
        hAB
        hAchord
        hBchord
        hABK

    exact hKoff hKchord

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  --------------------------------------------------------------------
  -- Synchronize the two possible subtraction orientations.
  --------------------------------------------------------------------

  have hSync :=
    hilbert_forder_IV12_sameSide_orders_synchronized_stage30
      Geo
      K R A B C X
      axis
      hCKX
      hKaxis
      hXaxis
      hAcircle
      hBcircle
      hCcircle
      hSameAB
      hAKB
      hACB

  --------------------------------------------------------------------
  -- Stage 19: the two exterior-central half constructions.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_exterior_central_half_stage19
        Geo
        K R A C X
        hAcircle
        hCcircle
        hAKC
        hCKX
    with
    ⟨T,
      hInsideT_AX,
      hAKT_XKT,
      hACK_AKT⟩

  rcases
      hilbert_circle_exterior_central_half_stage19
        Geo
        K R B C X
        hBcircle
        hCcircle
        hBKC
        hCKX
    with
    ⟨U,
      hInsideU_BX,
      hBKU_XKU,
      hBCK_BKU⟩

  --------------------------------------------------------------------
  -- Choose an ordinary bisector of the target central angle AKB.
  --------------------------------------------------------------------

  rcases
      hilbert_angle_bisector_with_interior_stage23
        Geo
        K A B
        hAKB
    with
    ⟨E,
      hInsideE_AB,
      hBisectRaw⟩

  have hBisect :
      Geo.AngleCongruent
        A K E
        B K E :=
    (Geo.angle_congruent_reverse_second
      A K E
      E K B).mp
      hBisectRaw

  have hBisectSymm :
      Geo.AngleCongruent
        B K E
        A K E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K E
      B K E
      hBisect

  --------------------------------------------------------------------
  -- Split according to the synchronized ray order.
  --------------------------------------------------------------------

  rcases hSync with hCaseA | hCaseB

  --------------------------------------------------------------------
  -- Case A:
  --
  --   KA is interior to BKX,
  --   CA is interior to BCK.
  --
  -- Hence
  --
  --   BKX = BKA + AKX,
  --   BCK = BCA + ACK.
  --------------------------------------------------------------------

  · rcases hCaseA with
      ⟨hInsideA_BX,
        hInsideA_BK⟩

    have hInsideE_BA :
        HilbertRayMeetsSegment Geo K E B A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        K E A B
        hInsideE_AB

    have hXKT_AKT :
        Geo.AngleCongruent
          X K T
          A K T :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A K T
        X K T
        hAKT_XKT

    ------------------------------------------------------------------
    -- Rebuild the bisector of the larger angle BKX from
    --
    --   half(BKA) + half(AKX).
    ------------------------------------------------------------------

    rcases
        hilbert_angleDecomposition_double_sum_bisector_stage27
          Geo
          B K X A E T
          hBKX
          hInsideA_BX
          hInsideE_BA
          hInsideT_AX
          hBisectSymm
          hXKT_AKT
      with
      ⟨W,
        hInsideW_BX,
        hInsideE_BW,
        _hInsideT_WX,
        hBisectW,
        hEKW_XKT⟩

    ------------------------------------------------------------------
    -- The rebuilt bisector W and the stage-19 bisector U bisect the
    -- same whole angle BKX.
    ------------------------------------------------------------------

    have hBKW_BKU :
        Geo.AngleCongruent
          B K W
          B K U :=
      hilbert_angleDecomposition_angle_half_unique
        Geo
        K B X W U
        hBKX
        hInsideW_BX
        hInsideU_BX
        hBisectW
        hBKU_XKU

    have hBKU_BKW :
        Geo.AngleCongruent
          B K U
          B K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        B K W
        B K U
        hBKW_BKU

    have hBCK_BKW :
        Geo.AngleCongruent
          B C K
          B K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        B C K
        B K U
        B K W
        hBCK_BKU
        hBKU_BKW

    ------------------------------------------------------------------
    -- Match the smaller right components:
    --
    --   KCA ~= WKE.
    ------------------------------------------------------------------

    have hACKrefl :
        Geo.AngleCongruent
          A C K
          A C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A C K

    have hKCA_ACK :
        Geo.AngleCongruent
          K C A
          A C K :=
      (Geo.angle_congruent_reverse_first
        A C K
        A C K).mp
        hACKrefl

    have hKCA_AKT :
        Geo.AngleCongruent
          K C A
          A K T :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        A C K
        A K T
        hKCA_ACK
        hACK_AKT

    have hKCA_XKT :
        Geo.AngleCongruent
          K C A
          X K T :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        A K T
        X K T
        hKCA_AKT
        hAKT_XKT

    have hXKT_EKW :
        Geo.AngleCongruent
          X K T
          E K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        E K W
        X K T
        hEKW_XKT

    have hKCA_EKW :
        Geo.AngleCongruent
          K C A
          E K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        X K T
        E K W
        hKCA_XKT
        hXKT_EKW

    have hEKWrefl :
        Geo.AngleCongruent
          E K W
          E K W :=
      Geometry.Geo.angle_congruent_reflexive
        Geo E K W

    have hEKW_WKE :
        Geo.AngleCongruent
          E K W
          W K E :=
      (Geo.angle_congruent_reverse_second
        E K W
        E K W).mp
        hEKWrefl

    have hKCA_WKE :
        Geo.AngleCongruent
          K C A
          W K E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        E K W
        W K E
        hKCA_EKW
        hEKW_WKE

    ------------------------------------------------------------------
    -- Subtract the matched smaller components from the matched larger
    -- halves.
    ------------------------------------------------------------------

    have hBKW :
        Not (PrimCollinear Geo B K W) :=
      (hilbert_interior_angle_less
        Geo
        K W B X
        hBKX
        hInsideW_BX).1

    have hBCA_BKE :
        Geo.AngleCongruent
          B C A
          B K E :=
      hilbert_angleDecomposition_angle_subtraction
        Geo
        C B K A
        B K W E
        hBCK
        hBKW
        hInsideA_BK
        hInsideE_BW
        hBCK_BKW
        hKCA_WKE

    have hACB_BKE :
        Geo.AngleCongruent
          A C B
          B K E :=
      (Geo.angle_congruent_reverse_first
        B C A
        B K E).mp
        hBCA_BKE

    have hACB_AKE :
        Geo.AngleCongruent
          A C B
          A K E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        A C B
        B K E
        A K E
        hACB_BKE
        hBisectSymm

    exact
      ⟨E,
        hInsideE_AB,
        hBisect,
        hACB_AKE⟩

  --------------------------------------------------------------------
  -- Case B:
  --
  --   KB is interior to AKX,
  --   CB is interior to ACK.
  --
  -- Hence
  --
  --   AKX = AKB + BKX,
  --   ACK = ACB + BCK.
  --------------------------------------------------------------------

  · rcases hCaseB with
      ⟨hInsideB_AX,
        hInsideB_AK⟩

    have hXKU_BKU :
        Geo.AngleCongruent
          X K U
          B K U :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        B K U
        X K U
        hBKU_XKU

    ------------------------------------------------------------------
    -- Rebuild the bisector of the larger angle AKX from
    --
    --   half(AKB) + half(BKX).
    ------------------------------------------------------------------

    rcases
        hilbert_angleDecomposition_double_sum_bisector_stage27
          Geo
          A K X B E U
          hAKX
          hInsideB_AX
          hInsideE_AB
          hInsideU_BX
          hBisect
          hXKU_BKU
      with
      ⟨W,
        hInsideW_AX,
        hInsideE_AW,
        _hInsideU_WX,
        hBisectW,
        hEKW_XKU⟩

    ------------------------------------------------------------------
    -- The rebuilt bisector W and the stage-19 bisector T bisect the
    -- same whole angle AKX.
    ------------------------------------------------------------------

    have hAKW_AKT :
        Geo.AngleCongruent
          A K W
          A K T :=
      hilbert_angleDecomposition_angle_half_unique
        Geo
        K A X W T
        hAKX
        hInsideW_AX
        hInsideT_AX
        hBisectW
        hAKT_XKT

    have hAKT_AKW :
        Geo.AngleCongruent
          A K T
          A K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A K W
        A K T
        hAKW_AKT

    have hACK_AKW :
        Geo.AngleCongruent
          A C K
          A K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        A C K
        A K T
        A K W
        hACK_AKT
        hAKT_AKW

    ------------------------------------------------------------------
    -- Match the smaller right components:
    --
    --   KCB ~= WKE.
    ------------------------------------------------------------------

    have hBCKrefl :
        Geo.AngleCongruent
          B C K
          B C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B C K

    have hKCB_BCK :
        Geo.AngleCongruent
          K C B
          B C K :=
      (Geo.angle_congruent_reverse_first
        B C K
        B C K).mp
        hBCKrefl

    have hKCB_BKU :
        Geo.AngleCongruent
          K C B
          B K U :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        B C K
        B K U
        hKCB_BCK
        hBCK_BKU

    have hKCB_XKU :
        Geo.AngleCongruent
          K C B
          X K U :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        B K U
        X K U
        hKCB_BKU
        hBKU_XKU

    have hXKU_EKW :
        Geo.AngleCongruent
          X K U
          E K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        E K W
        X K U
        hEKW_XKU

    have hKCB_EKW :
        Geo.AngleCongruent
          K C B
          E K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        X K U
        E K W
        hKCB_XKU
        hXKU_EKW

    have hEKWrefl :
        Geo.AngleCongruent
          E K W
          E K W :=
      Geometry.Geo.angle_congruent_reflexive
        Geo E K W

    have hEKW_WKE :
        Geo.AngleCongruent
          E K W
          W K E :=
      (Geo.angle_congruent_reverse_second
        E K W
        E K W).mp
        hEKWrefl

    have hKCB_WKE :
        Geo.AngleCongruent
          K C B
          W K E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        E K W
        W K E
        hKCB_EKW
        hEKW_WKE

    ------------------------------------------------------------------
    -- Subtract the matched smaller components.
    ------------------------------------------------------------------

    have hAKW :
        Not (PrimCollinear Geo A K W) :=
      (hilbert_interior_angle_less
        Geo
        K W A X
        hAKX
        hInsideW_AX).1

    have hACB_AKE :
        Geo.AngleCongruent
          A C B
          A K E :=
      hilbert_angleDecomposition_angle_subtraction
        Geo
        C A K B
        A K W E
        hACK
        hAKW
        hInsideB_AK
        hInsideE_AW
        hACK_AKW
        hKCB_WKE

    exact
      ⟨E,
        hInsideE_AB,
        hBisect,
        hACB_AKE⟩
/- END folded proof support: Crossing_circle_stage31_IV12_subtraction_case_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage32_IV12_diameter_cases_v2.lean -/
/-!
# Forder IV.12 -- stage 32, diameter endpoint cases

Forder separates the case in which the auxiliary opposite ray CX
continues directly through one of the endpoints A or B.

In the present synthetic formulation this is exactly the case in which

  A,K,C are collinear

or symmetrically

  B,K,C are collinear.

Then the corresponding chord AC (or BC) is a diameter.  Stage 16 gives
the center as its midpoint.  Euclid I.32 applied to the isosceles
triangle KBC (or KAC) decomposes the exterior central angle into the
two equal base angles.  This directly constructs the required
bisector witness for Forder IV.12.

No numerical angular measure is used.
-/

------------------------------------------------------------------------
-- 1. A,K,C collinear.
------------------------------------------------------------------------

theorem hilbert_forder_IV12_diameter_A_stage32
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hAKCcol : PrimCollinear Geo A K C) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  --------------------------------------------------------------------
  -- The inscribed angle ACB is proper.
  --------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC :
      Ne A C :=
    hilbert_noncollinear_ne_first
      Geo
      A C B
      hACB

  --------------------------------------------------------------------
  -- Put A,C,K on their carrier and use stage 16:
  -- K is the midpoint of the diameter AC.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC
    with
    ⟨lineAC,
      hAlineAC,
      hClineAC⟩

  have hACKcol :
      PrimCollinear Geo A C K :=
    PrimCollinearRotate
      Geo A K C hAKCcol

  have hKlineAC :
      H.OnLine K lineAC :=
    hilbert_collinear_on_line
      Geo
      A C K
      lineAC
      hAC
      hAlineAC
      hClineAC
      hACKcol

  have hMidK :
      HilbertIsMidpoint Geo K A C :=
    hilbert_circle_center_midpoint_of_chord_stage16
      Geo
      K R A C
      lineAC
      hAC
      hAlineAC
      hClineAC
      hKlineAC
      hAcircle
      hCcircle

  have hAKC :
      Geo.Between A K C :=
    hMidK.1

  have hAKCdata :=
    HilbertOrder.between_incidence
      A K C hAKC

  have hAK :
      Ne A K :=
    hAKCdata.1

  have hKC :
      Ne K C :=
    hAKCdata.2.1

  have hCK :
      Ne C K :=
    hKC.symm

  have hCKA :
      Geo.Between C K A :=
    hAKCdata.2.2.2.2

  --------------------------------------------------------------------
  -- Triangle BCK is proper.
  --------------------------------------------------------------------

  have hBCK :
      Not (PrimCollinear Geo B C K) := by
    intro h

    have hCKB :
        PrimCollinear Geo C K B :=
      PrimCollinearCycle
        Geo B C K h

    have hACBcol :
        PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo
        A C K B
        hCK
        hACKcol
        hCKB

    exact hACB hACBcol

  --------------------------------------------------------------------
  -- KB ~= KC, so triangle KBC is isosceles.
  --------------------------------------------------------------------

  have hKB_KC :
      Geo.Congruent K B K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      B C
      hBcircle
      hCcircle

  have hKBC :
      Not (PrimCollinear Geo K B C) := by
    intro h
    exact
      hBCK
        (PrimCollinearCycle
          Geo K B C h)

  have hIso :
      Geo.AngleCongruent
        K B C
        K C B :=
    hilbert_isosceles_base_angles
      Geo
      K B C
      hKBC
      hKB_KC

  have hCBK_BCK :
      Geo.AngleCongruent
        C B K
        B C K :=
    (Geo.angle_congruent_reverse_second
      C B K
      K C B).mp
      ((Geo.angle_congruent_reverse_first
        K B C
        K C B).mp
        hIso)

  --------------------------------------------------------------------
  -- I.32 on triangle BCK with CK produced through K to A.
  --
  -- It returns P inside the exterior angle BKA:
  --
  --   CBK ~= BKP,
  --   BCK ~= PKA.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B C K A
        hBCK
        hCKA
    with
    ⟨P,
      hBPA,
      hCBK_BKP,
      hBCK_PKA⟩

  --------------------------------------------------------------------
  -- The two I.32 components are congruent.
  --------------------------------------------------------------------

  have hBKP_CBK :
      Geo.AngleCongruent
        B K P
        C B K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C B K
      B K P
      hCBK_BKP

  have hBKP_BCK :
      Geo.AngleCongruent
        B K P
        B C K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B K P
      C B K
      B C K
      hBKP_CBK
      hCBK_BCK

  have hBKP_PKA :
      Geo.AngleCongruent
        B K P
        P K A :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B K P
      B C K
      P K A
      hBKP_BCK
      hBCK_PKA

  have hBKP_AKP :
      Geo.AngleCongruent
        B K P
        A K P :=
    (Geo.angle_congruent_reverse_second
      B K P
      P K A).mp
      hBKP_PKA

  have hBisect :
      Geo.AngleCongruent
        A K P
        B K P :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K P
      A K P
      hBKP_AKP

  --------------------------------------------------------------------
  -- P lies on chord AB, while K is off the chord.
  --------------------------------------------------------------------

  have hBPAdata :=
    HilbertOrder.between_incidence
      B P A hBPA

  have hBP :
      Ne B P :=
    hBPAdata.1

  have hBPAcol :
      PrimCollinear Geo B P A :=
    hBPAdata.2.2.2.1

  have hBAPcol :
      PrimCollinear Geo B A P :=
    PrimCollinearRotate
      Geo B P A hBPAcol

  have hPchord :
      H.OnLine P chord :=
    hilbert_collinear_on_line
      Geo
      B A P
      chord
      hAB.symm
      hBchord
      hAchord
      hBAPcol

  have hPK :
      Ne P K := by
    intro h
    subst P
    exact hKoff hPchord

  have hInsideP_BA :
      HilbertRayMeetsSegment Geo K P B A :=
    ⟨P,
      hBPA,
      hilbert_sameRay_refl
        Geo K P hPK⟩

  have hInsideP_AB :
      HilbertRayMeetsSegment Geo K P A B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K P B A
      hInsideP_BA

  --------------------------------------------------------------------
  -- From C, the points K and A are on the same ray.
  -- Hence angle ACB is the same angle as KCB.
  --------------------------------------------------------------------

  have hRayCKA :
      HilbertSameRay Geo C K A :=
    hilbert_sameRay_of_between
      Geo C K A hCKA

  have hRayCAK :
      HilbertSameRay Geo C A K :=
    hilbert_sameRay_symm
      Geo C K A hRayCKA

  have hAngleEq :
      Geo.Angle A C B =
      Geo.Angle K C B :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      C A K B
      hRayCAK

  have hKCB_PKA :
      Geo.AngleCongruent
        K C B
        P K A :=
    (Geo.angle_congruent_reverse_first
      B C K
      P K A).mp
      hBCK_PKA

  have hKCB_AKP :
      Geo.AngleCongruent
        K C B
        A K P :=
    (Geo.angle_congruent_reverse_second
      K C B
      P K A).mp
      hKCB_PKA

  have hACB_AKP :
      Geo.AngleCongruent
        A C B
        A K P := by
    unfold Geometry.Geo.AngleCongruent at hKCB_AKP
    unfold Geometry.Geo.AngleCongruent
    rw [hAngleEq]
    exact hKCB_AKP

  exact
    ⟨P,
      hInsideP_AB,
      hBisect,
      hACB_AKP⟩


------------------------------------------------------------------------
-- 2. B,K,C collinear: symmetric wrapper.
------------------------------------------------------------------------

theorem hilbert_forder_IV12_diameter_B_stage32
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hBKCcol : PrimCollinear Geo B K C) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  rcases
      hilbert_forder_IV12_diameter_A_stage32
        Geo
        K R B A C
        chord
        hAB.symm
        hBchord
        hAchord
        hBcircle
        hAcircle
        hCcircle
        hSameCK
        hBKCcol
    with
    ⟨E,
      hInsideE_BA,
      hBisectBA,
      hBCA_BKE⟩

  have hInsideE_AB :
      HilbertRayMeetsSegment Geo K E A B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K E B A
      hInsideE_BA

  have hBisect :
      Geo.AngleCongruent
        A K E
        B K E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K E
      A K E
      hBisectBA

  have hACB_BKE :
      Geo.AngleCongruent
        A C B
        B K E :=
    (Geo.angle_congruent_reverse_first
      B C A
      B K E).mp
      hBCA_BKE

  have hBisectSymm :
      Geo.AngleCongruent
        B K E
        A K E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K E
      B K E
      hBisect

  have hACB_AKE :
      Geo.AngleCongruent
        A C B
        A K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C B
      B K E
      A K E
      hACB_BKE
      hBisectSymm

  exact
    ⟨E,
      hInsideE_AB,
      hBisect,
      hACB_AKE⟩
/- END folded proof support: Crossing_circle_stage32_IV12_diameter_cases_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage33_IV12_complete_v1.lean -/
/-!
# Forder IV.12 -- stage 33, complete theorem

Stages 27, 31, and 32 prove the three geometric branches of Forder IV.12:

* the axis through C and K passes through A or B: diameter endpoint case;
* A and B are on opposite sides of the axis: addition case;
* A and B are on the same side of the axis: subtraction case.

This file only performs the exhaustive plane-separation classification.

For each circle point C, stage 14 constructs the antipodal point X with

  C-K-X.

The line KX is the reference axis.  If A or B lies on that axis, stage 32
applies.  Otherwise A and B are both off the axis; they are either on the
same side, giving stage 31, or not on the same side, which by plane
separation means that they are on opposite sides, giving stage 27.

No new geometric argument is introduced here.
-/

/--
Complete synthetic proof of Forder IV.12.

For A,B,C on a circle centered at K, with C and K on the same side of
chord AB, there exists an interior bisector KT of angle AKB such that

  angle ACB ~= angle AKT.
-/
theorem hilbert_forder_IV12_central_half_stage33
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV12CentralHalf
      (Geo := Geo) := by

  intro K R A B C chord
    hAB
    hAchord
    hBchord
    hAcircle
    hBcircle
    hCcircle
    hSameCK

  --------------------------------------------------------------------
  -- Construct the antipodal extension C-K-X.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_antipode_stage14
        Geo
        K R A B C
        hAB
        hAcircle
        hBcircle
        hCcircle
    with
    ⟨X,
      hCKX,
      _hXcircle⟩

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  --------------------------------------------------------------------
  -- Reference axis KX.  Since C,K,X are collinear, C lies on it too.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        K X hKX
    with
    ⟨axis,
      hKaxis,
      hXaxis⟩

  have hKXC :
      PrimCollinear Geo K X C :=
    PrimCollinearCycle
      Geo C K X hCKXcol

  have hCaxis :
      H.OnLine C axis :=
    hilbert_collinear_on_line
      Geo
      K X C
      axis
      hKX
      hKaxis
      hXaxis
      hKXC

  --------------------------------------------------------------------
  -- First exceptional branch: A lies on the axis.
  --------------------------------------------------------------------

  by_cases hAaxis : H.OnLine A axis

  · have hAKCcol :
        PrimCollinear Geo A K C :=
      ⟨axis,
        hAaxis,
        hKaxis,
        hCaxis⟩

    exact
      hilbert_forder_IV12_diameter_A_stage32
        Geo
        K R A B C
        chord
        hAB
        hAchord
        hBchord
        hAcircle
        hBcircle
        hCcircle
        hSameCK
        hAKCcol

  --------------------------------------------------------------------
  -- Second exceptional branch: B lies on the axis.
  --------------------------------------------------------------------

  · by_cases hBaxis : H.OnLine B axis

    · have hBKCcol :
          PrimCollinear Geo B K C :=
        ⟨axis,
          hBaxis,
          hKaxis,
          hCaxis⟩

      exact
        hilbert_forder_IV12_diameter_B_stage32
          Geo
          K R A B C
          chord
          hAB
          hAchord
          hBchord
          hAcircle
          hBcircle
          hCcircle
          hSameCK
          hBKCcol

    ------------------------------------------------------------------
    -- Generic case: A and B are both off the axis.
    ------------------------------------------------------------------

    · by_cases hSameAB :
          HilbertSameSide Geo A B axis

      ---------------------------------------------------------------
      -- Same side: Forder's subtraction branch.
      ---------------------------------------------------------------

      · exact
          hilbert_forder_IV12_subtraction_case_stage31
            Geo
            K R A B C X
            chord axis
            hAB
            hAchord
            hBchord
            hKaxis
            hXaxis
            hAcircle
            hBcircle
            hCcircle
            hSameCK
            hCKX
            hSameAB

      ---------------------------------------------------------------
      -- Not same side: since both points are off the axis, they are
      -- on opposite sides.  This is Forder's addition branch.
      ---------------------------------------------------------------

      · have hOppAB :
            HilbertOppositeSide Geo A B axis :=
          hilbert_oppositeSide_of_not_sameSide
            Geo
            A B
            axis
            hAaxis
            hBaxis
            hSameAB

        exact
          hilbert_forder_IV12_addition_case_stage27
            Geo
            K R A B C X
            chord axis
            hAB
            hAchord
            hBchord
            hKaxis
            hXaxis
            hAcircle
            hBcircle
            hCcircle
            hSameCK
            hCKX
            hOppAB
/- END folded proof support: Crossing_circle_stage33_IV12_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage34_IV12_1_complete_v1.lean -/
/-!
# Forder IV.12.1 -- stage 34, completed corollary

Stage 33 proves the full synthetic form of Forder IV.12.

Stage 18 already proved, abstractly, that IV.12 implies IV.12.1:
two inscribed angles standing on the same chord and lying in the same
segment are congruent.

This file is therefore only the final closed corollary.
-/

/--
Complete Forder IV.12.1.

If A,B,C,D lie on one circle centered at K and C,D,K lie in the same
half-plane determined by chord AB, then

  angle ACB ~= angle ADB.
-/
theorem hilbert_forder_IV12_1_same_segment_stage34
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV12_1SameSegment
      (Geo := Geo) := by

  exact
    hilbert_forder_IV12_1_of_IV12_stage18
      Geo
      (hilbert_forder_IV12_central_half_stage33
        Geo)
/- END folded proof support: Crossing_circle_stage34_IV12_1_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage35_right_triangle_third_angle_v1.lean -/
/-!
# Forder IV.14 -- stage 35, right-triangle third-angle theorem

A clean neutral helper needed for Forder IV.14.

An older experimental proof of this theorem already existed in the
segment-arithmetic development, but it depended on an unproved angle
subtraction placeholder.  The present proof uses the production theorem

  hilbert_angleDecomposition_angle_subtraction_right

from `HilbertAngleDecomposition`, so the result is fully synthetic and
contains no new axiom or `sorry`.
-/

/--
Two right triangles with one pair of corresponding acute angles
congruent have the other pair congruent.

The right angles are at O and O'.  The hypothesis `hAngleB` identifies
the angles at B and B'.  The conclusion identifies the remaining angles
at A and A'.
-/
theorem hilbert_right_triangle_third_angle_congruent_stage35
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A B O' A' B' : Geo.Point)
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B')
    (hNoncol : Not (PrimCollinear Geo O A B))
    (hNoncol' : Not (PrimCollinear Geo O' A' B'))
    (hAngleB :
      Geo.AngleCongruent
        A B O
        A' B' O') :
    Geo.AngleCongruent
      O A B
      O' A' B' := by

  --------------------------------------------------------------------
  -- Extend A-O and A'-O' beyond the right-angle vertices.
  --------------------------------------------------------------------

  have hAO :
      Ne A O :=
    (hilbert_noncollinear_ne_first
      Geo O A B hNoncol).symm

  have hA'O' :
      Ne A' O' :=
    (hilbert_noncollinear_ne_first
      Geo O' A' B' hNoncol').symm

  rcases
      HilbertOrder.between_extension
        A O hAO
    with
    ⟨C, hAOC⟩

  rcases
      HilbertOrder.between_extension
        A' O' hA'O'
    with
    ⟨C', hA'O'C'⟩

  have hBAO :
      Not (PrimCollinear Geo B A O) := by
    intro h
    exact
      hNoncol
        (PrimCollinearRotate
          Geo O B A
          (PrimCollinearSwap
            Geo B O A
            (PrimCollinearRotate
              Geo B A O h)))

  have hB'A'O' :
      Not (PrimCollinear Geo B' A' O') := by
    intro h
    exact
      hNoncol'
        (PrimCollinearRotate
          Geo O' B' A'
          (PrimCollinearSwap
            Geo B' O' A'
            (PrimCollinearRotate
              Geo B' A' O' h)))

  --------------------------------------------------------------------
  -- I.32 decomposes the two exterior angles.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B A O C
        hBAO
        hAOC
    with
    ⟨R,
      hBRC,
      hPart1,
      hPart2⟩

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B' A' O' C'
        hB'A'O'
        hA'O'C'
    with
    ⟨R',
      hB'R'C',
      hPart1',
      hPart2'⟩

  --------------------------------------------------------------------
  -- The supplements of the two right angles are congruent.
  --------------------------------------------------------------------

  have hNoncolAOB :
      Not (PrimCollinear Geo A O B) := by
    intro h
    exact
      hNoncol
        (PrimCollinearSwap
          Geo A O B h)

  have hNoncolA'O'B' :
      Not (PrimCollinear Geo A' O' B') := by
    intro h
    exact
      hNoncol'
        (PrimCollinearSwap
          Geo A' O' B' h)

  have hRightCong :
      Geo.AngleCongruent
        A O B
        A' O' B' :=
    hilbert_all_right_angles_congruent
      Geo
      A O B
      A' O' B'
      hNoncolAOB
      hNoncolA'O'B'
      hRight
      hRight'

  have hSupp :
      Geo.AngleCongruent
        B O C
        B' O' C' :=
    hilbert_adjacent_angles_congruent
      Geo
      A O B C
      A' O' B' C'
      hAOC
      hA'O'C'
      hNoncolAOB
      hNoncolA'O'B'
      hRightCong

  --------------------------------------------------------------------
  -- First components of the two exterior decompositions are equal.
  --------------------------------------------------------------------

  have hBOR_ABO :
      Geo.AngleCongruent
        B O R
        A B O :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B O
      B O R
      hPart1

  have hBOR_AngleB :
      Geo.AngleCongruent
        B O R
        A' B' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O R
      A B O
      A' B' O'
      hBOR_ABO
      hAngleB

  have hAngleB_B'O'R' :
      Geo.AngleCongruent
        A' B' O'
        B' O' R' :=
    hPart1'

  have hBOR_B'O'R' :
      Geo.AngleCongruent
        B O R
        B' O' R' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O R
      A' B' O'
      B' O' R'
      hBOR_AngleB
      hAngleB_B'O'R'

  --------------------------------------------------------------------
  -- The I.32 witnesses are interior rays of the exterior angles.
  --------------------------------------------------------------------

  have hOC :
      Ne O C :=
    (HilbertOrder.between_incidence
      A O C hAOC).2.1

  have hACO :
      PrimCollinear Geo A C O :=
    PrimCollinearRotate
      Geo A O C
      (HilbertOrder.between_incidence
        A O C hAOC).2.2.2.1

  have hBOC :
      Not (PrimCollinear Geo B O C) := by
    intro h
    rcases h with
      ⟨l, hBl, hOl, hCl⟩
    rcases hACO with
      ⟨m, hAm, hCm, hOm⟩
    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O C hOC
        l m
        hOl hCl
        hOm hCm
    exact
      hNoncol
        ⟨m,
          hOm,
          hAm,
          hlm ▸ hBl⟩

  have hO'C' :
      Ne O' C' :=
    (HilbertOrder.between_incidence
      A' O' C' hA'O'C').2.1

  have hA'C'O' :
      PrimCollinear Geo A' C' O' :=
    PrimCollinearRotate
      Geo A' O' C'
      (HilbertOrder.between_incidence
        A' O' C' hA'O'C').2.2.2.1

  have hB'O'C' :
      Not (PrimCollinear Geo B' O' C') := by
    intro h
    rcases h with
      ⟨l, hB'l, hO'l, hC'l⟩
    rcases hA'C'O' with
      ⟨m, hA'm, hC'm, hO'm⟩
    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O' C' hO'C'
        l m
        hO'l hC'l
        hO'm hC'm
    exact
      hNoncol'
        ⟨m,
          hO'm,
          hA'm,
          hlm ▸ hB'l⟩

  have hRO :
      Ne R O := by
    intro h
    apply hBOC
    have hPrim :
        PrimCollinear Geo B R C :=
      (HilbertOrder.between_incidence
        B R C hBRC).2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hR'O' :
      Ne R' O' := by
    intro h
    apply hB'O'C'
    have hPrim :
        PrimCollinear Geo B' R' C' :=
      (HilbertOrder.between_incidence
        B' R' C' hB'R'C').2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hRInside :
      HilbertRayMeetsSegment Geo O R B C :=
    ⟨R,
      hBRC,
      hilbert_sameRay_refl
        Geo O R hRO⟩

  have hR'Inside :
      HilbertRayMeetsSegment Geo O' R' B' C' :=
    ⟨R',
      hB'R'C',
      hilbert_sameRay_refl
        Geo O' R' hR'O'⟩

  --------------------------------------------------------------------
  -- Clean Common-Notion subtraction.
  --------------------------------------------------------------------

  have hCOR_C'O'R' :
      Geo.AngleCongruent
        C O R
        C' O' R' :=
    hilbert_angleDecomposition_angle_subtraction_right
      Geo
      O B C R
      B' O' C' R'
      hBOC
      hB'O'C'
      hRInside
      hR'Inside
      hSupp
      hBOR_B'O'R'

  have hROC_R'O'C' :
      Geo.AngleCongruent
        R O C
        R' O' C' :=
    AngleCongruentReverse
      Geo
      C O R
      C' O' R'
      hCOR_C'O'R'

  --------------------------------------------------------------------
  -- Normalize the I.32 second components to the required third angles.
  --------------------------------------------------------------------

  have hFinal1 :
      Geo.AngleCongruent
        B A O
        R' O' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A O
      R O C
      R' O' C'
      hPart2
      hROC_R'O'C'

  have hFinal2 :
      Geo.AngleCongruent
        B A O
        B' A' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A O
      R' O' C'
      B' A' O'
      hFinal1
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B' A' O'
        R' O' C'
        hPart2')

  have hFinal3 :
      Geo.AngleCongruent
        O A B
        B' A' O' :=
    (Geo.angle_congruent_reverse_first
      B A O
      B' A' O').mp
      hFinal2

  exact
    (Geo.angle_congruent_reverse_second
      O A B
      B' A' O').mp
      hFinal3
/- END folded proof support: Crossing_circle_stage35_right_triangle_third_angle_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage36_diameter_right_decomposition_v1.lean -/
/-!
# Forder IV.14 -- stage 36, diameter right-angle decomposition

This stage isolates the local diameter block used twice in Forder IV.14.

Let AC be a diameter of a circle centered at K and let B be another
circle point off the diameter. Forder IV.13 gives

  angle ABC right.

Extend AB through B to E. The adjacent angle CBE is right as well.
Euclid I.32 applied to triangle C-A-B with A-B-E produces a point P
strictly between C and E such that

  angle ACB ~= angle CBP,
  angle CAB ~= angle PBE.

Thus the right angle CBE is decomposed into the two acute angles of
triangle ABC, entirely synthetically and without angle measures.
-/

/--
Diameter right-angle decomposition.

For a diameter AC and a circle point B off its carrier, there are
points E and P with

  A-B-E,
  C-P-E,

such that CBE is right and the two I.32 component angles are precisely
the two acute angles of triangle ABC.
-/
theorem hilbert_forder_diameter_right_decomposition_stage36
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hBoff : Not (H.OnLine B diameter)) :
    exists E P : Geo.Point,
      Geo.Between A B E /\
      HilbertRightAngle Geo C B E /\
      Geo.Between C P E /\
      Geo.AngleCongruent A C B C B P /\
      Geo.AngleCongruent C A B P B E := by

  --------------------------------------------------------------------
  -- Triangle ABC is proper because B is off the diameter AC.
  --------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) := by
    intro h

    have hACBcol :
        PrimCollinear Geo A C B :=
      PrimCollinearRotate
        Geo A B C h

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        A C B
        diameter
        hAC
        hAdiam
        hCdiam
        hACBcol

    exact hBoff hBdiam

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hCBA :
      Not (PrimCollinear Geo C B A) := by
    intro h
    exact
      hABC
        (PrimCollinearSymm
          Geo C B A h)

  have hCAB :
      Not (PrimCollinear Geo C A B) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B h)

  --------------------------------------------------------------------
  -- Forder IV.13: the angle ABC standing on diameter AC is right.
  --------------------------------------------------------------------

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R A C B
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle
      hBcircle
      hBoff

  have hRightCBA :
      HilbertRightAngle Geo C B A :=
    proposition2_12_right_angle_swap
      Geo
      A B C
      hABC
      hRightABC

  --------------------------------------------------------------------
  -- Extend AB through B.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A B hAB
    with
    ⟨E, hABE⟩

  --------------------------------------------------------------------
  -- The adjacent angle CBE is right as well.
  --------------------------------------------------------------------

  have hRightCBE :
      HilbertRightAngle Geo C B E :=
    proposition2_13_right_angle_other_side
      Geo
      C A E B
      hABE
      hCBA
      hRightCBA

  --------------------------------------------------------------------
  -- Euclid I.32 on triangle C-A-B, with AB extended through B to E.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        C A B E
        hCAB
        hABE
    with
    ⟨P,
      hCPE,
      hACB_CBP,
      hCAB_PBE⟩

  exact
    ⟨E,
      P,
      hABE,
      hRightCBE,
      hCPE,
      hACB_CBP,
      hCAB_PBE⟩
/- END folded proof support: Crossing_circle_stage36_diameter_right_decomposition_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage37_diameter_chord_intersection_v2.lean -/
/-!
# Forder IV.14 -- stage 37, a chord crosses a diameter internally

Forder's proof of IV.14 says that the chord BD and the diameter AC meet.
The diagram silently uses the stronger fact that their intersection lies
inside the diameter AC.

This stage makes that order fact explicit.

Let AC be a diameter of a circle centered at K, and let B,D be circle
points on opposite sides of the diameter line.  The opposite-side
witness gives Y with

  B-Y-D

and Y on AC.

If K lies on chord BD, uniqueness of the intersection of the two
carriers gives Y = K, hence A-Y-C.

Otherwise Y is an interior point of chord BD and stage 20 gives

  KY < KB.

Since all circle radii are congruent,

  KY < KA.

The two exterior orders on the diameter would force the reverse strict
inequality.  Trichotomy therefore leaves only

  A-Y-C.

No continuity or coordinate argument is used.
-/

/--
If a chord BD crosses a diameter AC, then its crossing point lies
strictly inside the diameter.
-/
theorem hilbert_forder_diameter_chord_intersection_inside_stage37
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists Y : Geo.Point,
      Geo.Between B Y D /\
      H.OnLine Y diameter /\
      Geo.Between A Y C := by

  --------------------------------------------------------------------
  -- The diameter center is the midpoint of AC.
  --------------------------------------------------------------------

  have hMidK :
      HilbertIsMidpoint Geo K A C :=
    hilbert_circle_center_midpoint_of_chord_stage16
      Geo
      K R A C
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle

  have hAKC :
      Geo.Between A K C :=
    hMidK.1

  have hKA_KC :
      Geo.Congruent K A K C :=
    CongruentReverseFirst
      Geo
      A K
      K C
      hMidK.2

  --------------------------------------------------------------------
  -- Opposite-side data supplies the crossing point Y.
  --------------------------------------------------------------------

  rcases hOppBD.2.2 with
    ⟨Y, hBYD, hYdiam⟩

  have hBYDdata :=
    HilbertOrder.between_incidence
      B Y D hBYD

  have hBD :
      Ne B D :=
    hBYDdata.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        B D hBD
    with
    ⟨chord,
      hBchord,
      hDchord⟩

  have hYchord :
      H.OnLine Y chord :=
    hilbert_between_on_line
      Geo
      B Y D
      chord
      hBchord
      hDchord
      hBYD

  --------------------------------------------------------------------
  -- If K is also on chord BD, the two carriers meet at both K and Y.
  -- Hence Y = K, unless the carriers coincide; the latter would put B
  -- on the diameter, contradicting opposite-side data.
  --------------------------------------------------------------------

  by_cases hKchord :
      H.OnLine K chord

  · have hYK :
        Y = K := by
      by_contra hYK

      have hEq :
          diameter = chord :=
        HilbertPlaneIncidence.line_unique
          Y K hYK
          diameter chord
          hYdiam hKdiam
          hYchord hKchord

      have hBdiam :
          H.OnLine B diameter := by
        rw [hEq]
        exact hBchord

      exact hOppBD.1 hBdiam

    subst Y

    exact
      ⟨K,
        hBYD,
        hKdiam,
        hAKC⟩

  --------------------------------------------------------------------
  -- Otherwise Y is an interior point of a non-diameter chord BD.
  -- Stage 20 places it strictly inside the circle.
  --------------------------------------------------------------------

  · have hKY_KB :
        HilbertSegmentLess Geo K Y K B :=
      hilbert_circle_chord_inner_point_inside_stage20
        Geo
        K R B D Y
        chord
        hBD
        hBchord
        hDchord
        hKchord
        hBcircle
        hDcircle
        hBYD

    have hKB_KA :
        Geo.Congruent K B K A :=
      hilbert_circle_center_congruent
        Geo
        K R
        B A
        hBcircle
        hAcircle

    have hKY_KA :
        HilbertSegmentLess Geo K Y K A :=
      hilbert_segmentLess_congruent_right
        Geo
        K Y
        K B
        K A
        hKY_KB
        hKB_KA

    ------------------------------------------------------------------
    -- Y is a proper point distinct from the diameter endpoints.
    ------------------------------------------------------------------

    have hAY :
        Ne A Y := by
      intro hAY
      subst Y

      have hKA_KA :
          Geo.Congruent K A K A :=
        hilbert_congruent_reflexive
          Geo K A

      exact
        (hilbert_segmentLess_not_congruent
          Geo
          K A
          K A
          hKY_KA)
          hKA_KA

    have hYC :
        Ne Y C := by
      intro hYC
      subst Y

      have hKC_KA :
          Geo.Congruent K C K A :=
        hilbert_congruent_symmetry
          Geo
          K A
          K C
          hKA_KC

      exact
        (hilbert_segmentLess_not_congruent
          Geo
          K C
          K A
          hKY_KA)
          hKC_KA

    have hAYCcol :
        PrimCollinear Geo A Y C :=
      ⟨diameter,
        hAdiam,
        hYdiam,
        hCdiam⟩

    ------------------------------------------------------------------
    -- Trichotomy on the diameter carrier.
    ------------------------------------------------------------------

    rcases
        hilbert_between_trichotomy
          Geo
          A Y C
          hAY
          hYC
          hAC
          hAYCcol
      with
      hAYC | hYAC | hACY

    ------------------------------------------------------------------
    -- Desired internal order.
    ------------------------------------------------------------------

    · exact
        ⟨Y,
          hBYD,
          hYdiam,
          hAYC⟩

    ------------------------------------------------------------------
    -- Exterior order Y-A-C forces KA < KY.
    ------------------------------------------------------------------

    · have hCAY :
          Geo.Between C A Y :=
        (HilbertOrder.between_incidence
          Y A C hYAC).2.2.2.2

      have hCKA :
          Geo.Between C K A :=
        (HilbertOrder.between_incidence
          A K C hAKC).2.2.2.2

      have hKAY :
          Geo.Between K A Y :=
        (hilbert_between_inner_trans
          Geo
          C K A Y
          hCKA
          hCAY).1

      have hKA_KY :
          HilbertSegmentLess Geo K A K Y :=
        hilbert_segmentLess_of_between
          Geo
          K A Y
          hKAY

      exact
        False.elim
          ((hilbert_segmentLess_asymm
              Geo
              K Y
              K A
              hKY_KA)
            hKA_KY)

    ------------------------------------------------------------------
    -- Exterior order A-C-Y forces KC < KY, hence KA < KY.
    ------------------------------------------------------------------

    · have hKCY :
          Geo.Between K C Y :=
        (hilbert_between_inner_trans
          Geo
          A K C Y
          hAKC
          hACY).1

      have hKC_KY :
          HilbertSegmentLess Geo K C K Y :=
        hilbert_segmentLess_of_between
          Geo
          K C Y
          hKCY

      have hKA_KY :
          HilbertSegmentLess Geo K A K Y :=
        hilbert_segmentLess_congruent_left
          Geo
          K C
          K A
          K Y
          hKC_KY
          hKA_KC

      exact
        False.elim
          ((hilbert_segmentLess_asymm
              Geo
              K Y
              K A
              hKY_KA)
            hKA_KY)
/- END folded proof support: Crossing_circle_stage37_diameter_chord_intersection_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage38_IV14_diameter_rays_inside_v1.lean -/
/-!
# Forder IV.14 -- stage 38, the diameter rays are interior

Stage 37 made explicit the hidden order statement in Forder IV.14:
if the chord BD crosses the diameter AC, then the crossing point Y lies
strictly inside both segments,

  A-Y-C,
  B-Y-D.

This file converts that crossing configuration into the exact
`HilbertRayMeetsSegment` statements needed by the angle-decomposition API:

  ray AC is interior to angle BAD,
  ray CA is interior to angle BCD.

No angle theorem is used here.
-/

/--
In the IV.14 diameter configuration, the two opposite diameter rays are
the interior dividing rays of the two angles BAD and BCD.
-/
theorem hilbert_forder_IV14_diameter_rays_inside_stage38
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    HilbertRayMeetsSegment Geo A C B D /\
    HilbertRayMeetsSegment Geo C A B D := by

  rcases
      hilbert_forder_diameter_chord_intersection_inside_stage37
        Geo
        K R A B C D
        diameter
        hAC
        hAdiam
        hCdiam
        hKdiam
        hAcircle
        hBcircle
        hCcircle
        hDcircle
        hOppBD
    with
    ⟨Y,
      hBYD,
      _hYdiam,
      hAYC⟩

  --------------------------------------------------------------------
  -- From A-Y-C, Y and C lie on the same ray from A.
  --------------------------------------------------------------------

  have hRayAYC :
      HilbertSameRay Geo A Y C :=
    hilbert_sameRay_of_between
      Geo A Y C hAYC

  have hRayACY :
      HilbertSameRay Geo A C Y :=
    hilbert_sameRay_symm
      Geo A Y C hRayAYC

  have hInsideAC :
      HilbertRayMeetsSegment Geo A C B D :=
    ⟨Y,
      hBYD,
      hRayACY⟩

  --------------------------------------------------------------------
  -- Reverse A-Y-C to C-Y-A.  Thus Y and A lie on the same ray from C.
  --------------------------------------------------------------------

  have hCYA :
      Geo.Between C Y A :=
    (HilbertOrder.between_incidence
      A Y C hAYC).2.2.2.2

  have hRayCYA :
      HilbertSameRay Geo C Y A :=
    hilbert_sameRay_of_between
      Geo C Y A hCYA

  have hRayCAY :
      HilbertSameRay Geo C A Y :=
    hilbert_sameRay_symm
      Geo C Y A hRayCYA

  have hInsideCA :
      HilbertRayMeetsSegment Geo C A B D :=
    ⟨Y,
      hBYD,
      hRayCAY⟩

  exact
    ⟨hInsideAC,
      hInsideCA⟩
/- END folded proof support: Crossing_circle_stage38_IV14_diameter_rays_inside_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage39_IV14_prescribed_perpendicular_v1.lean -/
/-!
# Forder IV.14 -- stage 39, prescribed-side perpendicular at C

For the IV.14 diameter configuration, construct at C a ray CP
perpendicular to the diameter AC and lying on the prescribed side of AC,
namely the side containing D.

The construction is entirely Hilbertian:

* IV.13 supplies the right angle ABC;
* Hilbert III.4 copies that angle to the ray CA at C, on the side of
  the diameter containing D;
* right-angle transport turns the copied congruent angle into a right
  angle.

No Euclidean angle measure is used.
-/

/--
In the IV.14 diameter configuration there exists a point P on the same
side of the diameter as D such that angle ACP is right.
-/
theorem hilbert_forder_IV14_prescribed_perpendicular_stage39
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (_hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists P : Geo.Point,
      HilbertSameSide Geo P D diameter /\
      HilbertRightAngle Geo A C P := by

  have hBoff :
      Not (H.OnLine B diameter) :=
    hOppBD.1

  have hDoff :
      Not (H.OnLine D diameter) :=
    hOppBD.2.1

  --------------------------------------------------------------------
  -- Triangle ABC is proper because B is off the diameter AC.
  --------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) := by
    intro h

    have hACBcol :
        PrimCollinear Geo A C B :=
      PrimCollinearRotate
        Geo A B C h

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        A C B
        diameter
        hAC
        hAdiam
        hCdiam
        hACBcol

    exact hBoff hBdiam

  --------------------------------------------------------------------
  -- Forder IV.13: angle ABC is right because AC is a diameter.
  --------------------------------------------------------------------

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R A C B
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle
      hBcircle
      hBoff

  --------------------------------------------------------------------
  -- Copy the right angle ABC to A-C-P on the side containing D.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A B C
        A C D
        hABC
        hAC
        diameter
        hAdiam
        hCdiam
        hDoff
    with
    ⟨P,
      hPDSame,
      hABC_ACP,
      _hUnique⟩

  have hPoff :
      Not (H.OnLine P diameter) :=
    hPDSame.1

  have hACP :
      Not (PrimCollinear Geo A C P) :=
    hilbert_not_collinear_of_off_line
      Geo
      A C P
      diameter
      hAC
      hAdiam
      hCdiam
      hPoff

  have hRightACP :
      HilbertRightAngle Geo A C P :=
    hilbert_right_angle_transport
      Geo
      A B C
      A C P
      hABC
      hACP
      hRightABC
      hABC_ACP

  exact
    ⟨P,
      hPDSame,
      hRightACP⟩
/- END folded proof support: Crossing_circle_stage39_IV14_prescribed_perpendicular_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage40_IV14_perpendicular_inside_supplement_v3.lean -/
/-!
# Forder IV.14 -- stage 40, the perpendicular lies inside the supplement

Let AC be a diameter, with B and D on opposite sides of AC.
Stage 39 constructs a point P on the D-side of AC with angle ACP right.

Now extend BC through C to X:

  B-C-X.

The target supplementary angle for IV.14 is XCD, because

  BookZeroSupplement Geo B C D D X

is represented by the straight extension B-C-X.

This stage proves that CP is an interior ray of angle XCD.

The proof is synthetic:

1. I.16 in triangle ABC gives the right angle ABC strictly smaller than
   the exterior angle ACX.  Since ACP is also right, ACP < ACX.
   Hence CP is interior to ACX.

2. In the right triangle ADC, the acute angle ACD is strictly smaller
   than the right angle ACP.  Hence CD is interior to ACP.

3. Reverse the first nesting and apply the stage-26 parent-divider
   theorem.  From

     P inside A-C-X,
     D inside A-C-P

   one obtains

     P inside X-C-D.

No numerical angle measure is used.
-/

/--
In the IV.14 configuration, after extending BC through C to X and
constructing the prescribed-side perpendicular CP, the ray CP lies
strictly inside the supplementary angle XCD.
-/
theorem hilbert_forder_IV14_perpendicular_inside_supplement_stage40
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists X P : Geo.Point,
      Geo.Between B C X /\
      HilbertSameSide Geo P D diameter /\
      HilbertRightAngle Geo A C P /\
      HilbertRayMeetsSegment Geo C P A X /\
      HilbertRayMeetsSegment Geo C D A P /\
      HilbertRayMeetsSegment Geo C P X D := by

  have hBoff :
      Not (H.OnLine B diameter) :=
    hOppBD.1

  have hDoff :
      Not (H.OnLine D diameter) :=
    hOppBD.2.1

  --------------------------------------------------------------------
  -- Proper triangles ABC and ACD.
  --------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) := by
    intro h

    have hACBcol :
        PrimCollinear Geo A C B :=
      PrimCollinearRotate
        Geo A B C h

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        A C B
        diameter
        hAC
        hAdiam
        hCdiam
        hACBcol

    exact hBoff hBdiam

  have hACD :
      Not (PrimCollinear Geo A C D) :=
    hilbert_not_collinear_of_off_line
      Geo
      A C D
      diameter
      hAC
      hAdiam
      hCdiam
      hDoff

  have hDAC :
      Not (PrimCollinear Geo D A C) := by
    intro h
    exact
      hACD
        (PrimCollinearCycle
          Geo D A C h)

  --------------------------------------------------------------------
  -- Both diameter angles at B and D are right.
  --------------------------------------------------------------------

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R A C B
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle
      hBcircle
      hBoff

  have hRightADC :
      HilbertRightAngle Geo A D C :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R A C D
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle
      hDcircle
      hDoff

  --------------------------------------------------------------------
  -- Prescribed-side perpendicular CP.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV14_prescribed_perpendicular_stage39
        Geo
        K R A B C D
        diameter
        hAC
        hAdiam
        hCdiam
        hKdiam
        hAcircle
        hBcircle
        hCcircle
        hDcircle
        hOppBD
    with
    ⟨P,
      hPDSame,
      hRightACP⟩

  have hPoff :
      Not (H.OnLine P diameter) :=
    hPDSame.1

  have hACP :
      Not (PrimCollinear Geo A C P) :=
    hilbert_not_collinear_of_off_line
      Geo
      A C P
      diameter
      hAC
      hAdiam
      hCdiam
      hPoff

  --------------------------------------------------------------------
  -- Extend BC through C to X.  This is the supplementary ray required
  -- by BookZeroSupplement for angle BCD.
  --------------------------------------------------------------------

  have hBC :
      Ne B C := by
    intro h
    subst B
    exact hBoff hCdiam

  rcases
      HilbertOrder.between_extension
        B C hBC
    with
    ⟨X, hBCX⟩

  have hBCXdata :=
    HilbertOrder.between_incidence
      B C X hBCX

  have hCX :
      Ne C X :=
    hBCXdata.2.1

  have hBCXcol :
      PrimCollinear Geo B C X :=
    hBCXdata.2.2.2.1

  --------------------------------------------------------------------
  -- X is off the diameter.
  --------------------------------------------------------------------

  have hXoff :
      Not (H.OnLine X diameter) := by
    intro hXdiam

    have hCXB :
        PrimCollinear Geo C X B :=
      PrimCollinearCycle
        Geo B C X hBCXcol

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        C X B
        diameter
        hCX
        hCdiam
        hXdiam
        hCXB

    exact hBoff hBdiam

  --------------------------------------------------------------------
  -- B and P are opposite sides of the diameter.
  --------------------------------------------------------------------

  have hDPSame :
      HilbertSameSide Geo D P diameter :=
    hilbert_sameSide_symm
      Geo P D diameter hPDSame

  have hOppBP :
      HilbertOppositeSide Geo B P diameter :=
    hilbert_oppositeSide_transport_right
      Geo
      B D P
      diameter
      hOppBD
      hDPSame

  --------------------------------------------------------------------
  -- P and X lie on the same side of the diameter.
  --
  -- In the generic branch this is the standard opposite-extension
  -- theorem.  The collinear branch is normalized directly from the
  -- two extensions B-C-X and B-C-P.
  --------------------------------------------------------------------

  have hPXSame :
      HilbertSameSide Geo P X diameter := by

    by_cases hBCP :
        PrimCollinear Geo B C P

    · ----------------------------------------------------------------
      -- Collinear branch: the opposite-side crossing B--P on the
      -- diameter must occur at C.
      ----------------------------------------------------------------

      rcases
          HilbertPlaneIncidence.line_through
            B C hBC
        with
        ⟨carrier,
          hBcarrier,
          hCcarrier⟩

      have hPcarrier :
          H.OnLine P carrier :=
        hilbert_collinear_on_line
          Geo
          B C P
          carrier
          hBC
          hBcarrier
          hCcarrier
          hBCP

      rcases hOppBP.2.2 with
        ⟨Y, hBYP, hYdiam⟩

      have hYcarrier :
          H.OnLine Y carrier :=
        hilbert_between_on_line
          Geo
          B Y P
          carrier
          hBcarrier
          hPcarrier
          hBYP

      have hYC :
          Y = C := by
        by_contra hYC

        have hEq :
            diameter = carrier :=
          HilbertPlaneIncidence.line_unique
            Y C hYC
            diameter carrier
            hYdiam hCdiam
            hYcarrier hCcarrier

        have hBdiam :
            H.OnLine B diameter := by
          rw [hEq]
          exact hBcarrier

        exact hBoff hBdiam

      subst Y

      have hBCPbetween :
          Geo.Between B C P :=
        hBYP

      have hRayCXP :
          HilbertSameRay Geo C X P :=
        hilbert_sameRay_beyond_common_middle_stage22
          Geo
          B C X P
          hBCX
          hBCPbetween

      have hXcarrier :
          H.OnLine X carrier :=
        hilbert_collinear_on_line
          Geo
          B C X
          carrier
          hBC
          hBcarrier
          hCcarrier
          hBCXcol

      have hAoffCarrier :
          Not (H.OnLine A carrier) := by
        intro hAcarrier
        exact
          hABC
            ⟨carrier,
              hAcarrier,
              hBcarrier,
              hCcarrier⟩

      have hRayCXX :
          HilbertSameRay Geo C X X :=
        hilbert_sameRay_refl
          Geo C X hCX.symm

      have hXPSame :
          HilbertSameSide Geo X P diameter :=
        hilbert_sameRay_points_sameSide
          Geo
          C X
          X P
          A
          carrier diameter
          hCcarrier
          hXcarrier
          hCdiam
          hAdiam
          hAoffCarrier
          hRayCXX
          hRayCXP

      exact
        hilbert_sameSide_symm
          Geo X P diameter hXPSame

    · ----------------------------------------------------------------
      -- Noncollinear branch: extending B through C crosses the
      -- diameter, so X lies on the P-side.
      ----------------------------------------------------------------

      exact
        hilbert_sameSide_after_opposite_extension
          Geo
          B C P X
          diameter
          hCdiam
          hBCP
          hBCX
          hOppBP

  --------------------------------------------------------------------
  -- ACP < ACX.
  --
  -- I.16 gives ABC < ACX, and ABC and ACP are both right.
  --------------------------------------------------------------------

  have hABC_ACX :
      HilbertAngleLess Geo A B C A C X :=
    euclid_proposition_16_second
      Geo
      A B C X
      hABC
      hBCX

  have hACP_ABC :
      Geo.AngleCongruent
        A C P
        A B C :=
    hilbert_all_right_angles_congruent
      Geo
      A C P
      A B C
      hACP
      hABC
      hRightACP
      hRightABC

  have hACP_ACX :
      HilbertAngleLess Geo A C P A C X :=
    hilbert_angleLess_transport_left
      Geo
      A B C
      A C P
      A C X
      hABC_ACX
      hACP
      hACP_ABC

  have hInsideP_AX :
      HilbertRayMeetsSegment Geo C P A X :=
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      P X C A
      diameter
      hCdiam
      hAdiam
      hAC.symm
      hPXSame
      hACP_ACX

  --------------------------------------------------------------------
  -- ACD < ACP.
  --
  -- In the right triangle ADC, DCA is acute.  Reverse the first
  -- component and then transport the right angle ADC to ACP.
  --------------------------------------------------------------------

  have hDCA_ADC :
      HilbertAngleLess Geo D C A A D C :=
    i47_aux_angle_ACB_less_right_BAC
      Geo
      D A C
      hDAC
      hRightADC

  have hDCA :
      Not (PrimCollinear Geo D C A) := by
    intro h
    exact
      hACD
        (PrimCollinearSymm
          Geo D C A h)

  have hDCArefl :
      Geo.AngleCongruent
        D C A
        D C A :=
    Geometry.Geo.angle_congruent_reflexive
      Geo D C A

  have hACD_DCA :
      Geo.AngleCongruent
        A C D
        D C A :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      D C A
      D C A).mp
      hDCArefl

  have hACD_ADC :
      HilbertAngleLess Geo A C D A D C :=
    hilbert_angleLess_transport_left
      Geo
      D C A
      A C D
      A D C
      hDCA_ADC
      hACD
      hACD_DCA

  have hADC :
      Not (PrimCollinear Geo A D C) := by
    intro h
    exact
      hDAC
        (PrimCollinearSwap
          Geo A D C h)

  have hADC_ACP :
      Geo.AngleCongruent
        A D C
        A C P :=
    hilbert_all_right_angles_congruent
      Geo
      A D C
      A C P
      hADC
      hACP
      hRightADC
      hRightACP

  have hACD_ACP :
      HilbertAngleLess Geo A C D A C P :=
    hilbert_angleLess_transport_right
      Geo
      A C D
      A D C
      A C P
      hACD_ADC
      hACP
      hADC_ACP

  have hInsideD_AP :
      HilbertRayMeetsSegment Geo C D A P :=
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      D P C A
      diameter
      hCdiam
      hAdiam
      hAC.symm
      hDPSame
      hACD_ACP

  --------------------------------------------------------------------
  -- Nesting:
  --
  --   P inside A-X,
  --   D inside A-P
  --
  -- becomes, after reversing both crossed segments,
  --
  --   P inside X-A,
  --   D inside P-A.
  --
  -- The stage-26 parent-divider theorem then gives P inside X-D.
  --------------------------------------------------------------------

  have hInsideP_XA :
      HilbertRayMeetsSegment Geo C P X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      C P A X
      hInsideP_AX

  have hInsideD_PA :
      HilbertRayMeetsSegment Geo C D P A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      C D A P
      hInsideD_AP

  have hXCA :
      Not (PrimCollinear Geo X C A) := by
    intro h
    exact
      hACP_ACX.2.1
        (PrimCollinearSymm
          Geo X C A h)

  have hInsideP_XD :
      HilbertRayMeetsSegment Geo C P X D :=
    hilbert_angleDecomposition_nested_parent_divider_stage26
      Geo
      X C A P D
      hXCA
      hInsideP_XA
      hInsideD_PA

  exact
    ⟨X,
      P,
      hBCX,
      hPDSame,
      hRightACP,
      hInsideP_AX,
      hInsideD_AP,
      hInsideP_XD⟩
/- END folded proof support: Crossing_circle_stage40_IV14_perpendicular_inside_supplement_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage41_IV14_first_component_v3.lean -/
/-!
# Forder IV.14 -- stage 41, first component

Stage 40 constructs X and P with

  B-C-X

and CP interior to the supplementary angle XCD.  It also records that
CP is interior to ACX and that ACP is right.

Apply I.32 to triangle ABC with BC produced through C to X.  This gives
an interior ray CQ of ACX such that

  BAC ~= ACQ,
  ABC ~= QCX.

Since ABC and ACP are right, the complementary components QCX and ACP
are congruent (after reversing QCX to XCQ).

Now compare the two decompositions

  ACX = ACQ + QCX,
  XCA = XCP + PCA.

The whole angles ACX and XCA are the same unoriented angle.  Subtracting
the congruent right components gives

  ACQ ~= XCP,

and hence

  BAC ~= XCP.

No numerical angle measure is used.
-/

/--
First component needed in Forder IV.14:

after the stage-40 construction, the acute angle BAC is congruent to
the first component XCP of the supplementary angle XCD.
-/
theorem hilbert_forder_IV14_first_component_stage41
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists X P : Geo.Point,
      Geo.Between B C X /\
      HilbertSameSide Geo P D diameter /\
      HilbertRightAngle Geo A C P /\
      HilbertRayMeetsSegment Geo C P A X /\
      HilbertRayMeetsSegment Geo C D A P /\
      HilbertRayMeetsSegment Geo C P X D /\
      Geo.AngleCongruent B A C X C P := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy at B.
  --------------------------------------------------------------------

  have hBoff :
      Not (H.OnLine B diameter) :=
    hOppBD.1

  have hABC :
      Not (PrimCollinear Geo A B C) := by
    intro h

    have hACB :
        PrimCollinear Geo A C B :=
      PrimCollinearRotate
        Geo A B C h

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        A C B
        diameter
        hAC
        hAdiam
        hCdiam
        hACB

    exact hBoff hBdiam

  --------------------------------------------------------------------
  -- The diameter angle ABC is right.
  --------------------------------------------------------------------

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R A C B
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle
      hBcircle
      hBoff

  --------------------------------------------------------------------
  -- Stage 40.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV14_perpendicular_inside_supplement_stage40
        Geo
        K R A B C D
        diameter
        hAC
        hAdiam
        hCdiam
        hKdiam
        hAcircle
        hBcircle
        hCcircle
        hDcircle
        hOppBD
    with
    ⟨X,
      P,
      hBCX,
      hPDSame,
      hRightACP,
      hInsideP_AX,
      hInsideD_AP,
      hInsideP_XD⟩

  --------------------------------------------------------------------
  -- ACP is a proper right angle.
  --------------------------------------------------------------------

  have hPoff :
      Not (H.OnLine P diameter) :=
    hPDSame.1

  have hACP :
      Not (PrimCollinear Geo A C P) :=
    hilbert_not_collinear_of_off_line
      Geo
      A C P
      diameter
      hAC
      hAdiam
      hCdiam
      hPoff

  --------------------------------------------------------------------
  -- I.32 for triangle ABC with B-C-X.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A B C X
        hABC
        hBCX
    with
    ⟨Q,
      hAQX,
      hBAC_ACQ,
      hABC_QCX⟩

  --------------------------------------------------------------------
  -- Q is different from C.
  --------------------------------------------------------------------

  have hCX :
      Ne C X :=
    (HilbertOrder.between_incidence
      B C X hBCX).2.1

  have hCQ :
      Ne C Q := by
    intro hCQ
    subst Q

    have hACXcol :
        PrimCollinear Geo A C X :=
      (HilbertOrder.between_incidence
        A C X hAQX).2.2.2.1

    have hBCXcol :
        PrimCollinear Geo B C X :=
      (HilbertOrder.between_incidence
        B C X hBCX).2.2.2.1

    rcases
        HilbertPlaneIncidence.line_through
          C X hCX
      with
      ⟨lineCX,
        hCline,
        hXline⟩

    have hAline :
        H.OnLine A lineCX :=
      hilbert_collinear_on_line
        Geo
        C X A
        lineCX
        hCX
        hCline
        hXline
        (PrimCollinearCycle
          Geo A C X hACXcol)

    have hBline :
        H.OnLine B lineCX :=
      hilbert_collinear_on_line
        Geo
        C X B
        lineCX
        hCX
        hCline
        hXline
        (PrimCollinearCycle
          Geo B C X hBCXcol)

    exact
      hABC
        ⟨lineCX,
          hAline,
          hBline,
          hCline⟩

  --------------------------------------------------------------------
  -- Hence CQ is genuinely an interior ray of ACX.
  --------------------------------------------------------------------

  have hInsideQ_AX :
      HilbertRayMeetsSegment Geo C Q A X :=
    ⟨Q,
      hAQX,
      hilbert_sameRay_refl
        Geo C Q hCQ.symm⟩

  --------------------------------------------------------------------
  -- Reverse the stage-40 decomposition.
  --------------------------------------------------------------------

  have hInsideP_XA :
      HilbertRayMeetsSegment Geo C P X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      C P A X
      hInsideP_AX

  --------------------------------------------------------------------
  -- The two right components are congruent.
  --------------------------------------------------------------------

  have hABC_ACP :
      Geo.AngleCongruent
        A B C
        A C P :=
    hilbert_all_right_angles_congruent
      Geo
      A B C
      A C P
      hABC
      hACP
      hRightABC
      hRightACP

  have hQCX_ABC :
      Geo.AngleCongruent
        Q C X
        A B C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B C
      Q C X
      hABC_QCX

  have hXCQ_ABC :
      Geo.AngleCongruent
        X C Q
        A B C :=
    (Geo.angle_congruent_reverse_first
      Q C X
      A B C).mp
      hQCX_ABC

  have hXCQ_ACP :
      Geo.AngleCongruent
        X C Q
        A C P :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X C Q
      A B C
      A C P
      hXCQ_ABC
      hABC_ACP

  --------------------------------------------------------------------
  -- ACX and XCA are the same angle with both rays exchanged.
  --------------------------------------------------------------------

  have hACXrefl :
      Geo.AngleCongruent
        A C X
        A C X :=
    Geometry.Geo.angle_congruent_reflexive
      Geo A C X

  have hACX_XCA :
      Geo.AngleCongruent
        A C X
        X C A :=
    (Geo.angle_congruent_reverse_second
      A C X
      A C X).mp
      hACXrefl

  --------------------------------------------------------------------
  -- Noncollinearity of the two whole angles.
  --
  -- These are intentionally exposed explicitly for the subtraction API.
  --------------------------------------------------------------------

  have hACX :
      Not (PrimCollinear Geo A C X) := by
    intro h
    have hACBcol :
        PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo
        A C X B
        hCX
        h
        (PrimCollinearCycle
          Geo B C X
          (HilbertOrder.between_incidence
            B C X hBCX).2.2.2.1)
    exact hABC
      (PrimCollinearRotate
        Geo A C B hACBcol)

  have hXCA :
      Not (PrimCollinear Geo X C A) := by
    intro h
    exact
      hACX
        (PrimCollinearSymm
          Geo X C A h)

  --------------------------------------------------------------------
  -- Subtract the equal right components.
  --------------------------------------------------------------------

  have hACQ_XCP :
      Geo.AngleCongruent
        A C Q
        X C P :=
    hilbert_angleDecomposition_angle_subtraction
      Geo
      C A X Q
      X C A P
      hACX
      hXCA
      hInsideQ_AX
      hInsideP_XA
      hACX_XCA
      hXCQ_ACP

  --------------------------------------------------------------------
  -- I.32 already gave BAC ~= ACQ.
  --------------------------------------------------------------------

  have hBAC_XCP :
      Geo.AngleCongruent
        B A C
        X C P :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A C
      A C Q
      X C P
      hBAC_ACQ
      hACQ_XCP

  exact
    ⟨X,
      P,
      hBCX,
      hPDSame,
      hRightACP,
      hInsideP_AX,
      hInsideD_AP,
      hInsideP_XD,
      hBAC_XCP⟩
/- END folded proof support: Crossing_circle_stage41_IV14_first_component_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage42_IV14_second_component_v1.lean -/
/-!
# Forder IV.14 -- stage 42, second component

Stage 41 gives the first component

  angle BAC ~= angle XCP.

This stage proves the second component

  angle CAD ~= angle PCD.

The argument is again purely synthetic.

* angle ADC is right, because AC is a diameter;
* extend CD through D to E;
* the adjacent angle ADE is therefore right;
* I.32 for triangle ACD decomposes ADE into copies of CAD and ACD;
* stage 40 gives D as an interior ray of the right angle ACP;
* reverse that decomposition to the right angle PCA;
* subtract the common component ACD from the two right angles.

No numerical angle measure is used.
-/

/--
The two component congruences needed for Forder IV.14.

For the stage-40 points X and P,

  BAC ~= XCP,
  CAD ~= PCD.
-/
theorem hilbert_forder_IV14_second_component_stage42
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists X P : Geo.Point,
      Geo.Between B C X /\
      HilbertSameSide Geo P D diameter /\
      HilbertRightAngle Geo A C P /\
      HilbertRayMeetsSegment Geo C P A X /\
      HilbertRayMeetsSegment Geo C D A P /\
      HilbertRayMeetsSegment Geo C P X D /\
      Geo.AngleCongruent B A C X C P /\
      Geo.AngleCongruent C A D P C D := by

  --------------------------------------------------------------------
  -- Stage 41.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV14_first_component_stage41
        Geo
        K R A B C D
        diameter
        hAC
        hAdiam
        hCdiam
        hKdiam
        hAcircle
        hBcircle
        hCcircle
        hDcircle
        hOppBD
    with
    ⟨X,
      P,
      hBCX,
      hPDSame,
      hRightACP,
      hInsideP_AX,
      hInsideD_AP,
      hInsideP_XD,
      hBAC_XCP⟩

  --------------------------------------------------------------------
  -- Proper triangle ACD.
  --------------------------------------------------------------------

  have hDoff :
      Not (H.OnLine D diameter) :=
    hOppBD.2.1

  have hACD :
      Not (PrimCollinear Geo A C D) :=
    hilbert_not_collinear_of_off_line
      Geo
      A C D
      diameter
      hAC
      hAdiam
      hCdiam
      hDoff

  have hADC :
      Not (PrimCollinear Geo A D C) := by
    intro h
    exact
      hACD
        (PrimCollinearRotate
          Geo A D C h)

  --------------------------------------------------------------------
  -- ADC is right because AC is a diameter.
  --------------------------------------------------------------------

  have hRightADC :
      HilbertRightAngle Geo A D C :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R A C D
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle
      hDcircle
      hDoff

  --------------------------------------------------------------------
  -- ACP is a proper right angle.
  --------------------------------------------------------------------

  have hPoff :
      Not (H.OnLine P diameter) :=
    hPDSame.1

  have hACP :
      Not (PrimCollinear Geo A C P) :=
    hilbert_not_collinear_of_off_line
      Geo
      A C P
      diameter
      hAC
      hAdiam
      hCdiam
      hPoff

  have hPCA :
      Not (PrimCollinear Geo P C A) := by
    intro h
    exact
      hACP
        (PrimCollinearSymm
          Geo P C A h)

  --------------------------------------------------------------------
  -- Extend CD through D to E.
  --------------------------------------------------------------------

  have hCD :
      Ne C D := by
    intro h
    subst D
    exact hDoff hCdiam

  rcases
      HilbertOrder.between_extension
        C D hCD
    with
    ⟨E, hCDE⟩

  have hCDEdata :=
    HilbertOrder.between_incidence
      C D E hCDE

  have hDE :
      Ne D E :=
    hCDEdata.2.1

  have hCDEcol :
      PrimCollinear Geo C D E :=
    hCDEdata.2.2.2.1

  --------------------------------------------------------------------
  -- The adjacent angle ADE is right.
  --------------------------------------------------------------------

  have hRightADE :
      HilbertRightAngle Geo A D E :=
    proposition2_13_right_angle_other_side
      Geo
      A C E D
      hCDE
      hADC
      hRightADC

  have hADE :
      Not (PrimCollinear Geo A D E) := by
    intro hADEcol

    have hDEC :
        PrimCollinear Geo D E C :=
      PrimCollinearCycle
        Geo C D E hCDEcol

    have hADCcol :
        PrimCollinear Geo A D C :=
      hilbert_primCollinear_trans
        Geo
        A D E C
        hDE
        hADEcol
        hDEC

    exact hADC hADCcol

  --------------------------------------------------------------------
  -- I.32 for triangle ACD with C-D-E.
  --
  -- It gives Q on A-E with
  --
  --   CAD ~= ADQ,
  --   ACD ~= QDE.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A C D E
        hACD
        hCDE
    with
    ⟨Q,
      hAQE,
      hCAD_ADQ,
      hACD_QDE⟩

  --------------------------------------------------------------------
  -- Q is different from D, hence DQ is a genuine interior ray of ADE.
  --------------------------------------------------------------------

  have hQD :
      Ne Q D := by
    intro hQD
    subst Q

    have hADEcol :
        PrimCollinear Geo A D E :=
      (HilbertOrder.between_incidence
        A D E hAQE).2.2.2.1

    have hDEC :
        PrimCollinear Geo D E C :=
      PrimCollinearCycle
        Geo C D E hCDEcol

    have hADCcol :
        PrimCollinear Geo A D C :=
      hilbert_primCollinear_trans
        Geo
        A D E C
        hDE
        hADEcol
        hDEC

    exact hADC hADCcol

  have hInsideQ_AE :
      HilbertRayMeetsSegment Geo D Q A E :=
    ⟨Q,
      hAQE,
      hilbert_sameRay_refl
        Geo D Q hQD⟩

  --------------------------------------------------------------------
  -- Reverse the stage-40 decomposition:
  --
  --   D inside A-C-P
  --
  -- becomes
  --
  --   D inside P-C-A.
  --------------------------------------------------------------------

  have hInsideD_PA :
      HilbertRayMeetsSegment Geo C D P A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      C D A P
      hInsideD_AP

  --------------------------------------------------------------------
  -- The two whole angles ADE and PCA are right, hence congruent.
  --------------------------------------------------------------------

  have hADE_ACP :
      Geo.AngleCongruent
        A D E
        A C P :=
    hilbert_all_right_angles_congruent
      Geo
      A D E
      A C P
      hADE
      hACP
      hRightADE
      hRightACP

  have hADE_PCA :
      Geo.AngleCongruent
        A D E
        P C A :=
    (Geo.angle_congruent_reverse_second
      A D E
      A C P).mp
      hADE_ACP

  --------------------------------------------------------------------
  -- I.32 gives ACD ~= QDE.
  -- Normalize it to the right components
  --
  --   EDQ ~= ACD.
  --------------------------------------------------------------------

  have hACD_EDQ :
      Geo.AngleCongruent
        A C D
        E D Q :=
    (Geo.angle_congruent_reverse_second
      A C D
      Q D E).mp
      hACD_QDE

  have hEDQ_ACD :
      Geo.AngleCongruent
        E D Q
        A C D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A C D
      E D Q
      hACD_EDQ

  --------------------------------------------------------------------
  -- Subtract the equal right components:
  --
  --   ADE = ADQ + EDQ,
  --   PCA = PCD + ACD.
  --
  -- Hence ADQ ~= PCD.
  --------------------------------------------------------------------

  have hADQ_PCD :
      Geo.AngleCongruent
        A D Q
        P C D :=
    hilbert_angleDecomposition_angle_subtraction
      Geo
      D A E Q
      P C A D
      hADE
      hPCA
      hInsideQ_AE
      hInsideD_PA
      hADE_PCA
      hEDQ_ACD

  --------------------------------------------------------------------
  -- I.32 already gave CAD ~= ADQ.
  --------------------------------------------------------------------

  have hCAD_PCD :
      Geo.AngleCongruent
        C A D
        P C D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C A D
      A D Q
      P C D
      hCAD_ADQ
      hADQ_PCD

  exact
    ⟨X,
      P,
      hBCX,
      hPDSame,
      hRightACP,
      hInsideP_AX,
      hInsideD_AP,
      hInsideP_XD,
      hBAC_XCP,
      hCAD_PCD⟩
/- END folded proof support: Crossing_circle_stage42_IV14_second_component_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage43_IV14_complete_v1.lean -/
/-!
# Forder IV.14 -- stage 43, complete supplement

For circle points A,B,C,D with AC a diameter and B,D on opposite
sides of AC, stage 42 supplies X and P with

  B-C-X,

and the two component congruences

  BAC ~= XCP,
  CAD ~= PCD.

Stage 38 supplies that AC is an interior ray of angle BAD, while
stage 42 supplies that CP is an interior ray of angle XCD.

Hilbert angle addition therefore gives

  BAD ~= XCD.

Together with B-C-X this is exactly the synthetic supplement statement
for the opposite angles BAD and BCD.

No numerical angle measure is used.
-/

/--
Forder IV.14 in Book Zero supplement form.

If A,B,C,D lie on a circle with diameter AC and B,D on opposite sides
of the diameter carrier, then angle BAD and angle BCD are supplementary.
-/
theorem hilbert_forder_IV14_diameter_supplement_stage43
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists X : Geo.Point,
      BookZeroSupplement Geo B C D D X /\
      Geo.AngleCongruent B A D X C D := by

  --------------------------------------------------------------------
  -- Stage 42: both component congruences and the target interior ray.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV14_second_component_stage42
        Geo
        K R A B C D
        diameter
        hAC
        hAdiam
        hCdiam
        hKdiam
        hAcircle
        hBcircle
        hCcircle
        hDcircle
        hOppBD
    with
    ⟨X,
      P,
      hBCX,
      hPDSame,
      hRightACP,
      hInsideP_AX,
      hInsideD_AP,
      hInsideP_XD,
      hBAC_XCP,
      hCAD_PCD⟩

  --------------------------------------------------------------------
  -- Stage 38: AC is interior to BAD.
  --------------------------------------------------------------------

  have hInsideAC :
      HilbertRayMeetsSegment Geo A C B D :=
    (hilbert_forder_IV14_diameter_rays_inside_stage38
      Geo
      K R A B C D
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hBcircle
      hCcircle
      hDcircle
      hOppBD).1

  --------------------------------------------------------------------
  -- Basic properness around the diameter.
  --------------------------------------------------------------------

  have hBoff :
      Not (H.OnLine B diameter) :=
    hOppBD.1

  have hDoff :
      Not (H.OnLine D diameter) :=
    hOppBD.2.1

  have hABC :
      Not (PrimCollinear Geo A B C) := by
    intro h

    have hACB :
        PrimCollinear Geo A C B :=
      PrimCollinearRotate
        Geo A B C h

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        A C B
        diameter
        hAC
        hAdiam
        hCdiam
        hACB

    exact hBoff hBdiam

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  --------------------------------------------------------------------
  -- BAD is proper.
  --
  -- If B,A,D were collinear, the stage-38 intersection point Y of BD
  -- with the ray AC would put B,A,C on one line, contradicting hBAC.
  --------------------------------------------------------------------

  have hBAD :
      Not (PrimCollinear Geo B A D) := by
    intro hBADcol

    rcases hInsideAC with
      ⟨Y, hBYD, hRayACY⟩

    have hBYDdata :=
      HilbertOrder.between_incidence
        B Y D hBYD

    have hBD :
        Ne B D :=
      hBYDdata.2.2.1

    rcases
        HilbertPlaneIncidence.line_through
          B D hBD
      with
      ⟨lineBD,
        hBline,
        hDline⟩

    have hAline :
        H.OnLine A lineBD :=
      hilbert_collinear_on_line
        Geo
        B D A
        lineBD
        hBD
        hBline
        hDline
        (PrimCollinearRotate
          Geo B A D hBADcol)

    have hYline :
        H.OnLine Y lineBD :=
      hilbert_between_on_line
        Geo
        B Y D
        lineBD
        hBline
        hDline
        hBYD

    have hAY :
        Ne A Y :=
      hRayACY.2.1.symm

    have hAYC :
        PrimCollinear Geo A Y C :=
      PrimCollinearRotate
        Geo A C Y
        hRayACY.2.2.1

    have hCline :
        H.OnLine C lineBD :=
      hilbert_collinear_on_line
        Geo
        A Y C
        lineBD
        hAY
        hAline
        hYline
        hAYC

    exact
      hBAC
        ⟨lineBD,
          hBline,
          hAline,
          hCline⟩

  --------------------------------------------------------------------
  -- X is off the diameter, hence XCA is proper.
  --------------------------------------------------------------------

  have hBCXdata :=
    HilbertOrder.between_incidence
      B C X hBCX

  have hCX :
      Ne C X :=
    hBCXdata.2.1

  have hBCXcol :
      PrimCollinear Geo B C X :=
    hBCXdata.2.2.2.1

  have hXoff :
      Not (H.OnLine X diameter) := by
    intro hXdiam

    have hCXB :
        PrimCollinear Geo C X B :=
      PrimCollinearCycle
        Geo B C X hBCXcol

    have hBdiam :
        H.OnLine B diameter :=
      hilbert_collinear_on_line
        Geo
        C X B
        diameter
        hCX
        hCdiam
        hXdiam
        hCXB

    exact hBoff hBdiam

  have hCAX :
      Not (PrimCollinear Geo C A X) :=
    hilbert_not_collinear_of_off_line
      Geo
      C A X
      diameter
      hAC.symm
      hCdiam
      hAdiam
      hXoff

  have hXCA :
      Not (PrimCollinear Geo X C A) := by
    intro h
    exact
      hCAX
        (PrimCollinearCycle
          Geo X C A h)

  --------------------------------------------------------------------
  -- Since CP is interior to XCA, the component XCP is proper.
  --------------------------------------------------------------------

  have hInsideP_XA :
      HilbertRayMeetsSegment Geo C P X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      C P A X
      hInsideP_AX

  have hXCP :
      Not (PrimCollinear Geo X C P) :=
    (hilbert_interior_angle_less
      Geo
      C P X A
      hXCA
      hInsideP_XA).1

  --------------------------------------------------------------------
  -- XCD is proper.
  --
  -- If X,C,D were collinear, the intersection point of ray CP with
  -- segment XD would force P onto the same carrier, contradicting hXCP.
  --------------------------------------------------------------------

  have hXCD :
      Not (PrimCollinear Geo X C D) := by
    intro hXCDcol

    rcases hInsideP_XD with
      ⟨Y, hXYD, hRayCPY⟩

    have hXYDdata :=
      HilbertOrder.between_incidence
        X Y D hXYD

    have hXD :
        Ne X D :=
      hXYDdata.2.2.1

    rcases
        HilbertPlaneIncidence.line_through
          X D hXD
      with
      ⟨lineXD,
        hXline,
        hDline⟩

    have hCline :
        H.OnLine C lineXD :=
      hilbert_collinear_on_line
        Geo
        X D C
        lineXD
        hXD
        hXline
        hDline
        (PrimCollinearRotate
          Geo X C D hXCDcol)

    have hYline :
        H.OnLine Y lineXD :=
      hilbert_between_on_line
        Geo
        X Y D
        lineXD
        hXline
        hDline
        hXYD

    have hCY :
        Ne C Y :=
      hRayCPY.2.1.symm

    have hCYP :
        PrimCollinear Geo C Y P :=
      PrimCollinearRotate
        Geo C P Y
        hRayCPY.2.2.1

    have hPline :
        H.OnLine P lineXD :=
      hilbert_collinear_on_line
        Geo
        C Y P
        lineXD
        hCY
        hCline
        hYline
        hCYP

    exact
      hXCP
        ⟨lineXD,
          hXline,
          hCline,
          hPline⟩

  --------------------------------------------------------------------
  -- Add the corresponding interior components.
  --
  -- Source:
  --   BAD = BAC + CAD
  --
  -- Target:
  --   XCD = XCP + PCD
  --------------------------------------------------------------------

  have hBAD_XCD :
      Geo.AngleCongruent
        B A D
        X C D :=
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      A B D C
      C X D P
      hBAD
      hXCD
      hInsideAC
      hInsideP_XD
      hBAC_XCP
      hCAD_PCD

  --------------------------------------------------------------------
  -- B-C-X is exactly the Book Zero supplement configuration.
  --------------------------------------------------------------------

  have hCD :
      Ne C D := by
    intro h
    subst D
    exact hDoff hCdiam

  have hSupp :
      BookZeroSupplement Geo
        B C D
        D X := by
    constructor

    · exact
        hilbert_sameRay_refl
          Geo C D hCD.symm

    · exact hBCX

  exact
    ⟨X,
      hSupp,
      hBAD_XCD⟩
/- END folded proof support: Crossing_circle_stage43_IV14_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage44_IV15_center_on_diagonal_v1.lean -/
/-!
# Forder IV.15 -- stage 44, center on the diagonal

This is the easy branch in Forder's proof of IV.15.

Let A,B,C,D lie on one circle, and let BD be the diagonal separating
A and C. If the center K lies on BD, then BD is a diameter. Hence

  angle BAD

and

  angle BCD

are both right by Forder IV.13.

Extend BC through C to X. The adjacent angle XCD is also right, so

  angle BAD ~= angle XCD.

Together with B-C-X this is exactly the Book Zero supplement form of
the desired conclusion.

No numerical angle measure is used.
-/

/--
Forder IV.15, center-on-diagonal branch.

If the center lies on the separating diagonal BD, the opposite angles
BAD and BCD are supplementary.
-/
theorem hilbert_forder_IV15_center_on_diagonal_stage44
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diagonal : Geo.Line)
    (hBD : Ne B D)
    (hBdiag : H.OnLine B diagonal)
    (hDdiag : H.OnLine D diagonal)
    (hKdiag : H.OnLine K diagonal)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppAC : HilbertOppositeSide Geo A C diagonal) :
    exists X : Geo.Point,
      BookZeroSupplement Geo B C D D X /\
      Geo.AngleCongruent B A D X C D := by

  --------------------------------------------------------------------
  -- A and C are off the diameter BD.
  --------------------------------------------------------------------

  have hAoff :
      Not (H.OnLine A diagonal) :=
    hOppAC.1

  have hCoff :
      Not (H.OnLine C diagonal) :=
    hOppAC.2.1

  --------------------------------------------------------------------
  -- Properness of the two inscribed angles.
  --------------------------------------------------------------------

  have hBDA :
      Not (PrimCollinear Geo B D A) :=
    hilbert_not_collinear_of_off_line
      Geo
      B D A
      diagonal
      hBD
      hBdiag
      hDdiag
      hAoff

  have hBAD :
      Not (PrimCollinear Geo B A D) := by
    intro h
    exact
      hBDA
        (PrimCollinearRotate
          Geo B A D h)

  have hBDC :
      Not (PrimCollinear Geo B D C) :=
    hilbert_not_collinear_of_off_line
      Geo
      B D C
      diagonal
      hBD
      hBdiag
      hDdiag
      hCoff

  have hBCD :
      Not (PrimCollinear Geo B C D) := by
    intro h
    exact
      hBDC
        (PrimCollinearRotate
          Geo B C D h)

  --------------------------------------------------------------------
  -- Forder IV.13: both angles subtending the diameter BD are right.
  --------------------------------------------------------------------

  have hRightBAD :
      HilbertRightAngle Geo B A D :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R B D A
      diagonal
      hBD
      hBdiag
      hDdiag
      hKdiag
      hBcircle
      hDcircle
      hAcircle
      hAoff

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    hilbert_forder_IV13_diameter_right_angle_stage17
      Geo
      K R B D C
      diagonal
      hBD
      hBdiag
      hDdiag
      hKdiag
      hBcircle
      hDcircle
      hCcircle
      hCoff

  --------------------------------------------------------------------
  -- Extend BC through C to X.
  --------------------------------------------------------------------

  have hBC :
      Ne B C := by
    intro h
    subst B
    exact hCoff hBdiag

  rcases
      HilbertOrder.between_extension
        B C hBC
    with
    ⟨X, hBCX⟩

  have hBCXdata :=
    HilbertOrder.between_incidence
      B C X hBCX

  have hCX :
      Ne C X :=
    hBCXdata.2.1

  have hBCXcol :
      PrimCollinear Geo B C X :=
    hBCXdata.2.2.2.1

  --------------------------------------------------------------------
  -- Reverse BCD to DCB, then transport the right angle across the
  -- straight carrier B-C-X.
  --------------------------------------------------------------------

  have hDCB :
      Not (PrimCollinear Geo D C B) := by
    intro h
    exact
      hBCD
        (PrimCollinearSymm
          Geo D C B h)

  have hRightDCB :
      HilbertRightAngle Geo D C B :=
    proposition2_12_right_angle_swap
      Geo
      B C D
      hBCD
      hRightBCD

  have hRightDCX :
      HilbertRightAngle Geo D C X :=
    proposition2_13_right_angle_other_side
      Geo
      D B X C
      hBCX
      hDCB
      hRightDCB

  --------------------------------------------------------------------
  -- The new angle XCD is proper.
  --------------------------------------------------------------------

  have hDCX :
      Not (PrimCollinear Geo D C X) := by
    intro hDCXcol

    have hCXD :
        PrimCollinear Geo C X D :=
      PrimCollinearCycle
        Geo D C X hDCXcol

    have hBCDcol :
        PrimCollinear Geo B C D :=
      hilbert_primCollinear_trans
        Geo
        B C X D
        hCX
        hBCXcol
        hCXD

    exact hBCD hBCDcol

  have hXCD :
      Not (PrimCollinear Geo X C D) := by
    intro h
    exact
      hDCX
        (PrimCollinearSymm
          Geo X C D h)

  have hRightXCD :
      HilbertRightAngle Geo X C D :=
    proposition2_12_right_angle_swap
      Geo
      D C X
      hDCX
      hRightDCX

  --------------------------------------------------------------------
  -- All right angles are congruent.
  --------------------------------------------------------------------

  have hBAD_XCD :
      Geo.AngleCongruent
        B A D
        X C D :=
    hilbert_all_right_angles_congruent
      Geo
      B A D
      X C D
      hBAD
      hXCD
      hRightBAD
      hRightXCD

  --------------------------------------------------------------------
  -- B-C-X gives the Book Zero supplement configuration.
  --------------------------------------------------------------------

  have hCD :
      Ne C D := by
    intro h
    subst D
    exact hCoff hDdiag

  have hSupp :
      BookZeroSupplement Geo
        B C D
        D X := by
    constructor

    · exact
        hilbert_sameRay_refl
          Geo C D hCD.symm

    · exact hBCX

  exact
    ⟨X,
      hSupp,
      hBAD_XCD⟩
/- END folded proof support: Crossing_circle_stage44_IV15_center_on_diagonal_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage45_IV15_antipode_side_v1.lean -/
/-!
# Forder IV.15 -- stage 45, antipode side transport

This file isolates one plane-separation fact used in the non-diameter
branch of Forder IV.15.

Assume:

* A and C are on opposite sides of a line d;
* C and K are on the same side of d;
* A-K-E.

Then A and E are on opposite sides of d.

Indeed, transporting the opposite-side relation from C to K gives
A opposite K.  The crossing point of AK with d remains between A and E
because K lies between A and E.

This is exactly the side-theoretic step needed after constructing the
antipode E of A.
-/

/--
If A,C are opposite sides of `d`, C,K are same side of `d`, and A-K-E,
then A,E are opposite sides of `d`.
-/
theorem hilbert_IV15_antipode_opposite_diagonal_stage45
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (A C K E : Geo.Point)
    (d : Geo.Line)
    (hOppAC : HilbertOppositeSide Geo A C d)
    (hSameCK : HilbertSameSide Geo C K d)
    (hAKE : Geo.Between A K E) :
    HilbertOppositeSide Geo A E d := by

  --------------------------------------------------------------------
  -- Transport A opposite C across the same-side relation C ~ K.
  --------------------------------------------------------------------

  have hOppAK :
      HilbertOppositeSide Geo A K d :=
    hilbert_oppositeSide_transport_right
      Geo
      A C K
      d
      hOppAC
      hSameCK

  have hAoff :
      Not (H.OnLine A d) :=
    hOppAK.1

  --------------------------------------------------------------------
  -- Let Y be the crossing point of AK with d.
  --------------------------------------------------------------------

  rcases hOppAK.2.2 with
    ⟨Y, hAYK, hYd⟩

  --------------------------------------------------------------------
  -- Since A-Y-K and A-K-E, also A-Y-E.
  --------------------------------------------------------------------

  have hAYE :
      Geo.Between A Y E :=
    (hilbert_between_inner_trans
      Geo
      A Y K E
      hAYK
      hAKE).2

  --------------------------------------------------------------------
  -- E cannot lie on d.  Otherwise the carrier AYE would coincide
  -- with d through the two distinct points Y,E, forcing A onto d.
  --------------------------------------------------------------------

  have hEoff :
      Not (H.OnLine E d) := by
    intro hEd

    have hAYEdata :=
      HilbertOrder.between_incidence
        A Y E hAYE

    have hYE :
        Ne Y E :=
      hAYEdata.2.1

    rcases hAYEdata.2.2.2.1 with
      ⟨lineAYE,
        hAline,
        hYline,
        hEline⟩

    have hEq :
        lineAYE = d :=
      HilbertPlaneIncidence.line_unique
        Y E hYE
        lineAYE d
        hYline
        hEline
        hYd
        hEd

    exact
      hAoff
        (hEq ▸ hAline)

  --------------------------------------------------------------------
  -- Y is now the required crossing witness for A and E.
  --------------------------------------------------------------------

  exact
    ⟨hAoff,
      hEoff,
      ⟨Y,
        hAYE,
        hYd⟩⟩
/- END folded proof support: Crossing_circle_stage45_IV15_antipode_side_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage46_IV15_diameter_inner_point_v2.lean -/
/-!
# Forder IV.15 -- stage 46, interior point of a diameter

This is a purely one-dimensional order/congruence lemma.

Assume

  A-K-E,

with KA congruent KE, so K is the midpoint of AE. Let Y be any other
point with

  A-Y-E.

Then either Y=K, or

  KY < KA.

This is the synthetic statement that every proper interior point of a
diameter lies strictly inside the circle, except for the center itself
where the radial segment is null.

No circle theorem is used.
-/

/--
If K is the midpoint of AE and Y lies strictly between A and E, then
either Y=K or KY is strictly shorter than the radius KA.
-/
theorem hilbert_IV15_diameter_inner_point_stage46
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A K E Y : Geo.Point)
    (hAKE : Geo.Between A K E)
    (hAYE : Geo.Between A Y E)
    (hKA_KE : Geo.Congruent K A K E) :
    Y = K \/
    HilbertSegmentLess Geo K Y K A := by

  by_cases hYK : Y = K

  · exact Or.inl hYK

  right

  --------------------------------------------------------------------
  -- Basic distinctness.
  --------------------------------------------------------------------

  have hAKEdata :=
    HilbertOrder.between_incidence
      A K E hAKE

  have hAYEdata :=
    HilbertOrder.between_incidence
      A Y E hAYE

  have hAK :
      Ne A K :=
    hAKEdata.1

  have hKE :
      Ne K E :=
    hAKEdata.2.1

  have hAE :
      Ne A E :=
    hAKEdata.2.2.1

  have hAY :
      Ne A Y :=
    hAYEdata.1

  have hKY :
      Ne K Y :=
    Ne.symm hYK

  --------------------------------------------------------------------
  -- A,K,Y are collinear because both K and Y lie on AE.
  --------------------------------------------------------------------

  have hAKEcol :
      PrimCollinear Geo A K E :=
    hAKEdata.2.2.2.1

  have hAYEcol :
      PrimCollinear Geo A Y E :=
    hAYEdata.2.2.2.1

  have hKAE :
      PrimCollinear Geo K A E :=
    PrimCollinearSwap
      Geo A K E hAKEcol

  have hAEY :
      PrimCollinear Geo A E Y :=
    PrimCollinearRotate
      Geo A Y E hAYEcol

  have hKAY :
      PrimCollinear Geo K A Y :=
    hilbert_primCollinear_trans
      Geo
      K A E Y
      hAE
      hKAE
      hAEY

  have hAKY :
      PrimCollinear Geo A K Y :=
    PrimCollinearSwap
      Geo K A Y hKAY

  --------------------------------------------------------------------
  -- Trichotomy for A,K,Y.
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        A K Y
        hAK
        hKY
        hAY
        hAKY
    with
    hAKY_between | hKAY_between | hAYK_between

  --------------------------------------------------------------------
  -- Case A-K-Y. Since also A-Y-E, we have K-Y-E, so
  --
  --   KY < KE ~= KA.
  --------------------------------------------------------------------

  · have hKYE :
        Geo.Between K Y E :=
      (hilbert_between_inner_trans
        Geo
        A K Y E
        hAKY_between
        hAYE).1

    have hKY_KE :
        HilbertSegmentLess Geo K Y K E :=
      hilbert_segmentLess_of_between
        Geo
        K Y E
        hKYE

    have hKE_KA :
        Geo.Congruent K E K A :=
      hilbert_congruent_symmetry
        Geo
        K A
        K E
        hKA_KE

    exact
      hilbert_segmentLess_congruent_right
        Geo
        K Y
        K E
        K A
        hKY_KE
        hKE_KA

  --------------------------------------------------------------------
  -- Case K-A-Y is impossible: together with A-Y-E it gives K-A-E,
  -- contradicting A-K-E.
  --------------------------------------------------------------------

  · have hKAE_between :
        Geo.Between K A E :=
      (hilbert_between_outer_trans
        Geo
        K A Y E
        hKAY_between
        hAYE).2

    have hUnique :=
      HilbertOrder.between_unique
        A K E
        hAKEcol
        hAKE

    exact
      False.elim
        (hUnique.1 hKAE_between)

  --------------------------------------------------------------------
  -- Case A-Y-K. Reverse it to K-Y-A; hence KY < KA directly.
  --------------------------------------------------------------------

  · have hKYA :
        Geo.Between K Y A :=
      (HilbertOrder.between_incidence
        A Y K hAYK_between).2.2.2.2

    exact
      hilbert_segmentLess_of_between
        Geo
        K Y A
        hKYA
/- END folded proof support: Crossing_circle_stage46_IV15_diameter_inner_point_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage47_IV15_chord_exterior_farther_v5.lean -/
/-!
# Forder IV.15 -- stage 47, exterior point of an isosceles chord

This file isolates the order fact corresponding to Forder IV.4.3.

Let KBD be an isosceles triangle with

  KB ~= KD.

If Y lies on the carrier BD beyond B,

  Y-B-D,

then Y is farther from K than the radius:

  KD < KY.

The proof is Euclid I.16 + I.19.

* In triangle KYB, KBD is an exterior angle, so
    angle KYB < angle KBD.
* Since KB ~= KD,
    angle KBD ~= angle KDB.
* Because Y-B-D, the rays YB,YD coincide and the rays DB,DY coincide.
  Hence
    angle KYD < angle KDY.
* I.19 in triangle KDY gives
    KD < KY.

The second theorem is the symmetric order B-D-Y.
-/

/--
If KB ~= KD and Y-B-D, then KD < KY.
-/
theorem hilbert_IV15_chord_exterior_farther_left_stage47
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (K B D Y : Geo.Point)
    (hKBD : Not (PrimCollinear Geo K B D))
    (hKB_KD : Geo.Congruent K B K D)
    (hYBD : Geo.Between Y B D) :
    HilbertSegmentLess Geo K D K Y := by

  have hYBDdata :=
    HilbertOrder.between_incidence
      Y B D hYBD

  have hBD :
      Ne B D :=
    hYBDdata.2.1

  have hYB :
      Ne Y B :=
    hYBDdata.1

  have hYD :
      Ne Y D :=
    hYBDdata.2.2.1

  have hYBDcol :
      PrimCollinear Geo Y B D :=
    hYBDdata.2.2.2.1

  --------------------------------------------------------------------
  -- Triangle K-Y-B is proper.
  --------------------------------------------------------------------

  have hKYB :
      Not (PrimCollinear Geo K Y B) := by
    intro hKYBcol

    have hBYD :
        PrimCollinear Geo B Y D :=
      PrimCollinearSwap
        Geo Y B D hYBDcol

    have hKBDcol :
        PrimCollinear Geo K B D :=
      hilbert_primCollinear_trans
        Geo
        K B Y D
        hYB.symm
        (PrimCollinearRotate
          Geo K Y B hKYBcol)
        hBYD

    exact hKBD hKBDcol

  --------------------------------------------------------------------
  -- Triangle K-D-Y is proper.
  --------------------------------------------------------------------

  have hKDY :
      Not (PrimCollinear Geo K D Y) := by
    intro hKDYcol

    have hBDY :
        PrimCollinear Geo B D Y :=
      PrimCollinearCycle
        Geo Y B D hYBDcol

    have hDYB :
        PrimCollinear Geo D Y B :=
      PrimCollinearCycle
        Geo B D Y hBDY

    have hKDB :
        PrimCollinear Geo K D B :=
      hilbert_primCollinear_trans
        Geo
        K D Y B
        hYD.symm
        hKDYcol
        hDYB

    exact
      hKBD
        (PrimCollinearRotate
          Geo K D B hKDB)

  --------------------------------------------------------------------
  -- I.16 in triangle K-Y-B, with Y-B-D.
  --------------------------------------------------------------------

  have hExterior :
      HilbertAngleLess Geo
        K Y B
        K B D :=
    euclid_proposition_16_second
      Geo
      K Y B D
      hKYB
      hYBD

  --------------------------------------------------------------------
  -- Normalize the left angle: ray YB = ray YD.
  --------------------------------------------------------------------

  have hRayYBD :
      HilbertSameRay Geo Y B D :=
    hilbert_sameRay_of_between
      Geo Y B D hYBD

  have hAtY :
      Geo.Angle K Y B =
      Geo.Angle K Y D :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      Y K B D
      hRayYBD

  have hKYD_KYB :
      Geo.AngleCongruent
        K Y D
        K Y B := by
    unfold Geometry.Geo.AngleCongruent
    rw [hAtY]
    exact
      Relation.EqvGen.refl
        (Geo.Angle K Y D)

  have hKYD :
      Not (PrimCollinear Geo K Y D) := by
    intro h
    exact
      hKDY
        (PrimCollinearRotate
          Geo K Y D h)

  have hExterior' :
      HilbertAngleLess Geo
        K Y D
        K B D :=
    hilbert_angleLess_transport_left
      Geo
      K Y B
      K Y D
      K B D
      hExterior
      hKYD
      hKYD_KYB

  --------------------------------------------------------------------
  -- Isosceles base angles:
  --
  --   KBD ~= BDK,
  --
  -- then reverse the second angle to KDB.
  --------------------------------------------------------------------

  have hKBD_KDB :
      Geo.AngleCongruent
        K B D
        K D B :=
    hilbert_isosceles_base_angles
      Geo
      K B D
      hKBD
      hKB_KD

  --------------------------------------------------------------------
  -- Since Y-B-D, also D-B-Y, hence ray DB = ray DY.
  --------------------------------------------------------------------

  have hDBY :
      Geo.Between D B Y :=
    hYBDdata.2.2.2.2

  have hRayDBY :
      HilbertSameRay Geo D B Y :=
    hilbert_sameRay_of_between
      Geo D B Y hDBY

  have hAtD :
      Geo.Angle K D B =
      Geo.Angle K D Y :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      D K B Y
      hRayDBY

  have hKBD_KDY :
      Geo.AngleCongruent
        K B D
        K D Y := by
    unfold Geometry.Geo.AngleCongruent
      at hKBD_KDB ⊢
    rw [← hAtD]
    exact hKBD_KDB

  --------------------------------------------------------------------
  -- Therefore angle KYD < angle KDY.
  --------------------------------------------------------------------

  have hFinalAngle :
      HilbertAngleLess Geo
        K Y D
        K D Y :=
    hilbert_angleLess_transport_right
      Geo
      K Y D
      K B D
      K D Y
      hExterior'
      hKDY
      hKBD_KDY

  --------------------------------------------------------------------
  -- I.19 in triangle K-D-Y gives KD < KY.
  --------------------------------------------------------------------

  exact
    euclid_proposition_19
      Geo
      K D Y
      hKDY
      hFinalAngle


/--
If KB ~= KD and B-D-Y, then KB < KY.
-/
theorem hilbert_IV15_chord_exterior_farther_right_stage47
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (K B D Y : Geo.Point)
    (hKBD : Not (PrimCollinear Geo K B D))
    (hKB_KD : Geo.Congruent K B K D)
    (hBDY : Geo.Between B D Y) :
    HilbertSegmentLess Geo K B K Y := by

  have hYDB :
      Geo.Between Y D B :=
    (HilbertOrder.between_incidence
      B D Y hBDY).2.2.2.2

  have hKDB :
      Not (PrimCollinear Geo K D B) := by
    intro h
    exact
      hKBD
        (PrimCollinearRotate
          Geo K D B h)

  have hKD_KB :
      Geo.Congruent K D K B :=
    hilbert_congruent_symmetry
      Geo
      K B
      K D
      hKB_KD

  exact
    hilbert_IV15_chord_exterior_farther_left_stage47
      Geo
      K D B Y
      hKDB
      hKD_KB
      hYDB
/- END folded proof support: Crossing_circle_stage47_IV15_chord_exterior_farther_v5.lean -/

/- BEGIN folded proof support: Crossing_circle_stage48_IV15_chord_opposite_diameter_v2.lean -/
/-!
# Forder IV.15 -- stage 48, the needed V.5 configuration

This stage proves the exact separation statement needed before applying
Forder IV.14 in the non-diameter branch of IV.15.

Assume:

* A-K-E is a diameter of the circle;
* A and E are on opposite sides of the chord line BD;
* Y lies on both BD and AE, with A-Y-E;
* B and D are circle points.

Then B and D lie on opposite sides of the diameter line AE.

The proof is purely synthetic:

1. stage 46 says Y is either K or strictly inside the circle;
2. therefore Y cannot equal B or D;
3. trichotomy on the chord carrier BD gives exactly one of
     B-Y-D, Y-B-D, B-D-Y;
4. stage 47 excludes the two exterior orders because they would put
   Y farther from K than a radius;
5. hence B-Y-D;
6. B and D are not on the diameter, since a circle point on the
   diameter through K must be one of the two antipodal endpoints A,E,
   both of which are off the chord line BD.

Thus Y is the witness for `HilbertOppositeSide Geo B D diameter`.
-/

/--
The V.5 separation configuration required in Forder IV.15.

A diameter AE crosses the chord line BD at an interior point Y.
If A,E are opposite sides of BD, then B,D are opposite sides of AE.
-/
theorem hilbert_IV15_chord_opposite_diameter_stage48
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B D E Y : Geo.Point)
    (diagonal diameter : Geo.Line)
    (hBD : Ne B D)
    (hBdiag : H.OnLine B diagonal)
    (hDdiag : H.OnLine D diagonal)
    (hYdiag : H.OnLine Y diagonal)
    (hKoffdiag : Not (H.OnLine K diagonal))
    (hAdiam : H.OnLine A diameter)
    (_hEdiam : H.OnLine E diameter)
    (hKdiam : H.OnLine K diameter)
    (hYdiam : H.OnLine Y diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hDcircle : HilbertCircle Geo K R D)
    (hEcircle : HilbertCircle Geo K R E)
    (hAKE : Geo.Between A K E)
    (hAYE : Geo.Between A Y E)
    (hOppAE : HilbertOppositeSide Geo A E diagonal) :
    HilbertOppositeSide Geo B D diameter := by

  --------------------------------------------------------------------
  -- Basic radius congruences.
  --------------------------------------------------------------------

  have hKA_KE :
      Geo.Congruent K A K E :=
    hilbert_circle_center_congruent
      Geo
      K R
      A E
      hAcircle hEcircle

  have hKB_KA :
      Geo.Congruent K B K A :=
    hilbert_circle_center_congruent
      Geo
      K R
      B A
      hBcircle hAcircle

  have hKD_KA :
      Geo.Congruent K D K A :=
    hilbert_circle_center_congruent
      Geo
      K R
      D A
      hDcircle hAcircle

  have hKB_KD :
      Geo.Congruent K B K D :=
    hilbert_circle_center_congruent
      Geo
      K R
      B D
      hBcircle hDcircle

  --------------------------------------------------------------------
  -- Y is either the center or strictly inside the circle.
  --------------------------------------------------------------------

  have hYinside :=
    hilbert_IV15_diameter_inner_point_stage46
      Geo
      A K E Y
      hAKE
      hAYE
      hKA_KE

  --------------------------------------------------------------------
  -- Y cannot coincide with B.
  --------------------------------------------------------------------

  have hYB :
      Ne Y B := by
    intro h
    subst Y

    rcases hYinside with hBK | hKBltKA

    · subst B

      have hAE :
          Ne A E :=
        (HilbertOrder.between_incidence
          A K E hAKE).2.2.1

      have hKneK :
          Ne K K :=
        hilbert_circle_center_ne_point_of_two_distinct_stage14
          Geo
          K R A E K
          hAE
          hAcircle hEcircle hBcircle

      exact hKneK rfl

    · exact
        (hilbert_segmentLess_not_congruent
          Geo
          K B
          K A
          hKBltKA)
        hKB_KA

  --------------------------------------------------------------------
  -- Y cannot coincide with D.
  --------------------------------------------------------------------

  have hYD :
      Ne Y D := by
    intro h
    subst Y

    rcases hYinside with hDK | hKDltKA

    · subst D

      have hAE :
          Ne A E :=
        (HilbertOrder.between_incidence
          A K E hAKE).2.2.1

      have hKneK :
          Ne K K :=
        hilbert_circle_center_ne_point_of_two_distinct_stage14
          Geo
          K R A E K
          hAE
          hAcircle hEcircle hDcircle

      exact hKneK rfl

    · exact
        (hilbert_segmentLess_not_congruent
          Geo
          K D
          K A
          hKDltKA)
        hKD_KA

  --------------------------------------------------------------------
  -- K,B,D form a genuine triangle because K is off the chord line.
  --------------------------------------------------------------------

  have hBDK :
      Not (PrimCollinear Geo B D K) :=
    hilbert_not_collinear_of_off_line
      Geo
      B D K
      diagonal
      hBD
      hBdiag
      hDdiag
      hKoffdiag

  have hKBD :
      Not (PrimCollinear Geo K B D) := by
    intro h
    exact
      hBDK
        (PrimCollinearCycle
          Geo K B D h)

  --------------------------------------------------------------------
  -- B,Y,D are collinear on the diagonal.
  --------------------------------------------------------------------

  have hBYDcol :
      PrimCollinear Geo B Y D :=
    ⟨diagonal,
      hBdiag,
      hYdiag,
      hDdiag⟩

  --------------------------------------------------------------------
  -- Trichotomy on B,Y,D.
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        B Y D
        hYB.symm
        hYD
        hBD
        hBYDcol
    with
    hBYD | hYBD | hBDY

  --------------------------------------------------------------------
  -- Desired order B-Y-D.
  --------------------------------------------------------------------

  · have hBoff :
        Not (H.OnLine B diameter) := by
      intro hBdiam

      have hAB :
          Ne A B := by
        intro hAB
        subst B
        exact hOppAE.1 hBdiag

      have hMidB :
          HilbertIsMidpoint Geo K A B :=
        hilbert_circle_center_midpoint_of_chord_stage16
          Geo
          K R A B
          diameter
          hAB
          hAdiam
          hBdiam
          hKdiam
          hAcircle
          hBcircle

      have hAKB :
          Geo.Between A K B :=
        hMidB.1

      have hRayKBE :
          HilbertSameRay Geo K B E :=
        hilbert_sameRay_beyond_common_middle_stage22
          Geo
          A K B E
          hAKB
          hAKE

      have hRayKBB :
          HilbertSameRay Geo K B B :=
        hilbert_sameRay_refl
          Geo
          K B
          (hRayKBE.1)

      have hKB_KE :
          Geo.Congruent K B K E :=
        hilbert_circle_center_congruent
          Geo
          K R
          B E
          hBcircle hEcircle

      have hEB :
          E = B :=
        hilbert_segment_construction_unique
          Geo
          K E
          K B
          E B
          hRayKBE
          hRayKBB
          (hilbert_congruent_reflexive Geo K E)
          hKB_KE

      subst B
      exact hOppAE.2.1 hBdiag

    have hDoff :
        Not (H.OnLine D diameter) := by
      intro hDdiam

      have hAD :
          Ne A D := by
        intro hAD
        subst D
        exact hOppAE.1 hDdiag

      have hMidD :
          HilbertIsMidpoint Geo K A D :=
        hilbert_circle_center_midpoint_of_chord_stage16
          Geo
          K R A D
          diameter
          hAD
          hAdiam
          hDdiam
          hKdiam
          hAcircle
          hDcircle

      have hAKD :
          Geo.Between A K D :=
        hMidD.1

      have hRayKDE :
          HilbertSameRay Geo K D E :=
        hilbert_sameRay_beyond_common_middle_stage22
          Geo
          A K D E
          hAKD
          hAKE

      have hRayKDD :
          HilbertSameRay Geo K D D :=
        hilbert_sameRay_refl
          Geo
          K D
          (hRayKDE.1)

      have hKD_KE :
          Geo.Congruent K D K E :=
        hilbert_circle_center_congruent
          Geo
          K R
          D E
          hDcircle hEcircle

      have hED :
          E = D :=
        hilbert_segment_construction_unique
          Geo
          K E
          K D
          E D
          hRayKDE
          hRayKDD
          (hilbert_congruent_reflexive Geo K E)
          hKD_KE

      subst D
      exact hOppAE.2.1 hDdiag

    exact
      ⟨hBoff,
        hDoff,
        ⟨Y,
          hBYD,
          hYdiam⟩⟩

  --------------------------------------------------------------------
  -- Exterior order Y-B-D is impossible.
  --------------------------------------------------------------------

  · have hKD_KY :
        HilbertSegmentLess Geo K D K Y :=
      hilbert_IV15_chord_exterior_farther_left_stage47
        Geo
        K B D Y
        hKBD
        hKB_KD
        hYBD

    rcases hYinside with hYK | hKY_KA

    · subst Y

      have hKD_KK :
          HilbertSegmentLess Geo K D K K :=
        hKD_KY

      rcases hKD_KK with
        ⟨P, hKPK, _⟩

      exact
        False.elim
          ((HilbertOrder.between_incidence
            K P K hKPK).2.2.1 rfl)

    · have hKD_KA :
          Geo.Congruent K D K A :=
        hKD_KA

      have hKA_KD :
          Geo.Congruent K A K D :=
        hilbert_congruent_symmetry
          Geo
          K D
          K A
          hKD_KA

      have hKA_KY :
          HilbertSegmentLess Geo K A K Y :=
        hilbert_segmentLess_congruent_left
          Geo
          K D
          K A
          K Y
          hKD_KY
          hKA_KD

      exact
        False.elim
          ((hilbert_segmentLess_asymm
            Geo
            K Y
            K A
            hKY_KA)
          hKA_KY)

  --------------------------------------------------------------------
  -- Exterior order B-D-Y is impossible.
  --------------------------------------------------------------------

  · have hKB_KY :
        HilbertSegmentLess Geo K B K Y :=
      hilbert_IV15_chord_exterior_farther_right_stage47
        Geo
        K B D Y
        hKBD
        hKB_KD
        hBDY

    rcases hYinside with hYK | hKY_KA

    · subst Y

      rcases hKB_KY with
        ⟨P, hKPK, _⟩

      exact
        False.elim
          ((HilbertOrder.between_incidence
            K P K hKPK).2.2.1 rfl)

    · have hKA_KB :
          Geo.Congruent K A K B :=
        hilbert_congruent_symmetry
          Geo
          K B
          K A
          hKB_KA

      have hKA_KY :
          HilbertSegmentLess Geo K A K Y :=
        hilbert_segmentLess_congruent_left
          Geo
          K B
          K A
          K Y
          hKB_KY
          hKA_KB

      exact
        False.elim
          ((hilbert_segmentLess_asymm
            Geo
            K Y
            K A
            hKY_KA)
          hKA_KY)
/- END folded proof support: Crossing_circle_stage48_IV15_chord_opposite_diameter_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage49_IV15_antipodal_tail_sameSide_v2.lean -/
/-!
# Forder IV.15 -- stage 49, antipodal tail stays on one side

Assume:

* A and K are on opposite sides of the line d;
* A-K-E.

Let Y be the crossing point of AK with d. Then A-Y-K-E, hence K and E
lie on the same ray from Y. Since Y lies on d, the standard theorem
`hilbert_sameRay_points_sameSide` implies that K and E lie on the same
side of d.

To apply that theorem we need a second point of d which is not on the
carrier YE. If d is given by two distinct points B,D, at least one of
them has this property; otherwise the carrier YE would coincide with d,
forcing K onto d.
-/

/--
If A and K are on opposite sides of d and A-K-E, then K and E lie on
the same side of d.
-/
theorem hilbert_IV15_antipodal_tail_sameSide_stage49
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (A K E B D : Geo.Point)
    (d : Geo.Line)
    (hBD : Ne B D)
    (hBd : H.OnLine B d)
    (hDd : H.OnLine D d)
    (hOppAK : HilbertOppositeSide Geo A K d)
    (hAKE : Geo.Between A K E) :
    HilbertSameSide Geo K E d := by

  have hKoff :
      Not (H.OnLine K d) :=
    hOppAK.2.1

  rcases hOppAK.2.2 with
    ⟨Y, hAYK, hYd⟩

  have hTrans :=
    hilbert_between_inner_trans
      Geo
      A Y K E
      hAYK
      hAKE

  have hYKE :
      Geo.Between Y K E :=
    hTrans.1

  have hAYE :
      Geo.Between A Y E :=
    hTrans.2

  have hYKEdata :=
    HilbertOrder.between_incidence
      Y K E hYKE

  have hYK :
      Ne Y K :=
    hYKEdata.1

  have hYE :
      Ne Y E :=
    hYKEdata.2.2.1

  rcases
      (HilbertOrder.between_incidence
        A Y E hAYE).2.2.2.1
    with
    ⟨lineYE,
      hAline,
      hYline,
      hEline⟩

  have hKline :
      H.OnLine K lineYE :=
    hilbert_between_on_line
      Geo
      Y K E
      lineYE
      hYline hEline hYKE

  have hRayYKE :
      HilbertSameRay Geo Y K E :=
    hilbert_sameRay_of_between
      Geo
      Y K E
      hYKE

  have hRayYKK :
      HilbertSameRay Geo Y K K :=
    hilbert_sameRay_refl
      Geo
      Y K
      hYK.symm

  by_cases hBline :
      H.OnLine B lineYE

  --------------------------------------------------------------------
  -- B lies on YE, so D must be off YE.
  --------------------------------------------------------------------

  · have hDoffLine :
        Not (H.OnLine D lineYE) := by
      intro hDline

      have hEq :
          lineYE = d :=
        HilbertPlaneIncidence.line_unique
          B D hBD
          lineYE d
          hBline hDline
          hBd hDd

      exact
        hKoff
          (hEq ▸ hKline)

    exact
      hilbert_sameRay_points_sameSide
        Geo
        Y K
        K E
        D
        lineYE d
        hYline hKline
        hYd hDd
        hDoffLine
        hRayYKK
        hRayYKE

  --------------------------------------------------------------------
  -- B itself is the required second point of d off YE.
  --------------------------------------------------------------------

  · exact
      hilbert_sameRay_points_sameSide
        Geo
        Y K
        K E
        B
        lineYE d
        hYline hKline
        hYd hBd
        hBline
        hRayYKK
        hRayYKE
/- END folded proof support: Crossing_circle_stage49_IV15_antipodal_tail_sameSide_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage50_IV15_sameSide_CK_v2.lean -/
/-!
# Forder IV.15 -- stage 50, off-diameter branch with C and K on the same side

This closes the main non-diameter branch of Forder IV.15.

Assume A,C are opposite sides of the chord line BD and C,K are on the
same side of BD.

1. Construct E antipodal to A, so A-K-E.
2. Stage 45 gives A,E opposite sides of BD.
3. Stage 48 gives B,D opposite sides of the diameter AE.
4. IV.14 gives BAD supplementary to BED.
5. Stage 49 puts E and K on the same side of BD.
6. IV.12.1 gives BED ~= BCD.
7. Book Zero supplement transport moves the supplement from E to C.

The conclusion is exactly the IV.15 target:
there is Xc with B-C-Xc and BAD ~= XcCD.
-/

/--
The off-diameter IV.15 branch in which C and the center K lie on the
same side of the diagonal BD.
-/
theorem hilbert_forder_IV15_sameSide_CK_stage50
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diagonal : Geo.Line)
    (hBD : Ne B D)
    (hBdiag : H.OnLine B diagonal)
    (hDdiag : H.OnLine D diagonal)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppAC : HilbertOppositeSide Geo A C diagonal)
    (hSameCK : HilbertSameSide Geo C K diagonal) :
    exists Xc : Geo.Point,
      BookZeroSupplement Geo B C D D Xc /\
      Geo.AngleCongruent B A D Xc C D := by

  --------------------------------------------------------------------
  -- The center is off the diagonal.
  --------------------------------------------------------------------

  have hKoffdiag :
      Not (H.OnLine K diagonal) :=
    hSameCK.2.1

  --------------------------------------------------------------------
  -- Antipode E of A.  Use B,D as the distinct circle points which
  -- certify that the circle is nondegenerate.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_antipode_stage14
        Geo
        K R B D A
        hBD
        hBcircle
        hDcircle
        hAcircle
    with
    ⟨E, hAKE, hEcircle⟩

  have hAKEdata :=
    HilbertOrder.between_incidence
      A K E hAKE

  have hAE :
      Ne A E :=
    hAKEdata.2.2.1

  --------------------------------------------------------------------
  -- Construct the carrier of the diameter AE.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A E hAE
    with
    ⟨diameter, hAdiam, hEdiam⟩

  have hKdiam :
      H.OnLine K diameter :=
    hilbert_between_on_line
      Geo
      A K E
      diameter
      hAdiam hEdiam hAKE

  --------------------------------------------------------------------
  -- A and E are opposite sides of BD.
  --------------------------------------------------------------------

  have hOppAE :
      HilbertOppositeSide Geo A E diagonal :=
    hilbert_IV15_antipode_opposite_diagonal_stage45
      Geo
      A C K E
      diagonal
      hOppAC
      hSameCK
      hAKE

  rcases hOppAE.2.2 with
    ⟨Y, hAYE, hYdiag⟩

  have hYdiam :
      H.OnLine Y diameter :=
    hilbert_between_on_line
      Geo
      A Y E
      diameter
      hAdiam hEdiam hAYE

  --------------------------------------------------------------------
  -- The chord endpoints B,D are opposite sides of the diameter AE.
  --------------------------------------------------------------------

  have hOppBDdiam :
      HilbertOppositeSide Geo B D diameter :=
    hilbert_IV15_chord_opposite_diameter_stage48
      Geo
      K R A B D E Y
      diagonal diameter
      hBD
      hBdiag
      hDdiag
      hYdiag
      hKoffdiag
      hAdiam
      hEdiam
      hKdiam
      hYdiam
      hAcircle
      hBcircle
      hDcircle
      hEcircle
      hAKE
      hAYE
      hOppAE

  --------------------------------------------------------------------
  -- IV.14 on the cyclic quadrilateral A-B-E-D:
  --
  --   BAD is congruent to a supplement of BED.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV14_diameter_supplement_stage43
        Geo
        K R A B E D
        diameter
        hAE
        hAdiam
        hEdiam
        hKdiam
        hAcircle
        hBcircle
        hEcircle
        hDcircle
        hOppBDdiam
    with
    ⟨X, hSuppE, hBAD_XED⟩

  --------------------------------------------------------------------
  -- Since A and K are opposite sides of BD and A-K-E, K and E are
  -- on the same side of BD.
  --------------------------------------------------------------------

  have hOppAK :
      HilbertOppositeSide Geo A K diagonal :=
    hilbert_oppositeSide_transport_right
      Geo
      A C K
      diagonal
      hOppAC
      hSameCK

  have hSameKE :
      HilbertSameSide Geo K E diagonal :=
    hilbert_IV15_antipodal_tail_sameSide_stage49
      Geo
      A K E B D
      diagonal
      hBD
      hBdiag
      hDdiag
      hOppAK
      hAKE

  have hSameEK :
      HilbertSameSide Geo E K diagonal :=
    hilbert_sameSide_symm
      Geo K E diagonal hSameKE

  --------------------------------------------------------------------
  -- IV.12.1 on chord BD:
  --
  --   BED ~= BCD.
  --------------------------------------------------------------------

  have hBED_BCD :
      Geo.AngleCongruent B E D B C D :=
    hilbert_forder_IV12_1_same_segment_stage34
      Geo
      K R B D E C
      diagonal
      hBD
      hBdiag
      hDdiag
      hBcircle
      hDcircle
      hEcircle
      hCcircle
      hSameEK
      hSameCK

  --------------------------------------------------------------------
  -- Construct the target supplement at C: B-C-Xc.
  --------------------------------------------------------------------

  have hCoff :
      Not (H.OnLine C diagonal) :=
    hSameCK.1

  have hBC :
      Ne B C := by
    intro hBC
    subst C
    exact hCoff hBdiag

  rcases
      HilbertOrder.between_extension
        B C hBC
    with
    ⟨Xc, hBCXc⟩

  have hCD :
      Ne C D := by
    intro hCD
    subst C
    exact hCoff hDdiag

  have hRayCDD :
      HilbertSameRay Geo C D D :=
    hilbert_sameRay_refl
      Geo C D hCD.symm

  have hSuppC :
      BookZeroSupplement Geo B C D D Xc :=
    ⟨hRayCDD, hBCXc⟩

  --------------------------------------------------------------------
  -- Properness of BED and BCD for Book Zero supplement transport.
  --------------------------------------------------------------------

  have hEoff :
      Not (H.OnLine E diagonal) :=
    hOppAE.2.1

  have hBDE :
      Not (PrimCollinear Geo B D E) :=
    hilbert_not_collinear_of_off_line
      Geo
      B D E
      diagonal
      hBD
      hBdiag
      hDdiag
      hEoff

  have hBED :
      Not (PrimCollinear Geo B E D) := by
    intro h
    exact
      hBDE
        (PrimCollinearRotate
          Geo B E D h)

  have hBDC :
      Not (PrimCollinear Geo B D C) :=
    hilbert_not_collinear_of_off_line
      Geo
      B D C
      diagonal
      hBD
      hBdiag
      hDdiag
      hCoff

  have hBCD :
      Not (PrimCollinear Geo B C D) := by
    intro h
    exact
      hBDC
        (PrimCollinearRotate
          Geo B C D h)

  --------------------------------------------------------------------
  -- Supplements of BED and BCD are congruent.
  --
  -- hSuppE: BED has supplement DEX (angle DEX).
  -- hSuppC: BCD has supplement DCXc (angle DCXc).
  --------------------------------------------------------------------

  have hDEX_DCXc :
      Geo.AngleCongruent D E X D C Xc :=
    bookZero_43_supplements
      Geo
      B E D
      D X
      B C D
      D Xc
      hBED_BCD
      hSuppE
      hSuppC
      hBED
      hBCD

  --------------------------------------------------------------------
  -- Re-orient both supplement angles:
  --
  --   XED ~= XcCD.
  --------------------------------------------------------------------

  have hXED_XcCD :
      Geo.AngleCongruent X E D Xc C D :=
    (Geo.angle_congruent_reverse_second
      X E D
      D C Xc).mp
      ((Geo.angle_congruent_reverse_first
        D E X
        D C Xc).mp
        hDEX_DCXc)

  --------------------------------------------------------------------
  -- BAD ~= XED ~= XcCD.
  --------------------------------------------------------------------

  have hBAD_XcCD :
      Geo.AngleCongruent B A D Xc C D :=
    Geo.angle_congruent_transitivity
      B A D
      X E D
      Xc C D
      hBAD_XED
      hXED_XcCD

  exact
    ⟨Xc,
      hSuppC,
      hBAD_XcCD⟩
/- END folded proof support: Crossing_circle_stage50_IV15_sameSide_CK_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage51_IV15_two_opposites_sameSide_v2.lean -/
/-!
# Forder IV.15 -- stage 51, half-plane parity without noncollinearity

If C is opposite both A and K with respect to a line d, then A and K
lie on the same side of d.

For a genuine triangle C-A-K this is the standard Pasch parity lemma
`hilbert_two_oppositeSides_sameSide_VI`.

The only missing case is collinearity.  There the order trichotomy on
C,A,K reduces the proof to stage 49:

* C-A-K: from C opposite A and C-A-K, the tail A-K stays on one side;
* C-K-A: symmetrically, K-A stays on one side;
* A-C-K is impossible, because stage 49 applied to A-C-K would make
  C and K same-side, contradicting C opposite K.
-/

/--
Two points which are both opposite to a common point are same-side,
with no noncollinearity hypothesis.
-/
theorem hilbert_IV15_two_opposites_sameSide_stage51
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (C A K B D : Geo.Point)
    (d : Geo.Line)
    (hBD : Ne B D)
    (hBd : H.OnLine B d)
    (hDd : H.OnLine D d)
    (hOppCA : HilbertOppositeSide Geo C A d)
    (hOppCK : HilbertOppositeSide Geo C K d) :
    HilbertSameSide Geo A K d := by

  by_cases hAK : A = K

  · subst K
    exact
      hilbert_sameSide_refl
        Geo
        A d
        hOppCA.2.1

  have hCA :
      Ne C A := by
    rcases hOppCA.2.2 with
      ⟨X, hCXA, _⟩
    exact
      (HilbertOrder.between_incidence
        C X A hCXA).2.2.1

  have hCK :
      Ne C K := by
    rcases hOppCK.2.2 with
      ⟨X, hCXK, _⟩
    exact
      (HilbertOrder.between_incidence
        C X K hCXK).2.2.1

  by_cases hCol :
      PrimCollinear Geo C A K

  --------------------------------------------------------------------
  -- Collinear case.
  --------------------------------------------------------------------

  · rcases
        hilbert_between_trichotomy
          Geo
          C A K
          hCA
          hAK
          hCK
          hCol
      with
      hCAK | hACK | hCKA

    --------------------------------------------------------------
    -- C-A-K.
    --------------------------------------------------------------

    · exact
        hilbert_IV15_antipodal_tail_sameSide_stage49
          Geo
          C A K B D
          d
          hBD
          hBd
          hDd
          hOppCA
          hCAK

    --------------------------------------------------------------
    -- A-C-K is impossible: stage 49 would make C,K same-side.
    --------------------------------------------------------------

    · have hOppAC :
          HilbertOppositeSide Geo A C d :=
        hilbert_oppositeSide_symm
          Geo C A d hOppCA

      have hSameCK :
          HilbertSameSide Geo C K d :=
        hilbert_IV15_antipodal_tail_sameSide_stage49
          Geo
          A C K B D
          d
          hBD
          hBd
          hDd
          hOppAC
          hACK

      exact
        False.elim
          ((hilbert_oppositeSide_not_sameSide
            Geo C K d hOppCK)
          hSameCK)

    --------------------------------------------------------------
    -- C-K-A.
    --------------------------------------------------------------

    · have hSameKA :
          HilbertSameSide Geo K A d :=
        hilbert_IV15_antipodal_tail_sameSide_stage49
          Geo
          C K A B D
          d
          hBD
          hBd
          hDd
          hOppCK
          hCKA

      exact
        hilbert_sameSide_symm
          Geo K A d hSameKA

  --------------------------------------------------------------------
  -- Noncollinear case: ordinary Pasch parity.
  --------------------------------------------------------------------

  · rcases hOppCA.2.2 with
      ⟨X, hCXA, hXd⟩

    rcases hOppCK.2.2 with
      ⟨Y, hCYK, hYd⟩

    exact
      hilbert_third_side_endpoints_sameSide
        Geo
        C A K
        X Y
        d
        hCol
        hCXA
        hCYK
        hXd
        hYd
/- END folded proof support: Crossing_circle_stage51_IV15_two_opposites_sameSide_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage52_IV15_complete_v1.lean -/
/-!
# Forder IV.15 -- stage 52, complete theorem

This closes Forder IV.15.

Given a cyclic quadrilateral A-B-C-D with A,C on opposite sides of
the diagonal BD:

* if the center K lies on BD, stage 44 applies;
* otherwise, if C and K are on the same side of BD, stage 50 applies;
* in the remaining case C and K are opposite. Since C and A are also
  opposite, stage 51 puts A and K on the same side. We then apply
  stage 50 to the cyclically relabelled quadrilateral C-D-A-B.

The last branch returns the same supplementary-angle content with the
supplement represented at A rather than at C. A final
`bookZero_43_supplements` normalization converts it to the public IV.15
interface.
-/

/--
Complete Forder IV.15 in the synthetic Book Zero supplement language.
-/
theorem hilbert_forder_IV15_complete_stage52
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV15CyclicSupplement
      (Geo := Geo) := by

  intro A B C D diagonal
    hBD
    hBdiag
    hDdiag
    hCyclic
    hOppAC
    hBAD
    hBCD

  --------------------------------------------------------------------
  -- Put the cyclic quadrilateral on one explicit circle.
  --------------------------------------------------------------------

  rcases
      hilbert_concyclic4_circle
        Geo
        A B C D
        hCyclic
    with
    ⟨K,
      hAcircle,
      hBcircle,
      hCcircle,
      hDcircle⟩

  --------------------------------------------------------------------
  -- Case 1: the center lies on the diagonal BD.
  --------------------------------------------------------------------

  by_cases hKdiag :
      H.OnLine K diagonal

  · exact
      hilbert_forder_IV15_center_on_diagonal_stage44
        Geo
        K A A B C D
        diagonal
        hBD
        hBdiag
        hDdiag
        hKdiag
        hAcircle
        hBcircle
        hCcircle
        hDcircle
        hOppAC

  --------------------------------------------------------------------
  -- From now on K is off BD.
  --------------------------------------------------------------------

  · by_cases hSameCK :
        HilbertSameSide Geo C K diagonal

    ------------------------------------------------------------------
    -- Case 2: C and K are on the same side of BD.
    ------------------------------------------------------------------

    · exact
        hilbert_forder_IV15_sameSide_CK_stage50
          Geo
          K A A B C D
          diagonal
          hBD
          hBdiag
          hDdiag
          hAcircle
          hBcircle
          hCcircle
          hDcircle
          hOppAC
          hSameCK

    ------------------------------------------------------------------
    -- Case 3: C and K are not on the same side.
    ------------------------------------------------------------------

    · have hCoff :
          Not (H.OnLine C diagonal) :=
        hOppAC.2.1

      have hOppCK :
          HilbertOppositeSide Geo C K diagonal :=
        hilbert_oppositeSide_of_not_sameSide
          Geo
          C K
          diagonal
          hCoff
          hKdiag
          hSameCK

      have hOppCA :
          HilbertOppositeSide Geo C A diagonal :=
        hilbert_oppositeSide_symm
          Geo A C diagonal hOppAC

      have hSameAK :
          HilbertSameSide Geo A K diagonal :=
        hilbert_IV15_two_opposites_sameSide_stage51
          Geo
          C A K B D
          diagonal
          hBD
          hBdiag
          hDdiag
          hOppCA
          hOppCK

      ----------------------------------------------------------------
      -- Apply stage 50 to the cyclic relabelling
      --
      --   (A,B,C,D) -> (C,D,A,B).
      --
      -- It returns
      --
      --   D-A-X
      --   angle DCB ~= angle XAB.
      ----------------------------------------------------------------

      rcases
          hilbert_forder_IV15_sameSide_CK_stage50
            Geo
            K A C D A B
            diagonal
            hBD.symm
            hDdiag
            hBdiag
            hCcircle
            hDcircle
            hAcircle
            hBcircle
            hOppCA
            hSameAK
        with
        ⟨X,
          hSuppA,
          hDCB_XAB⟩

      ----------------------------------------------------------------
      -- Normalize the base-angle congruence:
      --
      --   DCB ~= XAB
      -- becomes
      --   BCD ~= XAB.
      ----------------------------------------------------------------

      have hBCD_XAB :
          Geo.AngleCongruent B C D X A B :=
        (Geo.angle_congruent_reverse_first
          D C B
          X A B).mp
          hDCB_XAB

      ----------------------------------------------------------------
      -- The same witness X also says that BAD is the supplement of
      -- XAB, because D-A-X implies X-A-D.
      ----------------------------------------------------------------

      have hXAD :
          Geo.Between X A D :=
        (HilbertOrder.between_incidence
          D A X hSuppA.2).2.2.2.2

      have hSuppARev :
          BookZeroSupplement Geo X A B B D :=
        ⟨hSuppA.1,
          hXAD⟩

      ----------------------------------------------------------------
      -- Construct the public target supplement at C: B-C-Xc.
      ----------------------------------------------------------------

      have hBC :
          Ne B C :=
        hilbert_noncollinear_ne_first
          Geo B C D hBCD

      rcases
          HilbertOrder.between_extension
            B C hBC
        with
        ⟨Xc, hBCXc⟩

      have hCD :
          Ne C D := by
        intro hCD
        subst D

        rcases
            HilbertPlaneIncidence.line_through
              B C hBC
          with
          ⟨l, hBl, hCl⟩

        exact
          hBCD
            ⟨l,
              hBl,
              hCl,
              hCl⟩

      have hRayCDD :
          HilbertSameRay Geo C D D :=
        hilbert_sameRay_refl
          Geo C D hCD.symm

      have hSuppC :
          BookZeroSupplement Geo B C D D Xc :=
        ⟨hRayCDD,
          hBCXc⟩

      ----------------------------------------------------------------
      -- Properness of XAB.
      --
      -- If X,A,B were collinear, then D,A,X and X,A,B would force
      -- D,A,B collinear, contradicting the proper angle BAD.
      ----------------------------------------------------------------

      have hDAXdata :=
        HilbertOrder.between_incidence
          D A X hSuppA.2

      have hAX :
          Ne A X :=
        hDAXdata.2.1

      have hDAXcol :
          PrimCollinear Geo D A X :=
        hDAXdata.2.2.2.1

      have hXAB :
          Not (PrimCollinear Geo X A B) := by
        intro h

        have hAXB :
            PrimCollinear Geo A X B :=
          PrimCollinearSwap
            Geo X A B h

        have hDAB :
            PrimCollinear Geo D A B :=
          hilbert_primCollinear_trans
            Geo
            D A X B
            hAX
            hDAXcol
            hAXB

        exact
          hBAD
            (PrimCollinearSymm
              Geo D A B hDAB)

      ----------------------------------------------------------------
      -- Supplements of the congruent base angles BCD and XAB are
      -- congruent:
      --
      --   DCXc ~= BAD.
      ----------------------------------------------------------------

      have hDCXc_BAD :
          Geo.AngleCongruent D C Xc B A D :=
        bookZero_43_supplements
          Geo
          B C D
          D Xc
          X A B
          B D
          hBCD_XAB
          hSuppC
          hSuppARev
          hBCD
          hXAB

      have hXcCD_BAD :
          Geo.AngleCongruent Xc C D B A D :=
        (Geo.angle_congruent_reverse_first
          D C Xc
          B A D).mp
          hDCXc_BAD

      have hBAD_XcCD :
          Geo.AngleCongruent B A D Xc C D :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          Xc C D
          B A D
          hXcCD_BAD

      exact
        ⟨Xc,
          hSuppC,
          hBAD_XcCD⟩
/- END folded proof support: Crossing_circle_stage52_IV15_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage53_IV16_opposite_complete_v1.lean -/
/-!
# Forder IV.16 opposite-side half -- stage 53, completed

Stage 13 proved that Forder IV.15 implies the opposite-side half of IV.16.

Stage 52 now supplies the complete synthetic proof of IV.15.

Therefore the opposite-side half of IV.16 is closed with no remaining
circle-theorem parameter.
-/

/--
Complete opposite-side half of Forder IV.16.
-/
theorem hilbert_forder_IV16_opposite_complete_stage53
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16OppositeSide
      (Geo := Geo) := by

  exact
    hilbert_forder_IV16_opposite_of_IV15_stage13
      Geo
      (hilbert_forder_IV15_complete_stage52
        Geo)
/- END folded proof support: Crossing_circle_stage53_IV16_opposite_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage54_IV16_same_complete_v1.lean -/
/-!
# Forder IV.16 same-side half -- stage 54, completed

Stage 15 reduces the same-side half of Forder IV.16 to:

* Forder IV.12.1;
* Forder IV.13;
* Forder IV.15.

All three are now complete:

* IV.12.1 -- stage 34;
* IV.13   -- stage 17;
* IV.15   -- stage 52.

Hence the same-side half of IV.16 is closed with no remaining
circle-theorem parameter.
-/

/--
Complete same-side half of Forder IV.16.
-/
theorem hilbert_forder_IV16_same_complete_stage54
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16SameSide
      (Geo := Geo) := by

  exact
    hilbert_forder_IV16_same_of_IV12_1_IV13_IV15_stage15
      Geo
      (hilbert_forder_IV12_1_same_segment_stage34
        Geo)
      (hilbert_forder_IV13_diameter_right_angle_stage17
        Geo)
      (hilbert_forder_IV15_complete_stage52
        Geo)
/- END folded proof support: Crossing_circle_stage54_IV16_same_complete_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage55_transfer_of_IV18_v1.lean -/
/-!
# Crossing circle -- stage 55, IV.16 fully discharged

The complete crossing-rays transfer of stage 11 depended on three lower
circle-theoretic inputs:

* Forder IV.16, same-side half;
* Forder IV.16, opposite-side half;
* Forder IV.18, tangent-chord theorem.

Stages 53 and 54 now close both halves of IV.16. Therefore the crossing
transfer depends only on IV.18.
-/

/--
Crossing-rays transfer with both halves of Forder IV.16 discharged.
-/
theorem hilbert_crossing_rays_transfer_of_IV18_stage55
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV18 :
      HilbertForderIV18TangentChord
        (Geo := Geo)) :
    HilbertCrossingRaysTransfer
      (Geo := Geo) := by

  exact
    hilbert_crossing_rays_transfer_stage11
      Geo
      (hilbert_forder_IV16_same_complete_stage54
        Geo)
      (hilbert_forder_IV16_opposite_complete_stage53
        Geo)
      hIV18
/- END folded proof support: Crossing_circle_stage55_transfer_of_IV18_v1.lean -/

/- BEGIN folded proof support: Crossing_circle_stage56_IV17_triangle_not_supplement_v2.lean -/
/-!
# Forder IV.17 preparation -- stage 56

A technical triangle-order lemma needed in the second secant branch of
Forder IV.17.

For a proper triangle X-S-A, let U lie beyond A on the ray from S:

  S-A-U.

Then the interior angle XSA cannot be congruent to the exterior angle
XAU.

This is exactly Euclid I.17 in the synthetic angle-order language:
I.17 says that XSA is strictly smaller than any supplement of XAS.
-/

/--
In a proper triangle X-S-A, if S-A-U, then

  angle XSA != angle XAU.
-/
theorem hilbert_IV17_triangle_angle_not_supplement_stage56
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (X S A U : Geo.Point)
    (hXSA : Not (PrimCollinear Geo X S A))
    (hSAU : Geo.Between S A U) :
    Not (Geo.AngleCongruent X S A X A U) := by

  intro hCong

  --------------------------------------------------------------------
  -- Euclid I.17: angle XSA is strictly smaller than a supplement of
  -- angle XAS.  The witness is some E with S-A-E.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_17_ABC_ACB
        Geo
        X S A
        hXSA
    with
    ⟨E, hSAE, hLessE⟩

  --------------------------------------------------------------------
  -- E and U are both beyond A from S, hence they determine the same
  -- ray from A.
  --------------------------------------------------------------------

  have hRayAEU :
      HilbertSameRay Geo A E U :=
    hilbert_sameRay_beyond_common_middle_stage22
      Geo
      S A E U
      hSAE
      hSAU

  have hAngleEq :
      Geo.Angle X A E =
      Geo.Angle X A U :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      A X E U
      hRayAEU

  have hE_U :
      Geo.AngleCongruent X A E X A U := by
    unfold Geometry.Geo.AngleCongruent
    rw [hAngleEq]
    exact Relation.EqvGen.refl _

  --------------------------------------------------------------------
  -- The target angle XAU is proper.
  --------------------------------------------------------------------

  have hSAUdata :=
    HilbertOrder.between_incidence
      S A U hSAU

  have hAU :
      Ne A U :=
    hSAUdata.2.1

  have hSAUcol :
      PrimCollinear Geo S A U :=
    hSAUdata.2.2.2.1

  have hAUS :
      PrimCollinear Geo A U S :=
    PrimCollinearCycle
      Geo S A U hSAUcol

  have hXAU :
      Not (PrimCollinear Geo X A U) := by
    intro h

    rcases
        HilbertPlaneIncidence.line_through
          A U hAU
      with
      ⟨l, hAl, hUl⟩

    have hSl :
        H.OnLine S l :=
      hilbert_collinear_on_line
        Geo
        A U S
        l
        hAU
        hAl
        hUl
        hAUS

    have hAUX :
        PrimCollinear Geo A U X :=
      PrimCollinearCycle
        Geo X A U h

    have hXl :
        H.OnLine X l :=
      hilbert_collinear_on_line
        Geo
        A U X
        l
        hAU
        hAl
        hUl
        hAUX

    exact
      hXSA
        ⟨l,
          hXl,
          hSl,
          hAl⟩

  --------------------------------------------------------------------
  -- Transport the I.17 strict inequality from XAE to XAU.
  --------------------------------------------------------------------

  have hLessU :
      HilbertAngleLess Geo
        X S A
        X A U :=
    hilbert_angleLess_transport_right
      Geo
      X S A
      X A E
      X A U
      hLessE
      hXAU
      hE_U

  --------------------------------------------------------------------
  -- If XSA ~= XAU, transport once more and obtain XSA < XSA.
  --------------------------------------------------------------------

  have hU_S :
      Geo.AngleCongruent X A U X S A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X S A
      X A U
      hCong

  have hCycle :
      HilbertAngleLess Geo
        X S A
        X S A :=
    hilbert_angleLess_transport_right
      Geo
      X S A
      X A U
      X S A
      hLessU
      hXSA
      hU_S

  exact
    hilbert_angleLess_irrefl
      Geo
      X S A
      hCycle
/- END folded proof support: Crossing_circle_stage56_IV17_triangle_not_supplement_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage57_IV17_sameRay_secant_impossible_v2.lean -/
/-!
# Forder IV.17 -- stage 57, same-ray secant branch

Assume X,A,Y lie on one circle, T and Y are on opposite sides of
the chord AX, and

  angle XAT ~= angle XYA.

Suppose a second circle point S lies on the same ray AT from A.
Then S and T lie on the same side of AX, hence S and Y lie on
opposite sides of AX.

Forder IV.16 (opposite-side half) says that angle XSA is congruent
to a supplement of angle XYA. Since AS and AT are the same ray,
angle SAX is congruent to angle XYA. Transport of supplements then
makes angle XSA congruent to a supplement of angle XAS, contradicting
stage 56 / Euclid I.17.
-/

/--
The same-ray second-intersection branch in Forder IV.17 is impossible.
-/
theorem hilbert_IV17_sameRay_secant_impossible_stage57
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R X A Y T S : Geo.Point)
    (chord : Geo.Line)
    (hXA : Ne X A)
    (hXchord : H.OnLine X chord)
    (hAchord : H.OnLine A chord)
    (hXcircle : HilbertCircle Geo K R X)
    (hAcircle : HilbertCircle Geo K R A)
    (hYcircle : HilbertCircle Geo K R Y)
    (hScircle : HilbertCircle Geo K R S)
    (hOppTY : HilbertOppositeSide Geo T Y chord)
    (hAngle :
      Geo.AngleCongruent X A T X Y A)
    (hRayAST :
      HilbertSameRay Geo A S T) :
    False := by

  --------------------------------------------------------------------
  -- Carrier of the common ray AS = AT.
  --------------------------------------------------------------------

  rcases hRayAST.2.2.1 with
    ⟨lineAS, hAline, hSline, hTline⟩

  have hAS :
      Ne A S :=
    hRayAST.1.symm

  have hSA :
      Ne S A :=
    hRayAST.1

  have hXoffAS :
      Not (H.OnLine X lineAS) := by
    intro hXline

    have hEq :
        lineAS = chord :=
      HilbertPlaneIncidence.line_unique
        X A hXA
        lineAS chord
        hXline hAline
        hXchord hAchord

    have hTchord :
        H.OnLine T chord := by
      rw [← hEq]
      exact hTline

    exact hOppTY.1 hTchord

  --------------------------------------------------------------------
  -- S and T are on the same side of chord AX.
  --------------------------------------------------------------------

  have hRayASS :
      HilbertSameRay Geo A S S :=
    hilbert_sameRay_refl
      Geo A S hSA

  have hSameST :
      HilbertSameSide Geo S T chord :=
    hilbert_sameRay_points_sameSide
      Geo
      A S
      S T
      X
      lineAS chord
      hAline hSline
      hAchord hXchord
      hXoffAS
      hRayASS
      hRayAST

  --------------------------------------------------------------------
  -- T opposite Y and T same-side S imply S opposite Y.
  --------------------------------------------------------------------

  have hOppYT :
      HilbertOppositeSide Geo Y T chord :=
    hilbert_oppositeSide_symm
      Geo T Y chord hOppTY

  have hSameTS :
      HilbertSameSide Geo T S chord :=
    hilbert_sameSide_symm
      Geo S T chord hSameST

  have hOppYS :
      HilbertOppositeSide Geo Y S chord :=
    hilbert_oppositeSide_transport_right
      Geo
      Y T S
      chord
      hOppYT
      hSameTS

  have hOppSY :
      HilbertOppositeSide Geo S Y chord :=
    hilbert_oppositeSide_symm
      Geo Y S chord hOppYS

  --------------------------------------------------------------------
  -- IV.16 opposite-side:
  --
  -- XSA is congruent to a supplement UYA of XYA.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV16_opposite_complete_stage53
        Geo
        K R X A S Y
        chord
        hXA
        hXchord
        hAchord
        hXcircle
        hAcircle
        hScircle
        hYcircle
        hOppSY
    with
    ⟨U, hSuppY, hXSA_UYA⟩

  --------------------------------------------------------------------
  -- Since AS and AT are the same ray:
  --
  --   XAS ~= XAT ~= XYA,
  --
  -- hence SAX ~= XYA.
  --------------------------------------------------------------------

  have hXAS_eq_XAT :
      Geo.Angle X A S =
      Geo.Angle X A T :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      A X S T
      hRayAST

  have hXAS_XYA :
      Geo.AngleCongruent X A S X Y A := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢
    rw [hXAS_eq_XAT]
    exact hAngle

  have hSAX_XYA :
      Geo.AngleCongruent S A X X Y A :=
    (Geo.angle_congruent_reverse_first
      X A S
      X Y A).mp
      hXAS_XYA

  --------------------------------------------------------------------
  -- Construct the supplement of SAX by extending SA through A:
  --
  --   S-A-V.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        S A hSA
    with
    ⟨V, hSAV⟩

  have hRayAXX :
      HilbertSameRay Geo A X X :=
    hilbert_sameRay_refl
      Geo A X hXA

  have hSuppA :
      BookZeroSupplement Geo
        S A X
        X V :=
    ⟨hRayAXX, hSAV⟩

  --------------------------------------------------------------------
  -- Properness of the two base angles.
  --------------------------------------------------------------------

  have hSAX :
      Not (PrimCollinear Geo S A X) :=
    hilbert_not_collinear_of_off_line
      Geo
      S A X
      lineAS
      hSA
      hSline
      hAline
      hXoffAS

  have hYoff :
      Not (H.OnLine Y chord) :=
    hOppTY.2.1

  have hXYA :
      Not (PrimCollinear Geo X Y A) := by
    intro h

    have hXAY :
        PrimCollinear Geo X A Y :=
      PrimCollinearRotate
        Geo X Y A h

    exact
      (hilbert_not_collinear_of_off_line
        Geo
        X A Y
        chord
        hXA
        hXchord
        hAchord
        hYoff)
        hXAY

  --------------------------------------------------------------------
  -- Supplements of congruent angles SAX ~= XYA are congruent:
  --
  --   XAV ~= AYU.
  --------------------------------------------------------------------

  have hXAV_AYU :
      Geo.AngleCongruent X A V A Y U :=
    bookZero_43_supplements
      Geo
      S A X
      X V
      X Y A
      A U
      hSAX_XYA
      hSuppA
      hSuppY
      hSAX
      hXYA

  have hXAV_UYA :
      Geo.AngleCongruent X A V U Y A :=
    (Geo.angle_congruent_reverse_second
      X A V
      A Y U).mp
      hXAV_AYU

  --------------------------------------------------------------------
  -- IV.16 gave XSA ~= UYA, so XSA ~= XAV.
  --------------------------------------------------------------------

  have hUYA_XSA :
      Geo.AngleCongruent U Y A X S A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X S A
      U Y A
      hXSA_UYA

  have hXAV_XSA :
      Geo.AngleCongruent X A V X S A :=
    Geo.angle_congruent_transitivity
      X A V
      U Y A
      X S A
      hXAV_UYA
      hUYA_XSA

  have hXSA_XAV :
      Geo.AngleCongruent X S A X A V :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X A V
      X S A
      hXAV_XSA

  --------------------------------------------------------------------
  -- Contradiction with stage 56 (Euclid I.17).
  --------------------------------------------------------------------

  exact
    (hilbert_IV17_triangle_angle_not_supplement_stage56
      Geo
      X S A V
      (by
        intro h
        exact
          hSAX
            (PrimCollinearCycle
              Geo X S A h))
      hSAV)
      hXSA_XAV
/- END folded proof support: Crossing_circle_stage57_IV17_sameRay_secant_impossible_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage58_IV17_oppositeRay_secant_impossible_v3.lean -/
/-!
# Forder IV.17 -- stage 58, opposite-ray secant branch

Assume X,A,Y,S are concyclic, T and Y are on opposite sides of chord AX,
and

  angle XAT ~= angle XYA.

If the second circle point S satisfies

  S-A-T,

then T is an exterior point on the extension of SA. Since S and Y lie on
the same side of AX, Forder IV.16 (same-side half) gives

  angle XSA ~= angle XYA.

Together with the hypothesis this yields

  angle XSA ~= angle XAT,

contradicting the exterior-angle theorem for triangle XSA.
-/

/--
The S-A-T second-intersection branch in Forder IV.17 is impossible.
-/
theorem hilbert_IV17_oppositeRay_secant_impossible_stage58
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R X A Y T S : Geo.Point)
    (chord : Geo.Line)
    (hXA : Ne X A)
    (hXchord : H.OnLine X chord)
    (hAchord : H.OnLine A chord)
    (hXcircle : HilbertCircle Geo K R X)
    (hAcircle : HilbertCircle Geo K R A)
    (hYcircle : HilbertCircle Geo K R Y)
    (hScircle : HilbertCircle Geo K R S)
    (hOppTY : HilbertOppositeSide Geo T Y chord)
    (hAngle :
      Geo.AngleCongruent X A T X Y A)
    (hSAT :
      Geo.Between S A T) :
    False := by

  --------------------------------------------------------------------
  -- S is opposite T across chord AX or same-side with Y.
  --
  -- Because S-A-T and A lies on the chord, S and T are opposite
  -- sides of the chord.
  --------------------------------------------------------------------

  have hSATdata :=
    HilbertOrder.between_incidence
      S A T hSAT

  have hSA :
      Ne S A :=
    hSATdata.1

  have hAT :
      Ne A T :=
    hSATdata.2.1

  have hSATcol :
      PrimCollinear Geo S A T :=
    hSATdata.2.2.2.1

  have hSoff :
      Not (H.OnLine S chord) := by
    intro hSchord

    have hTchord :
        H.OnLine T chord :=
      hilbert_collinear_on_line
        Geo
        S A T
        chord
        hSA
        hSchord
        hAchord
        hSATcol

    exact hOppTY.1 hTchord

  have hToff :
      Not (H.OnLine T chord) :=
    hOppTY.1

  have hOppST :
      HilbertOppositeSide Geo S T chord :=
    ⟨hSoff,
      hToff,
      ⟨A, hSAT, hAchord⟩⟩

  have hOppTS :
      HilbertOppositeSide Geo T S chord :=
    hilbert_oppositeSide_symm
      Geo S T chord hOppST

  --------------------------------------------------------------------
  -- T is opposite both S and Y across chord XA.
  -- Stage 51 converts the two opposite-side relations into S,Y
  -- being on the same side.
  --------------------------------------------------------------------

  have hSameSY :
      HilbertSameSide Geo S Y chord :=
    hilbert_IV15_two_opposites_sameSide_stage51
      Geo
      T S Y X A
      chord
      hXA
      hXchord
      hAchord
      hOppTS
      hOppTY

  --------------------------------------------------------------------
  -- IV.16 same-side gives angle XSA ~= XYA.
  --------------------------------------------------------------------

  have hXS :
      Ne X S := by
    intro hXS
    subst S

    exact
      hSoff hXchord

  rcases
      HilbertPlaneIncidence.line_through
        X A hXA
    with
    ⟨lineXA, hXlineXA, hAlineXA⟩

  have hLineEq :
      lineXA = chord :=
    HilbertPlaneIncidence.line_unique
      X A hXA
      lineXA chord
      hXlineXA hAlineXA
      hXchord hAchord

  have hSameSY' :
      HilbertSameSide Geo S Y lineXA := by
    rw [hLineEq]
    exact hSameSY

  have hXSA_XYA :
      Geo.AngleCongruent X S A X Y A :=
    hilbert_forder_IV16_same_complete_stage54
      Geo
      K R
      X A S Y
      lineXA
      hXA
      hXlineXA
      hAlineXA
      hXcircle
      hAcircle
      hScircle
      hYcircle
      hSameSY'

  --------------------------------------------------------------------
  -- Hence XSA ~= XAT.
  --------------------------------------------------------------------

  have hXYA_XAT :
      Geo.AngleCongruent X Y A X A T :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X A T
      X Y A
      hAngle

  have hXSA_XAT :
      Geo.AngleCongruent X S A X A T :=
    Geo.angle_congruent_transitivity
      X S A
      X Y A
      X A T
      hXSA_XYA
      hXYA_XAT

  --------------------------------------------------------------------
  -- But XAT is the exterior angle of triangle XSA.
  --------------------------------------------------------------------

  have hXSA :
      Not (PrimCollinear Geo X S A) := by
    intro h

    rcases
        HilbertPlaneIncidence.line_through
          S A
          hSA
      with
      ⟨l, hSl, hAl⟩

    have hXl :
        H.OnLine X l :=
      hilbert_collinear_on_line
        Geo
        S A X
        l
        hSA
        hSl
        hAl
        (PrimCollinearCycle
          Geo X S A h)

    have hEq :
        l = chord :=
      HilbertPlaneIncidence.line_unique
        X A hXA
        l chord
        hXl hAl
        hXchord hAchord

    exact hSoff (hEq ▸ hSl)

  have hASX :
      Not (PrimCollinear Geo A S X) := by
    intro h
    exact
      hXSA
        (PrimCollinearSymm
          Geo A S X h)

  have hXAT_ASX :
      Geo.AngleCongruent X A T A S X :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A S X
      X A T
      ((Geo.angle_congruent_reverse_first
        X S A
        X A T).mp
        hXSA_XAT)

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      A S X T
      hASX
      hSAT)
      hXAT_ASX
/- END folded proof support: Crossing_circle_stage58_IV17_oppositeRay_secant_impossible_v3.lean -/

/- BEGIN folded proof support: Crossing_circle_stage59_IV17_complete_v4.lean -/
/-!
# Forder IV.17 -- stage 59, complete tangent converse

Forder IV.17:

If X,A,Y lie on a circle, T and Y are on opposite sides of chord AX,
and

  angle XAT ~= angle XYA,

then the line AT is tangent to the circle at A.

The proof follows Forder's secant/tangent dichotomy.

If AT is tangent, we are done.

Otherwise stage 4 supplies a second circle point S on line AT.
Relative to ray AT:

* if S lies on the same ray, stage 57 gives a contradiction;
* otherwise T-A-S, hence S-A-T after reversal, and stage 58 gives a
  contradiction.

Thus only the tangent alternative remains.
-/

/--
Complete Forder IV.17.
-/
theorem hilbert_forder_IV17_tangent_converse_stage59
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV17TangentConverse
      (Geo := Geo) := by

  intro K R X A Y T chord tangent
    hXA hXchord hAchord hAtangent hTtangent hTA
    hXcircle hAcircle hYcircle hOppTY hAngle

  --------------------------------------------------------------------
  -- The circle center differs from A.
  --------------------------------------------------------------------

  have hKX_KA :
      Geo.Congruent K X K A :=
    hilbert_congruent_transitivity
      Geo
      K X
      K R
      K A
      hXcircle
      (hilbert_congruent_symmetry
        Geo
        K A
        K R
        hAcircle)

  have hKA :
      Ne K A := by
    intro hKAeq
    subst K

    have hAX_AA :
        Geo.Congruent A X A A :=
      hKX_KA

    have hAXeq :
        A = X :=
      bookZero_nullSegment1
        Geo A X A hAX_AA

    exact hXA hAXeq.symm

  --------------------------------------------------------------------
  -- Analyze line AT through the circle point A.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_line_second_or_tangent_stage4
        Geo
        K R
        A T
        tangent
        hAcircle
        hKA
        hTA.symm
        hAtangent
        hTtangent
    with
    hSecant | hTangent

  --------------------------------------------------------------------
  -- Tangent alternative: exactly the conclusion.
  --------------------------------------------------------------------

  · rcases hSecant with
      ⟨S, hSA, hStangent, hScircle⟩

    by_cases hST :
        S = T

    --------------------------------------------------------------
    -- The second circle point is T itself.
    --------------------------------------------------------------

    · subst S

      have hRayATT :
          HilbertSameRay Geo A T T :=
        hilbert_sameRay_refl
          Geo A T hTA

      exact
        False.elim
          (hilbert_IV17_sameRay_secant_impossible_stage57
            Geo
            K R
            X A Y T T
            chord
            hXA
            hXchord
            hAchord
            hXcircle
            hAcircle
            hYcircle
            hScircle
            hOppTY
            hAngle
            hRayATT)

    --------------------------------------------------------------
    -- Distinct S,T: normalize their order on line AT.
    --------------------------------------------------------------

    · rcases
          hilbert_forder_IV19_secant_order_split_stage5
            Geo
            A T S
            tangent
            hTA.symm
            (by
              intro hTS
              exact hST hTS.symm)
            hSA.symm
            hAtangent
            hTtangent
            hStangent
        with
        hRayATS | hTAS

      ------------------------------------------------------------
      -- S lies on the same ray AT.
      ------------------------------------------------------------

      · exact
          False.elim
            (hilbert_IV17_sameRay_secant_impossible_stage57
              Geo
              K R
              X A Y T S
              chord
              hXA
              hXchord
              hAchord
              hXcircle
              hAcircle
              hYcircle
              hScircle
              hOppTY
              hAngle
              (hilbert_sameRay_symm
                Geo A T S hRayATS))

      ------------------------------------------------------------
      -- T-A-S, hence S-A-T.
      ------------------------------------------------------------

      · have hSAT :
            Geo.Between S A T :=
          (HilbertOrder.between_incidence
            T A S hTAS).2.2.2.2

        exact
          False.elim
            (hilbert_IV17_oppositeRay_secant_impossible_stage58
              Geo
              K R
              X A Y T S
              chord
              hXA
              hXchord
              hAchord
              hXcircle
              hAcircle
              hYcircle
              hScircle
              hOppTY
              hAngle
              hSAT)

  · exact hTangent
/- END folded proof support: Crossing_circle_stage59_IV17_complete_v4.lean -/

/- BEGIN folded proof support: HilbertPerpendicularUniqueness.lean -/
/-!
# Neutral uniqueness of a perpendicular direction

This is the planar Hilbert III.4 lemma needed by the circle tangent
development.  It is intentionally separated from Euclid XI.4 so that
planar clients do not import the full spatial XI.4 development.
-/

/--
If F-O-M and F-O-N are both nondegenerate right angles, then M,O,N
are collinear.
-/
theorem hilbert_two_right_angles_same_first_arm_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (F O M N : Geo.Point)
    (base : Geo.Line)
    (hFO : Ne F O)
    (hFbase : HilbertIncidence.OnLine F base)
    (hObase : HilbertIncidence.OnLine O base)
    (hFOM : Not (PrimCollinear Geo F O M))
    (hFON : Not (PrimCollinear Geo F O N))
    (hRightM : HilbertRightAngle Geo F O M)
    (hRightN : HilbertRightAngle Geo F O N) :
    PrimCollinear Geo M O N := by

  have hMoff :
      Not (HilbertIncidence.OnLine M base) := by
    intro hMbase
    exact hFOM
      ⟨base, hFbase, hObase, hMbase⟩

  have hNoff :
      Not (HilbertIncidence.OnLine N base) := by
    intro hNbase
    exact hFON
      ⟨base, hFbase, hObase, hNbase⟩

  by_cases hSameMN :
      HilbertSameSide Geo M N base

  · have hAngles :
        Geo.AngleCongruent F O M F O N :=
      hilbert_all_right_angles_congruent
        Geo
        F O M
        F O N
        hFOM hFON
        hRightM hRightN

    rcases
        hilbert_angle_unique_common_ray
          Geo
          F O M N
          base
          hFO
          hFbase hObase
          hMoff
          hSameMN
          hAngles with
      ⟨X, hRayXM, hRayXN⟩

    have hOX :
        Ne O X :=
      hRayXM.1.symm

    have hOXM :
        PrimCollinear Geo O X M :=
      hRayXM.2.2.1

    have hMOX :
        PrimCollinear Geo M O X :=
      PrimCollinearCycle
        Geo X M O
        (PrimCollinearCycle
          Geo O X M hOXM)

    have hOXN :
        PrimCollinear Geo O X N :=
      hRayXN.2.2.1

    exact
      hilbert_primCollinear_trans
        Geo
        M O X N
        hOX
        hMOX
        hOXN

  · have hOppMN :
        HilbertOppositeSide Geo M N base :=
      hilbert_oppositeSide_of_not_sameSide
        Geo
        M N base
        hMoff hNoff
        hSameMN

    have hMO : Ne M O := by
      intro hEq
      subst M
      exact hFOM
        ⟨base, hFbase, hObase, hObase⟩

    rcases
        HilbertOrder.between_extension
          (Geo := Geo)
          M O hMO with
      ⟨M', hMOM'⟩

    by_contra hMON

    have hSameNM' :
        HilbertSameSide Geo N M' base :=
      hilbert_sameSide_after_opposite_extension
        Geo
        M O N M'
        base
        hObase
        hMON
        hMOM'
        hOppMN

    have hM'off :
        Not (HilbertIncidence.OnLine M' base) :=
      hSameNM'.2.1

    have hFOM' :
        Not (PrimCollinear Geo F O M') :=
      hilbert_not_collinear_of_off_line
        Geo
        F O M'
        base
        hFO
        hFbase hObase
        hM'off

    have hMOF :
        Not (PrimCollinear Geo M O F) := by
      intro h
      exact hFOM
        (PrimCollinearSymm
          Geo M O F h)

    have hRightMOF :
        HilbertRightAngle Geo M O F :=
      hilbert_right_angle_swap_XI
        Geo
        F O M
        hFOM
        hRightM

    have hAngleMOF_FOM' :
        Geo.AngleCongruent M O F F O M' :=
      hilbert_right_angle_opposite_extension
        Geo
        M O F M'
        hMOF
        hRightMOF
        hMOM'

    have hRightM' :
        HilbertRightAngle Geo F O M' :=
      hilbert_right_angle_transport
        Geo
        M O F
        F O M'
        hMOF
        hFOM'
        hRightMOF
        hAngleMOF_FOM'

    have hSameM'N :
        HilbertSameSide Geo M' N base :=
      hilbert_sameSide_symm
        Geo N M' base hSameNM'

    have hAngles' :
        Geo.AngleCongruent F O M' F O N :=
      hilbert_all_right_angles_congruent
        Geo
        F O M'
        F O N
        hFOM' hFON
        hRightM' hRightN

    rcases
        hilbert_angle_unique_common_ray
          Geo
          F O M' N
          base
          hFO
          hFbase hObase
          hM'off
          hSameM'N
          hAngles' with
      ⟨X, hRayXM', hRayXN⟩

    have hOX :
        Ne O X :=
      hRayXM'.1.symm

    have hOXM' :
        PrimCollinear Geo O X M' :=
      hRayXM'.2.2.1

    have hM'OX :
        PrimCollinear Geo M' O X :=
      PrimCollinearCycle
        Geo X M' O
        (PrimCollinearCycle
          Geo O X M' hOXM')

    have hOXN :
        PrimCollinear Geo O X N :=
      hRayXN.2.2.1

    have hM'ON :
        PrimCollinear Geo M' O N :=
      hilbert_primCollinear_trans
        Geo
        M' O X N
        hOX
        hM'OX
        hOXN

    have hOM'N :
        PrimCollinear Geo O M' N :=
      PrimCollinearSwap
        Geo M' O N hM'ON

    have hMOM'Data :=
      HilbertOrder.between_incidence
        (Geo := Geo)
        M O M' hMOM'

    have hOM' : Ne O M' :=
      hMOM'Data.2.1

    have hMOM'col :
        PrimCollinear Geo M O M' :=
      hMOM'Data.2.2.2.1

    exact hMON
      (hilbert_primCollinear_trans
        Geo
        M O M' N
        hOM'
        hMOM'col
        hOM'N)
/- END folded proof support: HilbertPerpendicularUniqueness.lean -/

/- BEGIN folded proof support: Crossing_circle_stage60_tangent_carrier_unique_v4.lean -/
/-!
# Forder IV.18 preparation -- stage 60

Uniqueness of the tangent carrier at a fixed circle point.
-/

theorem hilbert_circle_tangent_carrier_unique_stage60
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K A : Geo.Point)
    (l m : Geo.Line)
    (hAl : H.OnLine A l)
    (hAm : H.OnLine A m)
    (hTanL :
      HilbertCircleTangentAtStage4
        (Geo := Geo) K A l)
    (hTanM :
      HilbertCircleTangentAtStage4
        (Geo := Geo) K A m) :
    l = m := by

  rcases hTanL with
    ⟨U, hUl, hUA, hUAK, hRightUAK⟩

  rcases hTanM with
    ⟨V, hVm, hVA, hVAK, hRightVAK⟩

  have hKAU :
      Not (PrimCollinear Geo K A U) := by
    intro h
    exact
      hUAK
        (PrimCollinearSymm
          Geo K A U h)

  have hKAV :
      Not (PrimCollinear Geo K A V) := by
    intro h
    exact
      hVAK
        (PrimCollinearSymm
          Geo K A V h)

  have hRightKAU :
      HilbertRightAngle Geo K A U :=
    hilbert_right_angle_swap_XI
      Geo
      U A K
      hUAK
      hRightUAK

  have hRightKAV :
      HilbertRightAngle Geo K A V :=
    hilbert_right_angle_swap_XI
      Geo
      V A K
      hVAK
      hRightVAK

  have hKA :
      Ne K A :=
    hilbert_noncollinear_ne_first
      Geo K A U hKAU

  rcases
      HilbertPlaneIncidence.line_through
        K A hKA
    with
    ⟨base, hKbase, hAbase⟩

  have hUAV :
      PrimCollinear Geo U A V :=
    hilbert_two_right_angles_same_first_arm_collinear
      Geo
      K A U V
      base
      hKA
      hKbase
      hAbase
      hKAU
      hKAV
      hRightKAU
      hRightKAV

  have hAU :
      Ne A U :=
    hUA.symm

  have hAUV :
      PrimCollinear Geo A U V :=
    PrimCollinearSwap
      Geo U A V hUAV

  have hVl :
      H.OnLine V l :=
    hilbert_collinear_on_line
      Geo
      A U V
      l
      hAU
      hAl
      hUl
      hAUV

  have hAV :
      Ne A V :=
    hVA.symm

  exact
    HilbertPlaneIncidence.line_unique
      A V hAV
      l m
      hAl hVl
      hAm hVm
/- END folded proof support: Crossing_circle_stage60_tangent_carrier_unique_v4.lean -/

/- BEGIN folded proof support: Crossing_circle_stage61_IV18_complete_v2.lean -/
/-!
# Forder IV.18 -- stage 61, complete tangent-chord theorem

Forder IV.18:

If AT is tangent to the circle XAY at A and T,Y lie on opposite
sides of chord AX, then

  angle XAT ~= angle XYA.

The proof follows Forder's route through IV.17 and Hilbert III.4.

Construct T' on the T-side of chord AX so that

  angle XAT' ~= angle XYA.

By IV.17 the line AT' is tangent at A.  Stage 60 identifies this
tangent carrier with the given tangent AT.  Since T and T' are on
the same side of AX, they lie on the same ray from A, so replacing
T' by T preserves the angle.
-/

theorem hilbert_forder_IV18_tangent_chord_stage61
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV18TangentChord
      (Geo := Geo) := by

  intro K R X A Y T chord tangent
    hXA hXchord hAchord
    hAtangent hTtangent hTA
    hXcircle hAcircle hYcircle
    hTan hOppTY

  --------------------------------------------------------------------
  -- T and Y are off chord AX.
  --------------------------------------------------------------------

  have hToff :
      Not (H.OnLine T chord) :=
    hOppTY.1

  have hYoff :
      Not (H.OnLine Y chord) :=
    hOppTY.2.1

  --------------------------------------------------------------------
  -- X,Y,A form a genuine angle.
  --------------------------------------------------------------------

  have hXAY :
      Not (PrimCollinear Geo X A Y) :=
    hilbert_not_collinear_of_off_line
      Geo
      X A Y
      chord
      hXA
      hXchord
      hAchord
      hYoff

  have hXYA :
      Not (PrimCollinear Geo X Y A) := by
    intro h
    exact
      hXAY
        (PrimCollinearRotate
          Geo X Y A h)

  --------------------------------------------------------------------
  -- Hilbert III.4:
  -- copy angle XYA at A on the side of chord AX containing T.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X Y A
        X A T
        hXYA
        hXA
        chord
        hXchord
        hAchord
        hToff
    with
    ⟨T', hT'TSame, hXYA_XAT', _hUnique⟩

  have hT'off :
      Not (H.OnLine T' chord) :=
    hT'TSame.1

  have hT'A :
      Ne T' A := by
    intro hEq
    subst T'
    exact hT'off hAchord

  have hAT' :
      Ne A T' :=
    hT'A.symm

  --------------------------------------------------------------------
  -- T' is opposite Y because T' is on the same side as T.
  --------------------------------------------------------------------

  have hTT'Same :
      HilbertSameSide Geo T T' chord :=
    hilbert_sameSide_symm
      Geo T' T chord hT'TSame

  have hOppYT :
      HilbertOppositeSide Geo Y T chord :=
    hilbert_oppositeSide_symm
      Geo T Y chord hOppTY

  have hOppYT' :
      HilbertOppositeSide Geo Y T' chord :=
    hilbert_oppositeSide_transport_right
      Geo
      Y T T'
      chord
      hOppYT
      hTT'Same

  have hOppT'Y :
      HilbertOppositeSide Geo T' Y chord :=
    hilbert_oppositeSide_symm
      Geo Y T' chord hOppYT'

  --------------------------------------------------------------------
  -- Carrier of the constructed ray AT'.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A T' hAT'
    with
    ⟨tangent', hAtangent', hT'tangent'⟩

  have hXAT'_XYA :
      Geo.AngleCongruent X A T' X Y A :=
    Geo.angle_congruent_symmetry
      X Y A
      X A T'
      hXYA_XAT'

  --------------------------------------------------------------------
  -- IV.17: the constructed line AT' is tangent.
  --------------------------------------------------------------------

  have hTan' :
      HilbertCircleTangentAtStage4
        (Geo := Geo) K A tangent' :=
    hilbert_forder_IV17_tangent_converse_stage59
      Geo
      K R X A Y T'
      chord tangent'
      hXA
      hXchord
      hAchord
      hAtangent'
      hT'tangent'
      hT'A
      hXcircle
      hAcircle
      hYcircle
      hOppT'Y
      hXAT'_XYA

  --------------------------------------------------------------------
  -- Uniqueness of tangent carrier.
  --------------------------------------------------------------------

  have hTangents :
      tangent = tangent' :=
    hilbert_circle_tangent_carrier_unique_stage60
      Geo
      K A
      tangent tangent'
      hAtangent
      hAtangent'
      hTan
      hTan'

  have hT'tangent :
      H.OnLine T' tangent := by
    rw [hTangents]
    exact hT'tangent'

  --------------------------------------------------------------------
  -- T and T' are on the same ray from A.
  --
  -- They are collinear on the tangent.  If A were between them,
  -- segment TT' would meet chord AX at A, contradicting same-side.
  --------------------------------------------------------------------

  have hATT' :
      PrimCollinear Geo A T T' :=
    ⟨tangent,
      hAtangent,
      hTtangent,
      hT'tangent⟩

  have hNotTAT' :
      Not (Geo.Between T A T') := by
    intro hTAT'

    have hOppTT' :
        HilbertOppositeSide Geo T T' chord :=
      ⟨hToff,
       hT'off,
       ⟨A, hTAT', hAchord⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo T T' chord hOppTT')
        hTT'Same

  have hRayATT' :
      HilbertSameRay Geo A T T' :=
    ⟨hTA,
     hT'A,
     hATT',
     hNotTAT'⟩

  --------------------------------------------------------------------
  -- Replace T' by T on the same ray.
  --------------------------------------------------------------------

  have hAngleXAT_XAT' :
      Geo.Angle X A T =
      Geo.Angle X A T' :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      A X T T'
      hRayATT'

  unfold Geometry.Geo.AngleCongruent
    at hXAT'_XYA ⊢

  rw [hAngleXAT_XAT']
  exact hXAT'_XYA
/- END folded proof support: Crossing_circle_stage61_IV18_complete_v2.lean -/

/- BEGIN folded proof support: Crossing_circle_stage62_transfer_complete_v2.lean -/
/-!
# Crossing rays transfer -- stage 62, complete

Stage 55 reduced the full crossing-rays transfer theorem to Forder IV.18.
Stage 61 now supplies IV.18 unconditionally, so the transfer closes with
no remaining hypotheses beyond the Euclidean Hilbert plane structure.
-/

theorem hilbert_crossing_rays_transfer_complete_stage62
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertCrossingRaysTransfer
      (Geo := Geo) := by
  exact
    hilbert_crossing_rays_transfer_of_IV18_stage55
      Geo
      (hilbert_forder_IV18_tangent_chord_stage61 Geo)
/- END folded proof support: Crossing_circle_stage62_transfer_complete_v2.lean -/


/-- Forder IV.12. -/
theorem hilbert_IV12_central_half
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV12CentralHalf (Geo := Geo) :=
  hilbert_forder_IV12_central_half_stage33 Geo

/-- Forder IV.12.1. -/
theorem hilbert_IV12_same_segment
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV12_1SameSegment (Geo := Geo) :=
  hilbert_forder_IV12_1_same_segment_stage34 Geo

/-- Forder IV.13. -/
theorem hilbert_IV13_diameter_right_angle
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV13DiameterRightAngle (Geo := Geo) :=
  hilbert_forder_IV13_diameter_right_angle_stage17 Geo

/-- Forder IV.14. -/
theorem hilbert_IV14_diameter_supplement
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists X : Geo.Point,
      BookZeroSupplement Geo B C D D X /\
      Geo.AngleCongruent B A D X C D :=
  hilbert_forder_IV14_diameter_supplement_stage43
    Geo K R A B C D diameter
    hAC hAdiam hCdiam hKdiam
    hAcircle hBcircle hCcircle hDcircle hOppBD

/-- Forder IV.15. -/
theorem hilbert_IV15_cyclic_supplement
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV15CyclicSupplement (Geo := Geo) :=
  hilbert_forder_IV15_complete_stage52 Geo

/-- Forder IV.16, opposite-side form. -/
theorem hilbert_IV16_opposite_side
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16OppositeSide (Geo := Geo) :=
  hilbert_forder_IV16_opposite_complete_stage53 Geo

/-- Forder IV.16, same-side form. -/
theorem hilbert_IV16_same_side
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16SameSide (Geo := Geo) :=
  hilbert_forder_IV16_same_complete_stage54 Geo

/-- Forder IV.17. -/
theorem hilbert_IV17_tangent_converse
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV17TangentConverse (Geo := Geo) :=
  hilbert_forder_IV17_tangent_converse_stage59 Geo

/-- Forder IV.18. -/
theorem hilbert_IV18_tangent_chord
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV18TangentChord (Geo := Geo) :=
  hilbert_forder_IV18_tangent_chord_stage61 Geo

/-- Forder IV.19. -/
theorem hilbert_IV19_circle_converse
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV19CircleConverse (Geo := Geo) :=
  hilbert_forder_IV19_circle_converse_stage6
    Geo
    (hilbert_forder_IV16_same_complete_stage54 Geo)
    (hilbert_forder_IV16_opposite_complete_stage53 Geo)
    (hilbert_forder_IV18_tangent_chord_stage61 Geo)

/-- Forder IV.20. -/
theorem hilbert_IV20_circle_converse
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV20CircleConverse (Geo := Geo) :=
  hilbert_forder_IV20_circle_converse_stage8
    Geo
    (hilbert_forder_IV16_same_complete_stage54 Geo)
    (hilbert_forder_IV16_opposite_complete_stage53 Geo)
    (hilbert_forder_IV18_tangent_chord_stage61 Geo)

/-- Synthetic secant/tangent dichotomy. -/
theorem hilbert_circle_line_second_or_tangent
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A D : Geo.Point)
    (line : Geo.Line)
    (hA : HilbertCircle Geo K R A)
    (hKA : Ne K A)
    (hAD : Ne A D)
    (hAline : H.OnLine A line)
    (hDline : H.OnLine D line) :
    (exists E : Geo.Point,
        Ne E A /\
        H.OnLine E line /\
        HilbertCircle Geo K R E)
    \/
    HilbertCircleTangentAt (Geo := Geo) K A line :=
  hilbert_circle_line_second_or_tangent_stage4
    Geo K R A D line hA hKA hAD hAline hDline

/-- Uniqueness of the tangent carrier. -/
theorem hilbert_circle_tangent_carrier_unique
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K A : Geo.Point)
    (l m : Geo.Line)
    (hAl : H.OnLine A l)
    (hAm : H.OnLine A m)
    (hTanL : HilbertCircleTangentAt (Geo := Geo) K A l)
    (hTanM : HilbertCircleTangentAt (Geo := Geo) K A m) :
    l = m :=
  hilbert_circle_tangent_carrier_unique_stage60
    Geo K A l m hAl hAm hTanL hTanM

/-- Completed crossing-rays transfer. -/
theorem hilbert_crossing_rays_transfer
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertCrossingRaysTransfer (Geo := Geo) :=
  hilbert_crossing_rays_transfer_complete_stage62 Geo


end Geometry

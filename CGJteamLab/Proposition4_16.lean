import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_12
import CGJteamLab.Proposition4_13
import CGJteamLab.Proposition4_15

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.16

Production module for Book IV proposition 16 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_IV16_opposite_of_IV15_stage13
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

private theorem hilbert_forder_IV16_same_of_IV12_1_IV13_IV15_stage15
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
          hilbert_circle_antipode
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

private theorem hilbert_forder_IV16_opposite_complete_stage53
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16OppositeSide
      (Geo := Geo) := by

  exact
    hilbert_forder_IV16_opposite_of_IV15_stage13
      Geo
      (hilbert_IV15_cyclic_supplement
        Geo)

private theorem hilbert_forder_IV16_same_complete_stage54
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16SameSide
      (Geo := Geo) := by

  exact
    hilbert_forder_IV16_same_of_IV12_1_IV13_IV15_stage15
      Geo
      (hilbert_IV12_same_segment
        Geo)
      (hilbert_IV13_diameter_right_angle
        Geo)
      (hilbert_IV15_cyclic_supplement
        Geo)

theorem hilbert_IV16_opposite_side
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16OppositeSide (Geo := Geo) :=
  hilbert_forder_IV16_opposite_complete_stage53 Geo

theorem hilbert_IV16_same_side
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV16SameSide (Geo := Geo) :=
  hilbert_forder_IV16_same_complete_stage54 Geo

end Geometry

import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_12
import CGJteamLab.Proposition4_13
import CGJteamLab.Proposition4_14

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.15

Production module for Book IV proposition 15 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_IV15_center_on_diagonal_stage44
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
    hilbert_IV13_diameter_right_angle
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
    hilbert_IV13_diameter_right_angle
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

private theorem hilbert_IV15_antipode_opposite_diagonal_stage45
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

private theorem hilbert_IV15_diameter_inner_point_stage46
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

private theorem hilbert_IV15_chord_exterior_farther_left_stage47
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

private theorem hilbert_IV15_chord_exterior_farther_right_stage47
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

private theorem hilbert_IV15_chord_opposite_diameter_stage48
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
        hilbert_circle_center_ne_point_of_two_distinct
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
        hilbert_circle_center_ne_point_of_two_distinct
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
        hilbert_circle_center_midpoint_of_chord
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
        hilbert_sameRay_beyond_common_middle
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
        hilbert_circle_center_midpoint_of_chord
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
        hilbert_sameRay_beyond_common_middle
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

private theorem hilbert_forder_IV15_sameSide_CK_stage50
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
      hilbert_circle_antipode
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
      hilbert_IV14_diameter_supplement
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
    hilbert_oppositeSide_tail_sameSide
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
    hilbert_IV12_same_segment
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

private theorem hilbert_forder_IV15_complete_stage52
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
        hilbert_two_opposites_sameSide_with_carrier
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

theorem hilbert_IV15_cyclic_supplement
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV15CyclicSupplement (Geo := Geo) :=
  hilbert_forder_IV15_complete_stage52 Geo

end Geometry

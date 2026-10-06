import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_13

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.14

Production module for Book IV proposition 14 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_diameter_right_decomposition_stage36
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
    hilbert_IV13_diameter_right_angle
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

private theorem hilbert_forder_IV14_diameter_rays_inside_stage38
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
      hilbert_circle_diameter_chord_intersection_inside
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

private theorem hilbert_forder_IV14_prescribed_perpendicular_stage39
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
    hilbert_IV13_diameter_right_angle
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

private theorem hilbert_forder_IV14_perpendicular_inside_supplement_stage40
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
    hilbert_IV13_diameter_right_angle
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
    hilbert_IV13_diameter_right_angle
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
        hilbert_sameRay_beyond_common_middle
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
    hilbert_angleDecomposition_nested_parent_divider
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

private theorem hilbert_forder_IV14_first_component_stage41
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
    hilbert_IV13_diameter_right_angle
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

private theorem hilbert_forder_IV14_second_component_stage42
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
    hilbert_IV13_diameter_right_angle
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

private theorem hilbert_forder_IV14_diameter_supplement_stage43
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

end Geometry

import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_16
import CGJteamLab.Proposition4_18
import CGJteamLab.Proposition4_19

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.20

Production module for Book IV proposition 20 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_IV20_secant_sameRay_stage7
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
    hilbert_equal_angles_same_secant_unique
      Geo
      C E B D
      hCED
      hRayCEB
      hCED_CBD

private theorem hilbert_forder_IV20_secant_oppositeRay_impossible_stage7
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
    hilbert_two_oppositeSides_sameSide
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

private theorem hilbert_forder_IV20_tangent_impossible_stage7
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
      HilbertCircleTangentAt
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

private theorem hilbert_forder_IV20_circle_converse_stage8
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
        hilbert_circle_line_second_or_tangent
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
          hilbert_secant_ray_order_split
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

theorem hilbert_IV20_circle_converse
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV20CircleConverse (Geo := Geo) :=
  hilbert_forder_IV20_circle_converse_stage8
    Geo
    (hilbert_IV16_same_side Geo)
    (hilbert_IV16_opposite_side Geo)
    (hilbert_IV18_tangent_chord Geo)

private theorem hilbert_crossing_chords_concyclic_stage9
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
    hilbert_IV19_circle_converse_of_IV16_IV18
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
    hilbert_crossing_chords_concyclic_of_forder
      Geo
      hIV19
      hIV20
      O A C B D
      hAOB
      hRayAC
      hRayBD
      hAngle

private theorem hilbert_crossing_rays_transfer_stage11
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
        hilbert_crossing_angle_at_O
          Geo
          O A A B D
          hRayAA
          hRayBD

      exact
        hilbert_AA_third_angle
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
        hilbert_crossing_chords_angle_nondegenerate
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

private theorem hilbert_crossing_rays_transfer_of_IV18_stage55
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
      (hilbert_IV16_same_side
        Geo)
      (hilbert_IV16_opposite_side
        Geo)
      hIV18

private theorem hilbert_crossing_rays_transfer_complete_stage62
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertCrossingRaysTransfer
      (Geo := Geo) := by
  exact
    hilbert_crossing_rays_transfer_of_IV18_stage55
      Geo
      (hilbert_IV18_tangent_chord Geo)

theorem hilbert_crossing_rays_transfer
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertCrossingRaysTransfer (Geo := Geo) :=
  hilbert_crossing_rays_transfer_complete_stage62 Geo

end Geometry

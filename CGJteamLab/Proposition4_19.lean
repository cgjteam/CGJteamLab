import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_16
import CGJteamLab.Proposition4_18

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.19

Production module for Book IV proposition 19 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_IV19_secant_sameRay_stage5
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
    hilbert_equal_angles_same_secant_unique
      Geo
      A E D B
      hAEB
      hRayAED
      hAEB_ADB

private theorem hilbert_forder_IV19_secant_oppositeRay_impossible_stage5
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
    hilbert_oppositeRay_gives_oppositeSide
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

private theorem hilbert_forder_IV19_tangent_impossible_stage5
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
      HilbertCircleTangentAt
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

theorem hilbert_IV19_circle_converse_of_IV16_IV18
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

theorem hilbert_IV19_circle_converse
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV19CircleConverse (Geo := Geo) :=
  hilbert_IV19_circle_converse_of_IV16_IV18
    Geo
    (hilbert_IV16_same_side Geo)
    (hilbert_IV16_opposite_side Geo)
    (hilbert_IV18_tangent_chord Geo)

end Geometry

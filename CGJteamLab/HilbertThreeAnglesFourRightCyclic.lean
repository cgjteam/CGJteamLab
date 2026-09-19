import CGJteamLab.HilbertThreeAnglesFourRight
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.HilbertBookZero

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/--
Cyclic setup for the synthetic three-angle bound.

The definition stores supplements of the first two angles:

    B - O - X,
    D - P - Y,

together with

    angle AOX + angle CPY > angle EQF.

For cyclic use we also construct Z beyond Q on the line FQ, so that
EQZ is the supplement of EQF.

No cyclic inequality is asserted yet; this theorem only packages the
three supplement witnesses in one configuration.
-/
theorem hilbertThreeAnglesLessThanFourRightAngles_cyclic_setup
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists X Y Z : Geo.Point,
      Geo.Between B O X /\
      Geo.Between D P Y /\
      Geo.Between F Q Z /\
      Not (PrimCollinear Geo A O X) /\
      Not (PrimCollinear Geo C P Y) /\
      Not (PrimCollinear Geo E Q Z) /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O X
        C P Y
        E Q F := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  rcases h.2.2.2 with
    ⟨X, Y, hBOX, hDPY, hCompare⟩

  have hFQE :
      Not (PrimCollinear Geo F Q E) := by
    intro hcol
    exact
      hEQF
        (PrimCollinearSymm
          Geo F Q E hcol)

  have hFQ :
      F ≠ Q :=
    hilbert_noncollinear_ne_first
      Geo F Q E hFQE

  rcases
      HilbertOrder.between_extension
        F Q hFQ
    with
    ⟨Z, hFQZ⟩

  have hBOXdata :=
    HilbertOrder.between_incidence
      B O X hBOX

  have hOX :
      O ≠ X :=
    hBOXdata.2.1

  have hBOXcol :
      PrimCollinear Geo B O X :=
    hBOXdata.2.2.2.1

  have hOXB :
      PrimCollinear Geo O X B :=
    PrimCollinearCycle
      Geo B O X hBOXcol

  have hAOX :
      Not (PrimCollinear Geo A O X) := by
    intro hcol

    have hAOBcol :
        PrimCollinear Geo A O B :=
      hilbert_primCollinear_trans
        Geo
        A O X B
        hOX
        hcol
        hOXB

    exact hAOB hAOBcol

  have hDPYdata :=
    HilbertOrder.between_incidence
      D P Y hDPY

  have hPY :
      P ≠ Y :=
    hDPYdata.2.1

  have hDPYcol :
      PrimCollinear Geo D P Y :=
    hDPYdata.2.2.2.1

  have hPYD :
      PrimCollinear Geo P Y D :=
    PrimCollinearCycle
      Geo D P Y hDPYcol

  have hCPY :
      Not (PrimCollinear Geo C P Y) := by
    intro hcol

    have hCPDcol :
        PrimCollinear Geo C P D :=
      hilbert_primCollinear_trans
        Geo
        C P Y D
        hPY
        hcol
        hPYD

    exact hCPD hCPDcol

  have hFQZdata :=
    HilbertOrder.between_incidence
      F Q Z hFQZ

  have hQZ :
      Q ≠ Z :=
    hFQZdata.2.1

  have hFQZcol :
      PrimCollinear Geo F Q Z :=
    hFQZdata.2.2.2.1

  have hQZF :
      PrimCollinear Geo Q Z F :=
    PrimCollinearCycle
      Geo F Q Z hFQZcol

  have hEQZ :
      Not (PrimCollinear Geo E Q Z) := by
    intro hcol

    have hEQFcol :
        PrimCollinear Geo E Q F :=
      hilbert_primCollinear_trans
        Geo
        E Q Z F
        hQZ
        hcol
        hQZF

    exact hEQF hEQFcol

  exact
    ⟨X, Y, Z,
      hBOX,
      hDPY,
      hFQZ,
      hAOX,
      hCPY,
      hEQZ,
      hCompare⟩

/--
If PW is an interior ray of angle CPD, and Y and Z are chosen on the
opposite rays to PD and PW respectively, then PY is an interior ray of
angle CPZ.

This is the plane-separation core needed for reversal of order under
supplementation.
-/
theorem hilbert_opposite_extensions_reverse_interior
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D W Y Z : Geo.Point)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hInsideW :
      HilbertRayMeetsSegment Geo P W C D)
    (hDPY : Geo.Between D P Y)
    (hWPZ : Geo.Between W P Z) :
    HilbertRayMeetsSegment Geo P Y C Z := by

  --------------------------------------------------------------------
  -- The reversed angle DPC and the fact that PW is also interior
  -- when the crossed segment CD is read in the opposite direction.
  --------------------------------------------------------------------

  have hDPC :
      Not (PrimCollinear Geo D P C) := by
    intro h
    exact hCPD
      (PrimCollinearSymm Geo D P C h)

  have hInsideWrev :
      HilbertRayMeetsSegment Geo P W D C :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      P W C D
      hInsideW

  have hDPW :
      Not (PrimCollinear Geo D P W) :=
    (hilbert_interior_angle_less
      Geo
      P W D C
      hDPC
      hInsideWrev).1

  --------------------------------------------------------------------
  -- Supporting line PC.  Since PW is interior to DPC, W and D are
  -- on the same side of PC.
  --------------------------------------------------------------------

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact hCPD
      (PrimCollinearSwap Geo P C D h)

  have hPC : Ne P C := by
    exact
      hilbert_noncollinear_ne_first
        Geo P C D hPCD

  rcases
      HilbertPlaneIncidence.line_through
        P C hPC
    with
    ⟨base, hPbase, hCbase⟩

  have hWDSame :
      HilbertSameSide Geo W D base :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      P W D C
      base
      hPbase
      hCbase
      hDPC
      hInsideWrev

  have hWoff :
      Not (HilbertIncidence.OnLine W base) :=
    hWDSame.1

  have hDoff :
      Not (HilbertIncidence.OnLine D base) :=
    hWDSame.2.1

  --------------------------------------------------------------------
  -- Y and Z are off PC.  Their opposite-side certificates use P as
  -- the crossing point.
  --------------------------------------------------------------------

  have hDPYdata :=
    HilbertOrder.between_incidence D P Y hDPY

  have hPY : Ne P Y :=
    hDPYdata.2.1

  have hDPYcol :
      PrimCollinear Geo D P Y :=
    hDPYdata.2.2.2.1

  have hPYD :
      PrimCollinear Geo P Y D :=
    PrimCollinearCycle
      Geo D P Y hDPYcol

  have hYoff :
      Not (HilbertIncidence.OnLine Y base) := by
    intro hYbase

    have hDbase :
        HilbertIncidence.OnLine D base :=
      hilbert_collinear_on_line
        Geo
        P Y D
        base
        hPY
        hPbase
        hYbase
        hPYD

    exact hDoff hDbase

  have hWPZdata :=
    HilbertOrder.between_incidence W P Z hWPZ

  have hPW : Ne P W :=
    hWPZdata.1.symm

  have hPZ : Ne P Z :=
    hWPZdata.2.1

  have hWZ : Ne W Z :=
    hWPZdata.2.2.1

  have hWPZcol :
      PrimCollinear Geo W P Z :=
    hWPZdata.2.2.2.1

  have hPZW :
      PrimCollinear Geo P Z W :=
    PrimCollinearCycle
      Geo W P Z hWPZcol

  have hZoff :
      Not (HilbertIncidence.OnLine Z base) := by
    intro hZbase

    have hWbase :
        HilbertIncidence.OnLine W base :=
      hilbert_collinear_on_line
        Geo
        P Z W
        base
        hPZ
        hPbase
        hZbase
        hPZW

    exact hWoff hWbase

  have hOppDY :
      HilbertOppositeSide Geo D Y base :=
    ⟨hDoff,
      hYoff,
      ⟨P, hDPY, hPbase⟩⟩

  have hDWSame :
      HilbertSameSide Geo D W base :=
    hilbert_sameSide_symm
      Geo W D base hWDSame

  have hOppYD :
      HilbertOppositeSide Geo Y D base :=
    hilbert_oppositeSide_symm
      Geo D Y base hOppDY

  have hOppYW :
      HilbertOppositeSide Geo Y W base :=
    hilbert_oppositeSide_transport_right
      Geo
      Y D W
      base
      hOppYD
      hDWSame

  have hOppWY :
      HilbertOppositeSide Geo W Y base :=
    hilbert_oppositeSide_symm
      Geo Y W base hOppYW

  have hOppWZ :
      HilbertOppositeSide Geo W Z base :=
    ⟨hWoff,
      hZoff,
      ⟨P, hWPZ, hPbase⟩⟩

  --------------------------------------------------------------------
  -- W,Y,Z form a genuine triangle.  Otherwise the two collinearities
  -- W-P-Z and D-P-Y would force D,P,W to be collinear.
  --------------------------------------------------------------------

  have hWYZ :
      Not (PrimCollinear Geo W Y Z) := by
    intro hWYZcol

    have hPWZ :
        PrimCollinear Geo P W Z :=
      PrimCollinearSwap
        Geo W P Z hWPZcol

    have hWZY :
        PrimCollinear Geo W Z Y :=
      PrimCollinearRotate
        Geo W Y Z hWYZcol

    have hPWY :
        PrimCollinear Geo P W Y :=
      hilbert_primCollinear_trans
        Geo
        P W Z Y
        hWZ
        hPWZ
        hWZY

    have hPYW :
        PrimCollinear Geo P Y W :=
      PrimCollinearRotate
        Geo P W Y hPWY

    have hDPWcol :
        PrimCollinear Geo D P W :=
      hilbert_primCollinear_trans
        Geo
        D P Y W
        hPY
        hDPYcol
        hPYW

    exact hDPW hDPWcol

  --------------------------------------------------------------------
  -- W is opposite to both Y and Z with respect to PC.  Therefore
  -- Y and Z lie in the same half-plane: the line PC enters triangle
  -- WYZ through WY and WZ, hence cannot also meet YZ.
  --------------------------------------------------------------------

  rcases hOppWY.2.2 with
    ⟨K0, hWK0Y, hK0base⟩

  have hNoMeetYZ :
      Not (HilbertSegmentMeetsLine Geo Y Z base) :=
    hilbert_line_avoids_third_triangle_side
      Geo
      W Y Z
      K0 P
      base
      hWYZ
      hWK0Y
      hWPZ
      hK0base
      hPbase

  have hYZStep :
      HilbertSameSideStep Geo Y Z base :=
    ⟨hYoff, hZoff, hNoMeetYZ⟩

  have hYZSame :
      HilbertSameSide Geo Y Z base :=
    ⟨hYoff,
      hZoff,
      Relation.ReflTransGen.single hYZStep⟩

  --------------------------------------------------------------------
  -- Y and Z are distinct rays from P.
  --------------------------------------------------------------------

  have hYPZ :
      Not (PrimCollinear Geo Y P Z) := by
    intro hYPZcol

    have hYPW :
        PrimCollinear Geo Y P W :=
      hilbert_primCollinear_trans
        Geo
        Y P Z W
        hPZ
        hYPZcol
        hPZW

    have hPYW :
        PrimCollinear Geo P Y W :=
      PrimCollinearSwap
        Geo Y P W hYPW

    have hDPWcol :
        PrimCollinear Geo D P W :=
      hilbert_primCollinear_trans
        Geo
        D P Y W
        hPY
        hDPYcol
        hPYW

    exact hDPW hDPWcol

  --------------------------------------------------------------------
  -- Order the two rays PY and PZ in the half-plane bounded by PC.
  --------------------------------------------------------------------

  rcases
      hilbert_sameSide_rays_order
        Geo
        P Y C Z
        base
        hPC
        hPbase
        hCbase
        hYoff
        hZoff
        hYZSame
        hYPZ
    with
    hYInside | hZInside

  · exact
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        P Y Z C
        hYInside

  ·
    ------------------------------------------------------------------
    -- The reverse order is impossible.  The carrier W-P-Z then
    -- intersects all three sides of triangle DCY:
    --   DC at the original interior witness H,
    --   DY at P,
    --   CY at the witness supplied by hZInside.
    ------------------------------------------------------------------

    rcases hInsideW with
      ⟨H, hCHD, hRayPWH⟩

    rcases hZInside with
      ⟨K, hYKC, hRayPZK⟩

    rcases
        HilbertPlaneIncidence.line_through
          W Z hWZ
      with
      ⟨lineWZ, hWline, hZline⟩

    have hPline :
        HilbertIncidence.OnLine P lineWZ :=
      hilbert_between_on_line
        Geo
        W P Z
        lineWZ
        hWline
        hZline
        hWPZ

    have hPWHcol :
        PrimCollinear Geo P W H :=
      hRayPWH.2.2.1

    have hHline :
        HilbertIncidence.OnLine H lineWZ :=
      hilbert_collinear_on_line
        Geo
        P W H
        lineWZ
        hPW
        hPline
        hWline
        hPWHcol

    have hPZKcol :
        PrimCollinear Geo P Z K :=
      hRayPZK.2.2.1

    have hKline :
        HilbertIncidence.OnLine K lineWZ :=
      hilbert_collinear_on_line
        Geo
        P Z K
        lineWZ
        hPZ
        hPline
        hZline
        hPZKcol

    have hDY : Ne D Y :=
      hDPYdata.2.2.1

    have hCDY :
        Not (PrimCollinear Geo C D Y) := by
      intro hCDYcol

      have hDYP :
          PrimCollinear Geo D Y P :=
        PrimCollinearRotate
          Geo D P Y hDPYcol

      have hCDP :
          PrimCollinear Geo C D P :=
        hilbert_primCollinear_trans
          Geo
          C D Y P
          hDY
          hCDYcol
          hDYP

      exact hCPD
        (PrimCollinearRotate
          Geo C D P hCDP)

    have hDCY :
        Not (PrimCollinear Geo D C Y) := by
      intro h
      exact hCDY
        (PrimCollinearSwap Geo D C Y h)

    have hDHC :
        Geo.Between D H C :=
      (HilbertOrder.between_incidence
        C H D hCHD).2.2.2.2

    have hCYSame :
        HilbertSameSide Geo C Y lineWZ :=
      hilbert_third_side_endpoints_sameSide
        Geo
        D C Y
        H P
        lineWZ
        hDCY
        hDHC
        hDPY
        hHline
        hPline

    have hCKY :
        Geo.Between C K Y :=
      (HilbertOrder.between_incidence
        Y K C hYKC).2.2.2.2

    have hOppCY :
        HilbertOppositeSide Geo C Y lineWZ :=
      ⟨hCYSame.1,
        hCYSame.2.1,
        ⟨K, hCKY, hKline⟩⟩

    exact
      False.elim
        ((hilbert_oppositeSide_not_sameSide
          Geo
          C Y lineWZ
          hOppCY)
          hCYSame)


/--
Strict angle order reverses under taking supplements.

If AOB < CPD, X is beyond O on ray OB, and Y is beyond P on ray PD,
then the supplementary angles satisfy

    CPY < AOX.
-/
theorem hilbert_angleLess_supplements_reverse
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D X Y : Geo.Point)
    (hLess :
      HilbertAngleLess Geo A O B C P D)
    (hBOX : Geo.Between B O X)
    (hDPY : Geo.Between D P Y) :
    HilbertAngleLess Geo C P Y A O X := by

  rcases hLess with
    ⟨hAOB,
      hCPD,
      W,
      hInsideW,
      hAOB_CPW⟩

  have hCPW :
      Not (PrimCollinear Geo C P W) :=
    (hilbert_interior_angle_less
      Geo
      P W C D
      hCPD
      hInsideW).1

  have hWP : Ne W P := by
    rcases hInsideW with
      ⟨H, _hCHD, hRayPWH⟩
    exact hRayPWH.1

  rcases
      HilbertOrder.between_extension
        W P hWP
    with
    ⟨Z, hWPZ⟩

  have hInsideY :
      HilbertRayMeetsSegment Geo P Y C Z :=
    hilbert_opposite_extensions_reverse_interior
      Geo
      C P D W Y Z
      hCPD
      hInsideW
      hDPY
      hWPZ

  --------------------------------------------------------------------
  -- Properness of the two supplementary angles.
  --------------------------------------------------------------------

  have hBOXdata :=
    HilbertOrder.between_incidence
      B O X hBOX

  have hOX : Ne O X :=
    hBOXdata.2.1

  have hBOXcol :
      PrimCollinear Geo B O X :=
    hBOXdata.2.2.2.1

  have hOXB :
      PrimCollinear Geo O X B :=
    PrimCollinearCycle
      Geo B O X hBOXcol

  have hAOX :
      Not (PrimCollinear Geo A O X) := by
    intro hAOXcol

    have hAOBcol :
        PrimCollinear Geo A O B :=
      hilbert_primCollinear_trans
        Geo
        A O X B
        hOX
        hAOXcol
        hOXB

    exact hAOB hAOBcol

  have hDPYdata :=
    HilbertOrder.between_incidence
      D P Y hDPY

  have hPY : Ne P Y :=
    hDPYdata.2.1

  have hDPYcol :
      PrimCollinear Geo D P Y :=
    hDPYdata.2.2.2.1

  have hPYD :
      PrimCollinear Geo P Y D :=
    PrimCollinearCycle
      Geo D P Y hDPYcol

  have hCPY :
      Not (PrimCollinear Geo C P Y) := by
    intro hCPYcol

    have hCPDcol :
        PrimCollinear Geo C P D :=
      hilbert_primCollinear_trans
        Geo
        C P Y D
        hPY
        hCPYcol
        hPYD

    exact hCPD hCPDcol

  have hWPZdata :=
    HilbertOrder.between_incidence
      W P Z hWPZ

  have hPZ : Ne P Z :=
    hWPZdata.2.1

  have hWPZcol :
      PrimCollinear Geo W P Z :=
    hWPZdata.2.2.2.1

  have hPZW :
      PrimCollinear Geo P Z W :=
    PrimCollinearCycle
      Geo W P Z hWPZcol

  have hCPZ :
      Not (PrimCollinear Geo C P Z) := by
    intro hCPZcol

    have hCPWcol :
        PrimCollinear Geo C P W :=
      hilbert_primCollinear_trans
        Geo
        C P Z W
        hPZ
        hCPZcol
        hPZW

    exact hCPW hCPWcol

  --------------------------------------------------------------------
  -- AOB ~= CPW.  Therefore their supplements AOX and CPZ are
  -- congruent by Book Zero #43.
  --------------------------------------------------------------------

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact hAOB
      (PrimCollinearSymm Geo B O A h)

  have hWPC :
      Not (PrimCollinear Geo W P C) := by
    intro h
    exact hCPW
      (PrimCollinearSymm Geo W P C h)

  have hBOA_WPC :
      Geo.AngleCongruent B O A W P C :=
    AngleCongruentReverse
      Geo
      A O B
      C P W
      hAOB_CPW

  have hAO : Ne A O :=
    hilbert_noncollinear_ne_first
      Geo A O B hAOB

  have hCP : Ne C P :=
    hilbert_noncollinear_ne_first
      Geo C P W hCPW

  have hSupp1 :
      BookZeroSupplement Geo B O A A X :=
    ⟨hilbert_sameRay_refl
        Geo O A hAO,
      hBOX⟩

  have hSupp2 :
      BookZeroSupplement Geo W P C C Z :=
    ⟨hilbert_sameRay_refl
        Geo P C hCP,
      hWPZ⟩

  have hAOX_CPZ :
      Geo.AngleCongruent A O X C P Z :=
    bookZero_43_supplements
      Geo
      B O A A X
      W P C C Z
      hBOA_WPC
      hSupp1
      hSupp2
      hBOA
      hWPC

  have hCPZ_AOX :
      Geo.AngleCongruent C P Z A O X :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O X
      C P Z
      hAOX_CPZ

  --------------------------------------------------------------------
  -- PY lies inside CPZ, so CPY < CPZ ~= AOX.
  --------------------------------------------------------------------

  have hCPYrefl :
      Geo.AngleCongruent C P Y C P Y :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      C P Y
      hCPY

  have hCPY_CPZ :
      HilbertAngleLess Geo C P Y C P Z :=
    hilbert_angleLess_intro
      Geo
      C P Y
      C P Z
      Y
      hCPY
      hCPZ
      hInsideY
      hCPYrefl

  exact
    hilbert_angleLess_transport_right
      Geo
      C P Y
      C P Z
      A O X
      hCPY_CPZ
      hAOX
      hCPZ_AOX

/--
For two interior rays of the same proper angle, strict order of the
left components forces the opposite strict order of the right
components.

This is the already-clean v49 lemma, isolated here only so that the
cyclic four-right-angle module does not depend on HilbertInterfaceXI.
-/
theorem hilbert_angleDecomposition_complement_order_reverse
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
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


/--
The synthetic four-right-angle bound is cyclic:

    (alpha,beta,gamma) < 4R
      ->
    (beta,gamma,alpha) < 4R.

The proof stays entirely inside the existing synthetic angle language.
-/
theorem hilbertThreeAnglesLessThanFourRightAngles_cycle
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    HilbertThreeAnglesLessThanFourRightAngles
      Geo
      C P D
      E Q F
      A O B := by

  rcases
      hilbertThreeAnglesLessThanFourRightAngles_cyclic_setup
        Geo
        A O B C P D E Q F
        h
    with
    ⟨X, Y, Z,
      hBOX,
      hDPY,
      hFQZ,
      hAOX,
      hCPY,
      hEQZ,
      hCompare⟩

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  --------------------------------------------------------------------
  -- Compare the new target AOB with the new first summand CPY.
  --------------------------------------------------------------------

  rcases
      angle_trichotomy
        Geo
        A O B
        C P Y
        hAOB
        hCPY
    with hEqTargetFirst | hTargetLessFirst | hFirstLessTarget

  ·
    ------------------------------------------------------------------
    -- AOB ~= CPY.
    ------------------------------------------------------------------

    have hCyclic :
        HilbertTwoAnglesGreaterThanAngle
          Geo
          C P Y
          E Q Z
          A O B :=
      hilbertTwoAnglesGreaterThanAngle_of_first_equal
        Geo
        C P Y
        E Q Z
        A O B
        hCPY
        hEQZ
        hAOB
        hEqTargetFirst

    exact
      hilbertThreeAnglesLessThanFourRightAngles_intro
        Geo
        C P D
        E Q F
        A O B
        Y Z
        hCPD
        hEQF
        hAOB
        hDPY
        hFQZ
        hCyclic

  ·
    ------------------------------------------------------------------
    -- AOB < CPY.
    ------------------------------------------------------------------

    have hCyclic :
        HilbertTwoAnglesGreaterThanAngle
          Geo
          C P Y
          E Q Z
          A O B :=
      hilbertTwoAnglesGreaterThanAngle_of_first_greater
        Geo
        C P Y
        E Q Z
        A O B
        hCPY
        hEQZ
        hAOB
        hTargetLessFirst

    exact
      hilbertThreeAnglesLessThanFourRightAngles_intro
        Geo
        C P D
        E Q F
        A O B
        Y Z
        hCPD
        hEQF
        hAOB
        hDPY
        hFQZ
        hCyclic

  ·
    ------------------------------------------------------------------
    -- CPY < AOB.  Let OV be the interior ray realizing this strict
    -- comparison:
    --
    --   CPY ~= AOV.
    --
    -- It remains to prove VOB < EQZ.
    ------------------------------------------------------------------

    rcases hFirstLessTarget with
      ⟨_hCPY,
        _hAOB,
        V,
        hInsideV,
        hCPY_AOV⟩

    have hInsideVrev :
        HilbertRayMeetsSegment Geo O V B A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        O V A B
        hInsideV

    have hBOA :
        Not (PrimCollinear Geo B O A) := by
      intro hcol
      exact hAOB
        (PrimCollinearSymm Geo B O A hcol)

    have hBOV_BOA :
        HilbertAngleLess Geo B O V B O A :=
      hilbert_interior_angle_less
        Geo
        O V B A
        hBOA
        hInsideVrev

    have hBOV :
        Not (PrimCollinear Geo B O V) :=
      hBOV_BOA.1

    have hVOB :
        Not (PrimCollinear Geo V O B) := by
      intro hcol
      exact hBOV
        (PrimCollinearSymm Geo V O B hcol)

    have hBOVrefl :
        Geo.AngleCongruent B O V B O V :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B O V

    have hBOV_VOB :
        Geo.AngleCongruent B O V V O B :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        V O B
        B O V
        ((Geometry.Geo.angle_congruent_reverse_first
          Geo
          B O V
          B O V).mp
          hBOVrefl)

    have hAOBrefl :
        Geo.AngleCongruent A O B A O B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A O B

    have hBOA_AOB :
        Geo.AngleCongruent B O A A O B :=
      (Geometry.Geo.angle_congruent_reverse_first
        Geo
        A O B
        A O B).mp
        hAOBrefl

    have hVOB_BOA :
        HilbertAngleLess Geo V O B B O A :=
      hilbert_angleLess_transport_left
        Geo
        B O V
        V O B
        B O A
        hBOV_BOA
        hVOB
        (Geometry.Geo.angle_congruent_symmetry
          Geo
          B O V
          V O B
          hBOV_VOB)

    have hVOB_AOB :
        HilbertAngleLess Geo V O B A O B :=
      hilbert_angleLess_transport_right
        Geo
        V O B
        B O A
        A O B
        hVOB_BOA
        hAOB
        hBOA_AOB

    ------------------------------------------------------------------
    -- Now split the original certificate
    --
    --   AOX + CPY > EQF
    --
    -- into its three defining cases.
    ------------------------------------------------------------------

    rcases hCompare with
      ⟨_hAOX0,
        _hCPY0,
        _hEQF0,
        hCore⟩

    have hXOB :
        Geo.Between X O B :=
      (HilbertOrder.between_incidence
        B O X hBOX).2.2.2.2

    rcases hCore with
      hEQF_lt_AOX | hEQF_eq_AOX | hDecomp

    ·
      ---------------------------------------------------------------
      -- EQF < AOX.
      --
      -- Supplements reverse strict order:
      --
      --   AOB < EQZ.
      --
      -- Since VOB < AOB, transitivity gives VOB < EQZ.
      ---------------------------------------------------------------

      have hAOB_EQZ :
          HilbertAngleLess Geo A O B E Q Z :=
        hilbert_angleLess_supplements_reverse
          Geo
          E Q F
          A O X
          Z B
          hEQF_lt_AOX
          hFQZ
          hXOB

      have hVOB_EQZ :
          HilbertAngleLess Geo V O B E Q Z :=
        hilbert_angleLess_trans
          Geo
          V O B
          A O B
          E Q Z
          hVOB_AOB
          hAOB_EQZ

      have hCyclic :
          HilbertTwoAnglesGreaterThanAngle
            Geo
            C P Y
            E Q Z
            A O B :=
        hilbertTwoAnglesGreaterThanAngle_of_decomposition
          Geo
          C P Y
          E Q Z
          A O B
          V
          hCPY
          hEQZ
          hAOB
          hInsideV
          hCPY_AOV
          hVOB_EQZ

      exact
        hilbertThreeAnglesLessThanFourRightAngles_intro
          Geo
          C P D
          E Q F
          A O B
          Y Z
          hCPD
          hEQF
          hAOB
          hDPY
          hFQZ
          hCyclic

    ·
      ---------------------------------------------------------------
      -- EQF ~= AOX.
      --
      -- Their supplements EQZ and AOB are congruent.  Hence
      -- VOB < AOB ~= EQZ.
      ---------------------------------------------------------------

      have hFQE_XOA :
          Geo.AngleCongruent F Q E X O A :=
        AngleCongruentReverse
          Geo
          E Q F
          A O X
          hEQF_eq_AOX

      have hEA :
          Ne E Q :=
        hilbert_noncollinear_ne_first
          Geo E Q F hEQF

      have hAA :
          Ne A O :=
        hilbert_noncollinear_ne_first
          Geo A O B hAOB

      have hSuppEQF :
          BookZeroSupplement Geo F Q E E Z :=
        ⟨hilbert_sameRay_refl
            Geo Q E hEA,
          hFQZ⟩

      have hSuppAOX :
          BookZeroSupplement Geo X O A A B :=
        ⟨hilbert_sameRay_refl
            Geo O A hAA,
          hXOB⟩

      have hEQZ_AOB :
          Geo.AngleCongruent E Q Z A O B :=
        bookZero_43_supplements
          Geo
          F Q E E Z
          X O A A B
          hFQE_XOA
          hSuppEQF
          hSuppAOX
          (by
            intro hcol
            exact hEQF
              (PrimCollinearSymm Geo F Q E hcol))
          (by
            intro hcol
            exact hAOX
              (PrimCollinearSymm Geo X O A hcol))

      have hAOB_EQZ :
          Geo.AngleCongruent A O B E Q Z :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          E Q Z
          A O B
          hEQZ_AOB

      have hVOB_EQZ :
          HilbertAngleLess Geo V O B E Q Z :=
        hilbert_angleLess_transport_right
          Geo
          V O B
          A O B
          E Q Z
          hVOB_AOB
          hEQZ
          hAOB_EQZ

      have hCyclic :
          HilbertTwoAnglesGreaterThanAngle
            Geo
            C P Y
            E Q Z
            A O B :=
        hilbertTwoAnglesGreaterThanAngle_of_decomposition
          Geo
          C P Y
          E Q Z
          A O B
          V
          hCPY
          hEQZ
          hAOB
          hInsideV
          hCPY_AOV
          hVOB_EQZ

      exact
        hilbertThreeAnglesLessThanFourRightAngles_intro
          Geo
          C P D
          E Q F
          A O B
          Y Z
          hCPD
          hEQF
          hAOB
          hDPY
          hFQZ
          hCyclic

    ·
      ---------------------------------------------------------------
      -- Decomposition case:
      --
      --   W inside EQF,
      --   AOX ~= EQW,
      --   WQF < CPY.
      --
      -- Extend W through Q to T.  Then Z is interior to EQT, and
      -- AOB ~= EQT by equality of supplements.
      ---------------------------------------------------------------

      rcases hDecomp with
        ⟨W,
          hInsideW,
          hAOX_EQW,
          hWQF_CPY⟩

      have hWQF :
          Not (PrimCollinear Geo W Q F) :=
        hWQF_CPY.1

      rcases hInsideW with
        ⟨H,
          hEHF,
          hRayQWH⟩

      have hWQ :
          Ne W Q :=
        hRayQWH.1

      have hInsideW0 :
          HilbertRayMeetsSegment Geo Q W E F :=
        ⟨H, hEHF, hRayQWH⟩

      rcases
          HilbertOrder.between_extension
            W Q hWQ
        with
        ⟨T, hWQT⟩

      have hInsideZ_EQT :
          HilbertRayMeetsSegment Geo Q Z E T :=
        hilbert_opposite_extensions_reverse_interior
          Geo
          E Q F W Z T
          hEQF
          hInsideW0
          hFQZ
          hWQT

      have hInsideZ_TQE :
          HilbertRayMeetsSegment Geo Q Z T E :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo
          Q Z E T
          hInsideZ_EQT

      have hXOA_WQE :
          Geo.AngleCongruent X O A W Q E :=
        AngleCongruentReverse
          Geo
          A O X
          E Q W
          hAOX_EQW

      have hAO :
          Ne A O :=
        hilbert_noncollinear_ne_first
          Geo A O B hAOB

      have hEQW :
          Not (PrimCollinear Geo E Q W) :=
        (hilbert_interior_angle_less
          Geo
          Q W E F
          hEQF
          hInsideW0).1

      have hQE :
          Ne E Q :=
        hilbert_noncollinear_ne_first
          Geo E Q W hEQW

      have hSuppAOX :
          BookZeroSupplement Geo X O A A B :=
        ⟨hilbert_sameRay_refl
            Geo O A hAO,
          hXOB⟩

      have hSuppEQW :
          BookZeroSupplement Geo W Q E E T :=
        ⟨hilbert_sameRay_refl
            Geo Q E hQE,
          hWQT⟩

      have hAOB_EQT :
          Geo.AngleCongruent A O B E Q T :=
        bookZero_43_supplements
          Geo
          X O A A B
          W Q E E T
          hXOA_WQE
          hSuppAOX
          hSuppEQW
          (by
            intro hcol
            exact hAOX
              (PrimCollinearSymm Geo X O A hcol))
          (by
            intro hcol
            exact hEQW
              (PrimCollinearSymm Geo W Q E hcol))

      have hEQT_AOB :
          Geo.AngleCongruent E Q T A O B :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          A O B
          E Q T
          hAOB_EQT

      have hTQE_AOB :
          Geo.AngleCongruent T Q E A O B :=
        (Geometry.Geo.angle_congruent_reverse_first
          Geo
          E Q T
          A O B).mp
          hEQT_AOB

      have hWQTdata :=
        HilbertOrder.between_incidence W Q T hWQT

      have hQT :
          Ne Q T :=
        hWQTdata.2.1

      have hWQTcol :
          PrimCollinear Geo W Q T :=
        hWQTdata.2.2.2.1

      have hQTW :
          PrimCollinear Geo Q T W :=
        PrimCollinearCycle
          Geo W Q T hWQTcol

      have hTQE :
          Not (PrimCollinear Geo T Q E) := by
        intro hTQEcol

        have hEQT :
            PrimCollinear Geo E Q T :=
          PrimCollinearSymm
            Geo T Q E hTQEcol

        have hEQWcol :
            PrimCollinear Geo E Q W :=
          hilbert_primCollinear_trans
            Geo
            E Q T W
            hQT
            hEQT
            hQTW

        exact hEQW hEQWcol

      ----------------------------------------------------------------
      -- Transport the reversed decomposition TQE = TQZ + ZQE into
      -- AOB.  This gives an interior ray U with
      --
      --   TQZ ~= AOU,
      --   EQZ ~= BOU.
      ----------------------------------------------------------------

      rcases
          hilbert_interior_subangle_transport_both
            Geo
            Q T E Z
            A O B
            hTQE
            hAOB
            hInsideZ_TQE
            hTQE_AOB
        with
        ⟨U,
          hInsideU,
          hPartsU⟩

      have hEQZ_BOU :
          Geo.AngleCongruent E Q Z B O U :=
        hPartsU.1

      have hTQZ_AOU :
          Geo.AngleCongruent T Q Z A O U :=
        hPartsU.2

      have hAOU :
          Not (PrimCollinear Geo A O U) :=
        (hilbert_interior_angle_less
          Geo
          O U A B
          hAOB
          hInsideU).1

      have hAOV :
          Not (PrimCollinear Geo A O V) :=
        (hilbert_interior_angle_less
          Geo
          O V A B
          hAOB
          hInsideV).1

      ----------------------------------------------------------------
      -- WQF and TQZ are vertical angles.
      ----------------------------------------------------------------

      have hWQF_TQZ :
          Geo.AngleCongruent W Q F T Q Z :=
        VerticalAngles
          Geo
          W Q F
          T Z
          hWQT
          hFQZ
          hWQF

      have hTQZ :
          Not (PrimCollinear Geo T Q Z) :=
        (hilbert_interior_angle_less
          Geo
          Q Z T E
          hTQE
          hInsideZ_TQE).1

      have hTQZ_CPY :
          HilbertAngleLess Geo T Q Z C P Y :=
        hilbert_angleLess_transport_left
          Geo
          W Q F
          T Q Z
          C P Y
          hWQF_CPY
          hTQZ
          (Geometry.Geo.angle_congruent_symmetry
            Geo
            W Q F
            T Q Z
            hWQF_TQZ)

      have hTQZ_AOV :
          HilbertAngleLess Geo T Q Z A O V :=
        hilbert_angleLess_transport_right
          Geo
          T Q Z
          C P Y
          A O V
          hTQZ_CPY
          hAOV
          hCPY_AOV

      have hAOU_TQZ :
          Geo.AngleCongruent A O U T Q Z :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          T Q Z
          A O U
          hTQZ_AOU

      have hAOU_AOV :
          HilbertAngleLess Geo A O U A O V :=
        hilbert_angleLess_transport_left
          Geo
          T Q Z
          A O U
          A O V
          hTQZ_AOV
          hAOU
          hAOU_TQZ

      ----------------------------------------------------------------
      -- U and V are interior rays of the same whole angle AOB.
      -- Since AOU < AOV, complementary order reverses:
      --
      --   BOV < BOU.
      ----------------------------------------------------------------

      have hBOV_BOU :
          HilbertAngleLess Geo B O V B O U :=
        hilbert_angleDecomposition_complement_order_reverse
          Geo
          O A B
          U V
          hAOB
          hInsideU
          hInsideV
          hAOU_AOV

      have hBOU_EQZ :
          Geo.AngleCongruent B O U E Q Z :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          E Q Z
          B O U
          hEQZ_BOU

      have hBOV_EQZ :
          HilbertAngleLess Geo B O V E Q Z :=
        hilbert_angleLess_transport_right
          Geo
          B O V
          B O U
          E Q Z
          hBOV_BOU
          hEQZ
          hBOU_EQZ

      have hBOVrefl2 :
          Geo.AngleCongruent B O V B O V :=
        Geometry.Geo.angle_congruent_reflexive
          Geo B O V

      have hVOB_BOV :
          Geo.AngleCongruent V O B B O V :=
        (Geometry.Geo.angle_congruent_reverse_first
          Geo
          B O V
          B O V).mp
          hBOVrefl2

      have hVOB_EQZ :
          HilbertAngleLess Geo V O B E Q Z :=
        hilbert_angleLess_transport_left
          Geo
          B O V
          V O B
          E Q Z
          hBOV_EQZ
          hVOB
          hVOB_BOV

      have hCyclic :
          HilbertTwoAnglesGreaterThanAngle
            Geo
            C P Y
            E Q Z
            A O B :=
        hilbertTwoAnglesGreaterThanAngle_of_decomposition
          Geo
          C P Y
          E Q Z
          A O B
          V
          hCPY
          hEQZ
          hAOB
          hInsideV
          hCPY_AOV
          hVOB_EQZ

      exact
        hilbertThreeAnglesLessThanFourRightAngles_intro
          Geo
          C P D
          E Q F
          A O B
          Y Z
          hCPD
          hEQF
          hAOB
          hDPY
          hFQZ
          hCyclic

end Geometry

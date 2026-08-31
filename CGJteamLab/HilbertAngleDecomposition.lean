import CGJteamLab.HilbertInterface

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Permanent synthetic angle-decomposition calculus.
--
-- This module promotes the source-audited lemmas used by Euclid II.9.
-- It contains no numerical angle measure and no proposition-local axiom.
------------------------------------------------------------------------

/--
Reversing the endpoints of the crossed segment does not change
the fact that a ray meets its interior.
-/
theorem hilbert_angleDecomposition_ray_meets_segment_reverse
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O D X C : Geo.Point)
    (hInside :
      HilbertRayMeetsSegment Geo O D X C) :
    HilbertRayMeetsSegment Geo O D C X := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hCHX :
      Geo.Between C H X :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.2.2.2

  exact
    ⟨H, hCHX, hRayODH⟩


/--
An interior ray of angle XOC lies on the same side of the line OC
as the first boundary ray OX.

The supplied line `base` is the carrier OC.
-/
theorem hilbert_angleDecomposition_interior_ray_sameSide_first
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O D X C : Geo.Point)
    (base : Geo.Line)
    (hObase :
      HilbertIncidence.OnLine O base)
    (hCbase :
      HilbertIncidence.OnLine C base)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C) :
    HilbertSameSide Geo D X base := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hOC :
      O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo
      O C X
      (by
        intro h
        exact
          hXOC
            (PrimCollinearRotate
              Geo X C O
              (PrimCollinearSymm
                Geo O C X h)))

  have hXCO :
      Not (PrimCollinear Geo X C O) := by
    intro h
    exact
      hXOC
        (PrimCollinearRotate
          Geo X C O h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        X H O C
        hXHC
        hXCO
    with
    ⟨l,
      hOl,
      hCl,
      hXHsame_l⟩

  have hlbase :
      l = base :=
    HilbertPlaneIncidence.line_unique
      O C hOC
      l base
      hOl hCl
      hObase hCbase

  have hXHsame :
      HilbertSameSide Geo X H base := by
    rw [← hlbase]
    exact hXHsame_l

  rcases hRayODH.2.2.1 with
    ⟨rayLine,
      hOray,
      hDray,
      hHray⟩

  have hHC :
      H ≠ C :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.1

  have hCoff :
      Not (HilbertIncidence.OnLine C rayLine) := by

    intro hCray

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hHCX :
        PrimCollinear Geo H C X :=
      PrimCollinearCycle
        Geo X H C hXHCcol

    have hXray :
        HilbertIncidence.OnLine X rayLine :=
      hilbert_collinear_on_line
        Geo
        H C X
        rayLine
        hHC
        hHray
        hCray
        hHCX

    exact
      hXOC
        ⟨rayLine,
          hXray,
          hOray,
          hCray⟩

  have hDD :
      HilbertSameRay Geo O D D :=
    hilbert_sameRay_refl
      Geo O D hRayODH.1

  have hDHsame :
      HilbertSameSide Geo D H base :=
    hilbert_sameRay_points_sameSide
      Geo
      O D
      D H
      C
      rayLine base
      hOray
      hDray
      hObase
      hCbase
      hCoff
      hDD
      hRayODH

  have hHXsame :
      HilbertSameSide Geo H X base :=
    hilbert_sameSide_symm
      Geo X H base hXHsame

  exact
    hilbert_sameSide_trans
      Geo
      D H X
      base
      hDHsame
      hHXsame


/--
If angle XFA is strictly smaller than angle XFD, with A and D
on the same side of the base XF, then ray FA meets the open
segment XD.
-/
theorem hilbert_angleDecomposition_angle_less_ray_inside
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    HilbertRayMeetsSegment Geo F A X D := by

  rcases hLess with
    ⟨hXFA, hXFD, J, hInsideJ, hAngle⟩

  rcases hInsideJ with
    ⟨H, hXHD, hRayFJH⟩

  have hDHX :
      Geo.Between D H X :=
    (HilbertOrder.between_incidence
      X H D hXHD).2.2.2.2

  have hDXF :
      Not (PrimCollinear Geo D X F) := by
    intro h
    exact
      hXFD
        (PrimCollinearCycle
          Geo D X F h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        D H F X
        hDHX
        hDXF
    with
    ⟨lineFX,
      hFlineFX,
      hXlineFX,
      hDHSame_lineFX⟩

  have hLineEq :
      lineFX = base :=
    HilbertPlaneIncidence.line_unique
      F X hFX
      lineFX base
      hFlineFX hXlineFX
      hFbase hXbase

  have hDHSame :
      HilbertSameSide Geo D H base := by
    rw [← hLineEq]
    exact hDHSame_lineFX

  have hAHSame :
      HilbertSameSide Geo A H base :=
    hilbert_sameSide_trans
      Geo
      A D H
      base
      hSame
      hDHSame

  have hXFJ :
      Not (PrimCollinear Geo X F J) :=
    (hilbert_interior_angle_less
      Geo
      F J X D
      hXFD
      ⟨H, hXHD, hRayFJH⟩).1

  have hFJ :
      F ≠ J :=
    hRayFJH.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        F J hFJ
    with
    ⟨lineFJ,
      hFlineFJ,
      hJlineFJ⟩

  have hXoffFJ :
      Not (HilbertIncidence.OnLine X lineFJ) := by
    intro hXline
    exact
      hXFJ
        ⟨lineFJ,
          hXline,
          hFlineFJ,
          hJlineFJ⟩

  have hRayFJJ :
      HilbertSameRay Geo F J J :=
    hilbert_sameRay_refl
      Geo F J hFJ.symm

  have hJHSame :
      HilbertSameSide Geo J H base :=
    hilbert_sameRay_points_sameSide
      Geo
      F J
      J H
      X
      lineFJ base
      hFlineFJ
      hJlineFJ
      hFbase
      hXbase
      hXoffFJ
      hRayFJJ
      hRayFJH

  have hHJSame :
      HilbertSameSide Geo H J base :=
    hilbert_sameSide_symm
      Geo J H base hJHSame

  have hAJSame :
      HilbertSameSide Geo A J base :=
    hilbert_sameSide_trans
      Geo
      A H J
      base
      hAHSame
      hHJSame

  rcases
      hilbert_angle_unique_common_ray
        Geo
        X F A J
        base
        hFX.symm
        hXbase
        hFbase
        hAJSame.1
        hAJSame
        hAngle
    with
    ⟨Z,
      hRayZA,
      hRayZJ⟩

  have hRayAJ :
      HilbertSameRay Geo F A J :=
    hilbert_sameRay_of_common
      Geo
      F Z A J
      hRayZA
      hRayZJ

  have hRayJA :
      HilbertSameRay Geo F J A :=
    hilbert_sameRay_symm
      Geo
      F A J
      hRayAJ

  have hRayFAH :
      HilbertSameRay Geo F A H :=
    hilbert_sameRay_of_common
      Geo
      F J A H
      hRayJA
      hRayFJH

  exact
    ⟨H,
      hXHD,
      hRayFAH⟩

------------------------------------------------------------------------

/--
Two proper component angles of one decomposition cannot both be
strictly smaller than the corresponding component angles of another
decomposition of the same angle.

D and E are interior rays of angle XOC.

If

    angle XOD < angle XOE

and simultaneously

    angle COD < angle COE,

then the ray OD would cross both sides XE and CE. Together with
the original crossing of XC this contradicts plane separation/Pasch.
-/
theorem hilbert_angleDecomposition_two_component_less_impossible
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hLessFirst :
      HilbertAngleLess Geo
        X O D
        X O E)
    (hLessSecond :
      HilbertAngleLess Geo
        C O D
        C O E) :
    False := by

  --------------------------------------------------------------------
  -- The reversed angle COX.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- Supporting line OX.
  --------------------------------------------------------------------

  have hOXC :
      Not (PrimCollinear Geo O X C) := by
    intro h
    exact
      hXOC
        (PrimCollinearSwap
          Geo O X C h)

  have hOX :
      O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo O X C hOXC

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX
    with
    ⟨lineOX,
      hOlineOX,
      hXlineOX⟩

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

  have hECSameOX :
      HilbertSameSide Geo E C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideErev

  have hCESameOX :
      HilbertSameSide Geo C E lineOX :=
    hilbert_sameSide_symm
      Geo
      E C
      lineOX
      hECSameOX

  have hDESameOX :
      HilbertSameSide Geo D E lineOX :=
    hilbert_sameSide_trans
      Geo
      D C E
      lineOX
      hDCSameOX
      hCESameOX

  --------------------------------------------------------------------
  -- Supporting line OC.
  --------------------------------------------------------------------

  have hOCX :
      Not (PrimCollinear Geo O C X) := by
    intro h
    exact
      hXOC
        (PrimCollinearRotate
          Geo
          X C O
          (PrimCollinearSymm
            Geo O C X h))

  have hOC :
      O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo O C X hOCX

  rcases
      HilbertPlaneIncidence.line_through
        O C hOC
    with
    ⟨lineOC,
      hOlineOC,
      hClineOC⟩

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

  have hXESameOC :
      HilbertSameSide Geo X E lineOC :=
    hilbert_sameSide_symm
      Geo
      E X
      lineOC
      hEXSameOC

  have hDESameOC :
      HilbertSameSide Geo D E lineOC :=
    hilbert_sameSide_trans
      Geo
      D X E
      lineOC
      hDXSameOC
      hXESameOC

  --------------------------------------------------------------------
  -- Strict inequalities place OD inside both XOE and COE.
  --------------------------------------------------------------------

  have hInsideFirst :
      HilbertRayMeetsSegment Geo O D X E :=
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      D E O X
      lineOX
      hOlineOX
      hXlineOX
      hOX
      hDESameOX
      hLessFirst

  have hInsideSecond :
      HilbertRayMeetsSegment Geo O D C E :=
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      D E O C
      lineOC
      hOlineOC
      hClineOC
      hOC
      hDESameOC
      hLessSecond

  --------------------------------------------------------------------
  -- Carrier OD and its original crossing of XC.
  --------------------------------------------------------------------

  rcases hInsideD with
    ⟨H0,
      hXH0C,
      hRayODH0⟩

  have hOD :
      O ≠ D :=
    hRayODH0.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O D hOD
    with
    ⟨lineOD,
      hOlineOD,
      hDlineOD⟩

  have hH0lineOD :
      HilbertIncidence.OnLine H0 lineOD :=
    hilbert_collinear_on_line
      Geo
      O D H0
      lineOD
      hOD
      hOlineOD
      hDlineOD
      hRayODH0.2.2.1

  --------------------------------------------------------------------
  -- Split according to whether E happens to lie on XC.
  --------------------------------------------------------------------

  by_cases hEXC :
      PrimCollinear Geo E X C

  --------------------------------------------------------------------
  -- Degenerate representative: E lies on XC.
  --------------------------------------------------------------------

  · rcases hInsideE with
      ⟨H,
        hXHC,
        hRayOEH⟩

    have hXC :
        X ≠ C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.1

    rcases
        HilbertPlaneIncidence.line_through
          X C hXC
      with
      ⟨lineXC,
        hXlineXC,
        hClineXC⟩

    have hHlineXC :
        HilbertIncidence.OnLine H lineXC :=
      hilbert_between_on_line
        Geo
        X H C
        lineXC
        hXlineXC
        hClineXC
        hXHC

    have hXCE :
        PrimCollinear Geo X C E :=
      PrimCollinearCycle
        Geo E X C hEXC

    have hElineXC :
        HilbertIncidence.OnLine E lineXC :=
      hilbert_collinear_on_line
        Geo
        X C E
        lineXC
        hXC
        hXlineXC
        hClineXC
        hXCE

    have hOE :
        O ≠ E :=
      hRayOEH.1.symm

    rcases
        HilbertPlaneIncidence.line_through
          O E hOE
      with
      ⟨lineOE,
        hOlineOE,
        hElineOE⟩

    have hHlineOE :
        HilbertIncidence.OnLine H lineOE :=
      hilbert_collinear_on_line
        Geo
        O E H
        lineOE
        hOE
        hOlineOE
        hElineOE
        hRayOEH.2.2.1

    have hLinesXCOE :
        lineXC ≠ lineOE := by

      intro hEq

      have hOlineXC :
          HilbertIncidence.OnLine O lineXC := by
        rw [hEq]
        exact hOlineOE

      exact
        hXOC
          ⟨lineXC,
            hXlineXC,
            hOlineXC,
            hClineXC⟩

    have hHE :
        H = E := by

      by_contra hHE

      have hEq :
          lineXC = lineOE :=
        HilbertPlaneIncidence.line_unique
          E H
          (Ne.symm hHE)
          lineXC lineOE
          hElineXC hHlineXC
          hElineOE hHlineOE

      exact hLinesXCOE hEq

    have hXEC :
        Geo.Between X E C := by
      simpa [hHE] using hXHC

    rcases hInsideFirst with
      ⟨H1,
        hXH1E,
        hRayODH1⟩

    rcases hInsideSecond with
      ⟨H2,
        hCH2E,
        hRayODH2⟩

    have hH1lineOD :
        HilbertIncidence.OnLine H1 lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H1
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH1.2.2.1

    have hH2lineOD :
        HilbertIncidence.OnLine H2 lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H2
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH2.2.2.1

    have hH1lineXC :
        HilbertIncidence.OnLine H1 lineXC :=
      hilbert_between_on_line
        Geo
        X H1 E
        lineXC
        hXlineXC
        hElineXC
        hXH1E

    have hH2lineXC :
        HilbertIncidence.OnLine H2 lineXC :=
      hilbert_between_on_line
        Geo
        C H2 E
        lineXC
        hClineXC
        hElineXC
        hCH2E

    have hOoffXC :
        Not (HilbertIncidence.OnLine O lineXC) := by
      intro hOline
      exact
        hXOC
          ⟨lineXC,
            hXlineXC,
            hOline,
            hClineXC⟩

    have hLinesODXC :
        lineOD ≠ lineXC := by
      intro hEq
      apply hOoffXC
      rw [← hEq]
      exact hOlineOD

    have hH1H2 :
        H1 = H2 := by

      by_contra hH1H2

      have hEq :
          lineOD = lineXC :=
        HilbertPlaneIncidence.line_unique
          H1 H2
          hH1H2
          lineOD lineXC
          hH1lineOD hH2lineOD
          hH1lineXC hH2lineXC

      exact hLinesODXC hEq

    have hCH1E :
        Geo.Between C H1 E := by
      simpa [hH1H2] using hCH2E

    have hEH1C :
        Geo.Between E H1 C :=
      (HilbertOrder.between_incidence
        C H1 E hCH1E).2.2.2.2

    have hInner :=
      hilbert_between_inner_trans
        Geo
        X H1 E C
        hXH1E
        hXEC

    have hH1EC :
        Geo.Between H1 E C :=
      hInner.1

    have hH1ECcol :
        PrimCollinear Geo H1 E C :=
      (HilbertOrder.between_incidence
        H1 E C hH1EC).2.2.2.1

    have hNotEH1C :
        Not (Geo.Between E H1 C) :=
      (HilbertOrder.between_unique
        (Geo := Geo)
        H1 E C
        hH1ECcol
        hH1EC).1

    exact hNotEH1C hEH1C

  --------------------------------------------------------------------
  -- Genuine noncollinear representative.
  --------------------------------------------------------------------

  · rcases hInsideFirst with
      ⟨H1,
        hXH1E,
        hRayODH1⟩

    rcases hInsideSecond with
      ⟨H2,
        hCH2E,
        hRayODH2⟩

    have hH1lineOD :
        HilbertIncidence.OnLine H1 lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H1
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH1.2.2.1

    have hH2lineOD :
        HilbertIncidence.OnLine H2 lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H2
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH2.2.2.1

    have hEH1X :
        Geo.Between E H1 X :=
      (HilbertOrder.between_incidence
        X H1 E hXH1E).2.2.2.2

    have hEH2C :
        Geo.Between E H2 C :=
      (HilbertOrder.between_incidence
        C H2 E hCH2E).2.2.2.2

    have hSameXC :
        HilbertSameSide Geo X C lineOD :=
      hilbert_third_side_endpoints_sameSide
        Geo
        E X C
        H1 H2
        lineOD
        hEXC
        hEH1X
        hEH2C
        hH1lineOD
        hH2lineOD

    have hOppXC :
        HilbertOppositeSide Geo X C lineOD :=
      ⟨hSameXC.1,
        hSameXC.2.1,
        ⟨H0,
          hXH0C,
          hH0lineOD⟩⟩

    exact
      hilbert_oppositeSide_not_sameSide
        Geo
        X C
        lineOD
        hOppXC
        hSameXC


/--
Uniqueness of the half of an angle.

If OD and OE are two interior rays of the same nondegenerate angle XOC
and each divides the angle into two congruent component angles, then
the two first halves are congruent.
-/
theorem hilbert_angleDecomposition_angle_half_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hBisectD :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisectE :
      Geo.AngleCongruent
        X O E
        C O E) :
    Geo.AngleCongruent
      X O D
      X O E := by

  have hXOD :
      Not (PrimCollinear Geo X O D) :=
    (hilbert_interior_angle_less
      Geo
      O D X C
      hXOC
      hInsideD).1

  have hXOE :
      Not (PrimCollinear Geo X O E) :=
    (hilbert_interior_angle_less
      Geo
      O E X C
      hXOC
      hInsideE).1

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
        X O D
        X O E
        hXOD
        hXOE
    with
    hEqual | hLess | hGreater

  · exact hEqual

  · have hCOD_XOD :
        Geo.AngleCongruent
          C O D
          X O D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        C O D
        hBisectD

    have hCOD_XOE :
        HilbertAngleLess Geo
          C O D
          X O E :=
      hilbert_angleLess_transport_left
        Geo
        X O D
        C O D
        X O E
        hLess
        hCOD
        hCOD_XOD

    have hCOD_COE :
        HilbertAngleLess Geo
          C O D
          C O E :=
      hilbert_angleLess_transport_right
        Geo
        C O D
        X O E
        C O E
        hCOD_XOE
        hCOE
        hBisectE

    exact
      False.elim
        (hilbert_angleDecomposition_two_component_less_impossible
          Geo
          O X C
          D E
          hXOC
          hInsideD
          hInsideE
          hLess
          hCOD_COE)

  · have hCOE_XOE :
        Geo.AngleCongruent
          C O E
          X O E :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O E
        C O E
        hBisectE

    have hCOE_XOD :
        HilbertAngleLess Geo
          C O E
          X O D :=
      hilbert_angleLess_transport_left
        Geo
        X O E
        C O E
        X O D
        hGreater
        hCOE
        hCOE_XOE

    have hCOE_COD :
        HilbertAngleLess Geo
          C O E
          C O D :=
      hilbert_angleLess_transport_right
        Geo
        C O E
        X O D
        C O D
        hCOE_XOD
        hCOD
        hBisectD

    exact
      False.elim
        (hilbert_angleDecomposition_two_component_less_impossible
          Geo
          O X C
          E D
          hXOC
          hInsideE
          hInsideD
          hGreater
          hCOE_COD)


/--
Both corresponding halves of two bisections of the same angle
are congruent.
-/
theorem hilbert_angleDecomposition_angle_half_unique_both
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hBisectD :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisectE :
      Geo.AngleCongruent
        X O E
        C O E) :
    Geo.AngleCongruent
        X O D
        X O E
    ∧
    Geo.AngleCongruent
        C O D
        C O E := by

  have hFirst :
      Geo.AngleCongruent
        X O D
        X O E :=
    hilbert_angleDecomposition_angle_half_unique
      Geo
      O X C D E
      hXOC
      hInsideD
      hInsideE
      hBisectD
      hBisectE

  have hCOD_XOD :
      Geo.AngleCongruent
        C O D
        X O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X O D
      C O D
      hBisectD

  have hCOD_XOE :
      Geo.AngleCongruent
        C O D
        X O E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C O D
      X O D
      X O E
      hCOD_XOD
      hFirst

  have hSecond :
      Geo.AngleCongruent
        C O D
        C O E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C O D
      X O E
      C O E
      hCOD_XOE
      hBisectE

  exact
    ⟨hFirst, hSecond⟩

------------------------------------------------------------------------

/--
Addition of two congruent component angles.

If OD and O'D' are interior rays of the nondegenerate angles XOC and
X'O'C', and the corresponding left and right component angles are
congruent, then the whole angles are congruent.

This is the interior-ray wrapper around Hilbert Theorem 15.
-/
theorem hilbert_angleDecomposition_angle_addition_interior
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hX'O'C' :
      Not (PrimCollinear Geo X' O' C'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' X' C')
    (hLeft :
      Geo.AngleCongruent
        X O D
        X' O' D')
    (hRight :
      Geo.AngleCongruent
        D O C
        D' O' C') :
    Geo.AngleCongruent
      X O C
      X' O' C' := by

  --------------------------------------------------------------------
  -- First interior ray: line OD crosses segment XC.
  --------------------------------------------------------------------

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hOD :
      O ≠ D :=
    hRayODH.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O D hOD
    with
    ⟨lineOD,
      hOlineOD,
      hDlineOD⟩

  have hHlineOD :
      HilbertIncidence.OnLine H lineOD :=
    hilbert_collinear_on_line
      Geo
      O D H
      lineOD
      hOD
      hOlineOD
      hDlineOD
      hRayODH.2.2.1

  have hXHCdata :=
    HilbertOrder.between_incidence
      X H C hXHC

  have hXH :
      X ≠ H :=
    hXHCdata.1

  have hHC :
      H ≠ C :=
    hXHCdata.2.1

  have hXHCcol :
      PrimCollinear Geo X H C :=
    hXHCdata.2.2.2.1

  have hXoff :
      Not (HilbertIncidence.OnLine X lineOD) := by
    intro hXline

    have hCline :
        HilbertIncidence.OnLine C lineOD :=
      hilbert_collinear_on_line
        Geo
        X H C
        lineOD
        hXH
        hXline
        hHlineOD
        hXHCcol

    exact
      hXOC
        ⟨lineOD,
          hXline,
          hOlineOD,
          hCline⟩

  have hCoff :
      Not (HilbertIncidence.OnLine C lineOD) := by
    intro hCline

    have hCHX :
        PrimCollinear Geo C H X :=
      PrimCollinearSymm
        Geo X H C hXHCcol

    have hXline :
        HilbertIncidence.OnLine X lineOD :=
      hilbert_collinear_on_line
        Geo
        C H X
        lineOD
        hHC.symm
        hCline
        hHlineOD
        hCHX

    exact
      hXOC
        ⟨lineOD,
          hXline,
          hOlineOD,
          hCline⟩

  have hOppXC :
      HilbertOppositeSide Geo X C lineOD :=
    ⟨hXoff,
      hCoff,
      ⟨H,
        hXHC,
        hHlineOD⟩⟩

  have hNotSameXC :
      Not (HilbertSameSide Geo X C lineOD) :=
    hilbert_oppositeSide_not_sameSide
      Geo X C lineOD hOppXC

  --------------------------------------------------------------------
  -- Second interior ray: line O'D' crosses segment X'C'.
  --------------------------------------------------------------------

  rcases hInside' with
    ⟨H', hX'H'C', hRayO'D'H'⟩

  have hO'D' :
      O' ≠ D' :=
    hRayO'D'H'.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O' D' hO'D'
    with
    ⟨lineO'D',
      hO'line,
      hD'line⟩

  have hH'line :
      HilbertIncidence.OnLine H' lineO'D' :=
    hilbert_collinear_on_line
      Geo
      O' D' H'
      lineO'D'
      hO'D'
      hO'line
      hD'line
      hRayO'D'H'.2.2.1

  have hX'H'C'data :=
    HilbertOrder.between_incidence
      X' H' C' hX'H'C'

  have hX'H' :
      X' ≠ H' :=
    hX'H'C'data.1

  have hH'C' :
      H' ≠ C' :=
    hX'H'C'data.2.1

  have hX'H'C'col :
      PrimCollinear Geo X' H' C' :=
    hX'H'C'data.2.2.2.1

  have hX'off :
      Not (HilbertIncidence.OnLine X' lineO'D') := by
    intro hX'line

    have hC'line :
        HilbertIncidence.OnLine C' lineO'D' :=
      hilbert_collinear_on_line
        Geo
        X' H' C'
        lineO'D'
        hX'H'
        hX'line
        hH'line
        hX'H'C'col

    exact
      hX'O'C'
        ⟨lineO'D',
          hX'line,
          hO'line,
          hC'line⟩

  have hC'off :
      Not (HilbertIncidence.OnLine C' lineO'D') := by
    intro hC'line

    have hC'H'X' :
        PrimCollinear Geo C' H' X' :=
      PrimCollinearSymm
        Geo X' H' C' hX'H'C'col

    have hX'line :
        HilbertIncidence.OnLine X' lineO'D' :=
      hilbert_collinear_on_line
        Geo
        C' H' X'
        lineO'D'
        hH'C'.symm
        hC'line
        hH'line
        hC'H'X'

    exact
      hX'O'C'
        ⟨lineO'D',
          hX'line,
          hO'line,
          hC'line⟩

  have hOppX'C' :
      HilbertOppositeSide Geo X' C' lineO'D' :=
    ⟨hX'off,
      hC'off,
      ⟨H',
        hX'H'C',
        hH'line⟩⟩

  have hNotSameX'C' :
      Not (HilbertSameSide Geo X' C' lineO'D') :=
    hilbert_oppositeSide_not_sameSide
      Geo X' C' lineO'D' hOppX'C'

  --------------------------------------------------------------------
  -- The two configurations are both opposite-side configurations.
  --------------------------------------------------------------------

  have hSideConfiguration :
      HilbertSameSide Geo X C lineOD ↔
      HilbertSameSide Geo X' C' lineO'D' := by
    constructor

    · intro hSame
      exact
        False.elim
          (hNotSameXC hSame)

    · intro hSame'
      exact
        False.elim
          (hNotSameX'C' hSame')

  --------------------------------------------------------------------
  -- Hilbert Theorem 15: addition of the two component angles.
  --------------------------------------------------------------------

  exact
    hilbert_angle_addition
      Geo
      X O D C
      X' O' D' C'
      lineOD lineO'D'
      hOD
      hO'D'
      hOlineOD
      hDlineOD
      hO'line
      hD'line
      hXoff
      hCoff
      hX'off
      hC'off
      hSideConfiguration
      hXOC
      hX'O'C'
      hLeft
      hRight


/--
A bisector can be transported through a congruence of whole angles.

The returned ray Y is interior to the target angle X'O'C', bisects it,
and its two component angles are congruent to the two component angles
cut by D in the source angle XOC.
-/
theorem hilbert_angleDecomposition_bisector_transport
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hX'O'C' :
      Not (PrimCollinear Geo X' O' C'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hBisect :
      Geo.AngleCongruent
        X O D
        C O D)
    (hWhole :
      Geo.AngleCongruent
        X O C
        X' O' C') :
    ∃ Y : Geo.Point,
      HilbertRayMeetsSegment Geo O' Y X' C' ∧
      Geo.AngleCongruent X' O' Y C' O' Y ∧
      Geo.AngleCongruent X O D X' O' Y ∧
      Geo.AngleCongruent C O D C' O' Y := by

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        O X C D
        X' O' C'
        hXOC
        hX'O'C'
        hInside
        hWhole
    with
    ⟨Y,
      hInsideY,
      hBoth⟩

  have hRightY :
      Geo.AngleCongruent
        C O D
        C' O' Y :=
    hBoth.1

  have hLeftY :
      Geo.AngleCongruent
        X O D
        X' O' Y :=
    hBoth.2

  have hX'O'Y_XOD :
      Geo.AngleCongruent
        X' O' Y
        X O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X O D
      X' O' Y
      hLeftY

  have hX'O'Y_COD :
      Geo.AngleCongruent
        X' O' Y
        C O D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X' O' Y
      X O D
      C O D
      hX'O'Y_XOD
      hBisect

  have hBisectY :
      Geo.AngleCongruent
        X' O' Y
        C' O' Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X' O' Y
      C O D
      C' O' Y
      hX'O'Y_COD
      hRightY

  exact
    ⟨Y,
      hInsideY,
      hBisectY,
      hLeftY,
      hRightY⟩


/--
Halves of congruent nondegenerate angles are congruent.

This is the synthetic replacement for numerical division of angle
measures by two.
-/
theorem hilbert_angleDecomposition_halves_congruent_of_whole_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hX'O'C' :
      Not (PrimCollinear Geo X' O' C'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' X' C')
    (hBisect :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisect' :
      Geo.AngleCongruent
        X' O' D'
        C' O' D')
    (hWhole :
      Geo.AngleCongruent
        X O C
        X' O' C') :
    Geo.AngleCongruent
      X O D
      X' O' D' := by

  rcases
      hilbert_angleDecomposition_bisector_transport
        Geo
        O X C D
        O' X' C'
        hXOC
        hX'O'C'
        hInside
        hBisect
        hWhole
    with
    ⟨Y,
      hInsideY,
      hBisectY,
      hLeftY,
      _hRightY⟩

  have hY_D' :
      Geo.AngleCongruent
        X' O' Y
        X' O' D' :=
    hilbert_angleDecomposition_angle_half_unique
      Geo
      O' X' C' Y D'
      hX'O'C'
      hInsideY
      hInside'
      hBisectY
      hBisect'

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X O D
      X' O' Y
      X' O' D'
      hLeftY
      hY_D'


/--
If two angles are bisected and one pair of corresponding halves is
congruent, then the whole angles are congruent.

This is the converse assembly form used when the component data are
already available.
-/
theorem hilbert_angleDecomposition_wholes_congruent_of_halves_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hX'O'C' :
      Not (PrimCollinear Geo X' O' C'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' X' C')
    (hBisect :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisect' :
      Geo.AngleCongruent
        X' O' D'
        C' O' D')
    (hHalf :
      Geo.AngleCongruent
        X O D
        X' O' D') :
    Geo.AngleCongruent
      X O C
      X' O' C' := by

  have hDOC_XOD :
      Geo.AngleCongruent
        D O C
        X O D :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      C O D
      X O D).mp
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        C O D
        hBisect)

  have hX'O'D'_D'O'C' :
      Geo.AngleCongruent
        X' O' D'
        D' O' C' :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      X' O' D'
      C' O' D').mp
      hBisect'

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
      hHalf

  have hRight :
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

  exact
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      O X C D
      O' X' C' D'
      hXOC
      hX'O'C'
      hInside
      hInside'
      hHalf
      hRight

------------------------------------------------------------------------

/--
Angle subtraction for two congruent whole angles.

Suppose OD and O'D' are interior rays of the nondegenerate angles
XOC and A'O'B'.  If the whole angles are congruent and the right
components

    angle COD
    angle B'O'D'

are congruent, then the remaining left components

    angle XOD
    angle A'O'D'

are congruent.

This is the synthetic version of Euclid's "the remaining angles are
equal" step.  No numerical angle measure is used.
-/
theorem hilbert_angleDecomposition_angle_subtraction
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D A' O' B' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hAOB :
      Not (PrimCollinear Geo A' O' B'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' A' B')
    (hWhole :
      Geo.AngleCongruent
        X O C
        A' O' B')
    (hRight :
      Geo.AngleCongruent
        C O D
        B' O' D') :
    Geo.AngleCongruent
      X O D
      A' O' D' := by

  --------------------------------------------------------------------
  -- Transport the source interior ray D into the target whole angle.
  --------------------------------------------------------------------

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        O X C D
        A' O' B'
        hXOC
        hAOB
        hInside
        hWhole
    with
    ⟨Y,
      hInsideY,
      hBoth⟩

  have hRightY :
      Geo.AngleCongruent
        C O D
        B' O' Y :=
    hBoth.1

  have hLeftY :
      Geo.AngleCongruent
        X O D
        A' O' Y :=
    hBoth.2

  --------------------------------------------------------------------
  -- The transported right component and the prescribed target right
  -- component are congruent.
  --------------------------------------------------------------------

  have hB'Y_B'D' :
      Geo.AngleCongruent
        B' O' Y
        B' O' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B' O' Y
      C O D
      B' O' D'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        C O D
        B' O' Y
        hRightY)
      hRight

  --------------------------------------------------------------------
  -- Y and D' are both interior rays of A'O'B', hence both lie in
  -- the same half-plane bounded by O'B'.
  --------------------------------------------------------------------

  have hO'B'A' :
      Not (PrimCollinear Geo O' B' A') := by
    intro h
    exact
      hAOB
        (PrimCollinearRotate
          Geo
          A' B' O'
          (PrimCollinearSymm
            Geo O' B' A' h))

  have hO'B' :
      O' ≠ B' :=
    hilbert_noncollinear_ne_first
      Geo
      O' B' A'
      hO'B'A'

  rcases
      HilbertPlaneIncidence.line_through
        O' B' hO'B'
    with
    ⟨lineB',
      hO'line,
      hB'line⟩

  have hYASame :
      HilbertSameSide Geo Y A' lineB' :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O' Y A' B'
      lineB'
      hO'line
      hB'line
      hAOB
      hInsideY

  have hD'ASame :
      HilbertSameSide Geo D' A' lineB' :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O' D' A' B'
      lineB'
      hO'line
      hB'line
      hAOB
      hInside'

  have hAD'Same :
      HilbertSameSide Geo A' D' lineB' :=
    hilbert_sameSide_symm
      Geo
      D' A'
      lineB'
      hD'ASame

  have hYD'Same :
      HilbertSameSide Geo Y D' lineB' :=
    hilbert_sameSide_trans
      Geo
      Y A' D'
      lineB'
      hYASame
      hAD'Same

  --------------------------------------------------------------------
  -- Equal angles with common base ray O'B', on the same side of the
  -- base line, determine the same ray.
  --------------------------------------------------------------------

  rcases
      hilbert_angle_unique_common_ray
        Geo
        B' O' Y D'
        lineB'
        hO'B'.symm
        hB'line
        hO'line
        hYASame.1
        hYD'Same
        hB'Y_B'D'
    with
    ⟨Z,
      hRayZY,
      hRayZD'⟩

  have hRayYD' :
      HilbertSameRay Geo O' Y D' :=
    hilbert_sameRay_of_common
      Geo
      O' Z Y D'
      hRayZY
      hRayZD'

  --------------------------------------------------------------------
  -- Replace Y by D' in the left component.
  --------------------------------------------------------------------

  have hAngleReplace :
      Geo.Angle A' O' Y =
      Geo.Angle A' O' D' :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      O' A' Y D'
      hRayYD'

  unfold Geometry.Geo.AngleCongruent
    at hLeftY ⊢

  rw [← hAngleReplace]

  exact hLeftY


/--
The symmetric subtraction form: equality of the left components
determines equality of the right components.
-/
theorem hilbert_angleDecomposition_angle_subtraction_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D A' O' B' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hAOB :
      Not (PrimCollinear Geo A' O' B'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' A' B')
    (hWhole :
      Geo.AngleCongruent
        X O C
        A' O' B')
    (hLeft :
      Geo.AngleCongruent
        X O D
        A' O' D') :
    Geo.AngleCongruent
      C O D
      B' O' D' := by

  --------------------------------------------------------------------
  -- Reverse both whole angles and both decompositions.
  --------------------------------------------------------------------

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hB'O'A' :
      Not (PrimCollinear Geo B' O' A') := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B' O' A' h)

  have hInsideRev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D X C
      hInside

  have hInside'Rev :
      HilbertRayMeetsSegment Geo O' D' B' A' :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O' D' A' B'
      hInside'

  have hWholeRev :
      Geo.AngleCongruent
        C O X
        B' O' A' :=
    AngleCongruentReverse
      Geo
      X O C
      A' O' B'
      hWhole

  have hLeftRev :
      Geo.AngleCongruent
        X O D
        A' O' D' :=
    hLeft

  have hResult :
      Geo.AngleCongruent
        C O D
        B' O' D' :=
    hilbert_angleDecomposition_angle_subtraction
      Geo
      O C X D
      B' O' A' D'
      hCOX
      hB'O'A'
      hInsideRev
      hInside'Rev
      hWholeRev
      hLeft

  exact hResult

end Geometry

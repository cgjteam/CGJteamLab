import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]

/--
Strict comparison of Hilbert angles.

`HilbertAngleLess Geo A O B C P D` means that the angle `AOB`
is congruent to an angle obtained inside the angle `CPD`.
-/
def HilbertAngleLess
    (A O B C P D : Geo.Point) : Prop :=
  ¬ PrimCollinear Geo A O B ∧
  ¬ PrimCollinear Geo C P D ∧
  ∃ X : Geo.Point,
    HilbertRayMeetsSegment Geo P X C D ∧
    Geo.AngleCongruent A O B C P X

theorem hilbert_angleLess_intro
    (A O B C P D X : Geo.Point)
    (hAOB : ¬ PrimCollinear Geo A O B)
    (hCPD : ¬ PrimCollinear Geo C P D)
    (hInside : HilbertRayMeetsSegment Geo P X C D)
    (hAngle : Geo.AngleCongruent A O B C P X) :
    HilbertAngleLess Geo A O B C P D := by
  exact ⟨hAOB, hCPD, X, hInside, hAngle⟩

theorem hilbert_interior_subangle_not_congruent_whole
    [HilbertCongruence Geo]
    (O D X C : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hInside : HilbertRayMeetsSegment Geo O D X C) :
    ¬ Geo.AngleCongruent C O D X O C := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  --------------------------------------------------------------------
  -- Base line OC.
  --------------------------------------------------------------------

  have hOC : O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo O C X
      (fun h =>
        hXOC
          (PrimCollinearRotate Geo X C O
            (PrimCollinearSymm Geo O C X h)))

  rcases HilbertPlaneIncidence.line_through O C hOC with
    ⟨base, hObase, hCbase⟩

  --------------------------------------------------------------------
  -- X and H are on the same side of OC, since X-H-C.
  --------------------------------------------------------------------

  have hXCO : ¬ PrimCollinear Geo X C O := by
    intro h
    exact hXOC
      (PrimCollinearRotate Geo X C O h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo X H O C hXHC hXCO with
    ⟨l, hOl, hCl, hXHsame_l⟩

  have hlbase : l = base :=
    HilbertPlaneIncidence.line_unique
      O C hOC
      l base
      hOl hCl
      hObase hCbase

  have hXHsame :
      HilbertSameSide Geo X H base := by
    rw [← hlbase]
    exact hXHsame_l

  --------------------------------------------------------------------
  -- D and H are on the same ray from O, hence on the same side of OC.
  --------------------------------------------------------------------

  rcases hRayODH.2.2.1 with
    ⟨rayLine, hOray, hDray, hHray⟩

  have hHC : H ≠ C :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.1

  have hCoff :
      ¬ HilbertIncidence.OnLine C rayLine := by
    intro hCray

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hHCX :
        PrimCollinear Geo H C X :=
      PrimCollinearCycle Geo X H C hXHCcol

    have hXray :
        HilbertIncidence.OnLine X rayLine :=
      hilbert_collinear_on_line
        Geo H C X
        rayLine
        hHC
        hHray
        hCray
        hHCX

    exact hXOC
      ⟨rayLine, hXray, hOray, hCray⟩

  have hDD :
      HilbertSameRay Geo O D D :=
    hilbert_sameRay_refl
      Geo O D hRayODH.1

  have hDHsame :
      HilbertSameSide Geo D H base :=
    hilbert_sameRay_points_sameSide
      Geo
      O D D H C
      rayLine base
      hOray hDray
      hObase hCbase
      hCoff
      hDD
      hRayODH

  have hHXsame :
      HilbertSameSide Geo H X base :=
    hilbert_sameSide_symm
      Geo X H base hXHsame

  have hDXsame :
      HilbertSameSide Geo D X base :=
    hilbert_sameSide_trans
      Geo D H X base
      hDHsame
      hHXsame

  --------------------------------------------------------------------
  -- Assume the proper subangle COD is congruent to the whole angle XOC.
  --------------------------------------------------------------------

  intro hCong

  have hCong' :
      Geo.AngleCongruent C O D C O X := by
    unfold Geometry.Geo.AngleCongruent at hCong ⊢
    rw [← Geo.angle_swap X O C]
    exact hCong

  --------------------------------------------------------------------
  -- Uniqueness of angle construction forces OD and OX to be the same ray.
  --------------------------------------------------------------------

  have hCO : C ≠ O :=
    hOC.symm

  rcases
      hilbert_angle_unique_common_ray
        Geo
        C O D X
        base
        hCO
        hCbase
        hObase
        hDXsame.1
        hDXsame
        hCong' with
    ⟨Z, hZD, hZX⟩

  have hDX :
      HilbertSameRay Geo O D X :=
    hilbert_sameRay_of_common
      Geo O Z D X
      hZD
      hZX

  --------------------------------------------------------------------
  -- But OD is an interior ray meeting XC at H.
  -- If OD = OX, then O,X,H are collinear.
  -- Together with X-H-C this makes X,O,C collinear: contradiction.
  --------------------------------------------------------------------

  have hXHray :
      HilbertSameRay Geo O X H :=
    hilbert_sameRay_of_common
      Geo O D X H
      hDX
      hRayODH

  have hOXH :
      PrimCollinear Geo O X H :=
    hXHray.2.2.1

  have hXHCcol :
      PrimCollinear Geo X H C :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.2.2.1

  have hXH : X ≠ H :=
    (HilbertOrder.between_incidence
      X H C hXHC).1

  have hOXC :
      PrimCollinear Geo O X C :=
    hilbert_primCollinear_trans
      Geo O X H C
      hXH
      hOXH
      hXHCcol

  exact hXOC
    (PrimCollinearSwap Geo O X C hOXC)

theorem hilbert_ray_order_exclusive
    [HilbertOrder Geo]
    (O D X C : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hDXC : HilbertRayMeetsSegment Geo O D X C) :
    ¬ HilbertRayMeetsSegment Geo O X D C := by

  --------------------------------------------------------------------
  -- First ordering: ray OD meets XC.
  --------------------------------------------------------------------

  rcases hDXC with
    ⟨H, hXHC, hRayODH⟩

  have hXHCdata :=
    HilbertOrder.between_incidence X H C hXHC

  have hXH : X ≠ H :=
    hXHCdata.1

  have hHC : H ≠ C :=
    hXHCdata.2.1

  have hXC : X ≠ C :=
    hXHCdata.2.2.1

  --------------------------------------------------------------------
  -- Base line OX.
  --------------------------------------------------------------------

  have hOX : O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo O X C
      (fun h =>
        hXOC
          (PrimCollinearSwap Geo O X C h))

  rcases HilbertPlaneIncidence.line_through O X hOX with
    ⟨lineOX, hOox, hXox⟩

  --------------------------------------------------------------------
  -- Line XC.
  --------------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through X C hXC with
    ⟨lineXC, hXxc, hCxc⟩

  have hHxc :
      HilbertIncidence.OnLine H lineXC :=
    hilbert_between_on_line
      Geo X H C lineXC
      hXxc hCxc hXHC

  have hOoffXC :
      ¬ HilbertIncidence.OnLine O lineXC := by
    intro hOxc
    exact hXOC
      ⟨lineXC, hXxc, hOxc, hCxc⟩

  --------------------------------------------------------------------
  -- H and C lie on the same ray from X.
  -- Hence H and C are on the same side of OX.
  --------------------------------------------------------------------

  have hRayXHC :
      HilbertSameRay Geo X H C :=
    hilbert_sameRay_of_between
      Geo X H C hXHC

  have hRayXHH :
      HilbertSameRay Geo X H H :=
    hilbert_sameRay_refl
      Geo X H hXH.symm

  have hHCsame :
      HilbertSameSide Geo H C lineOX :=
    hilbert_sameRay_points_sameSide
      Geo
      X H H C O
      lineXC lineOX
      hXxc hHxc
      hXox hOox
      hOoffXC
      hRayXHH
      hRayXHC

  --------------------------------------------------------------------
  -- Line OD.
  --------------------------------------------------------------------

  have hOD : O ≠ D :=
    hRayODH.1.symm

  rcases HilbertPlaneIncidence.line_through O D hOD with
    ⟨lineOD, hOod, hDod⟩

  have hHod :
      HilbertIncidence.OnLine H lineOD :=
    hilbert_collinear_on_line
      Geo O D H lineOD
      hOD
      hOod hDod
      hRayODH.2.2.1

  --------------------------------------------------------------------
  -- X is not on OD.
  --------------------------------------------------------------------

  have hXoffOD :
      ¬ HilbertIncidence.OnLine X lineOD := by
    intro hXod

    have hXHCcol :
        PrimCollinear Geo X H C :=
      hXHCdata.2.2.2.1

    have hCod :
        HilbertIncidence.OnLine C lineOD :=
      hilbert_collinear_on_line
        Geo X H C lineOD
        hXH
        hXod hHod
        hXHCcol

    exact hXOC
      ⟨lineOD, hXod, hOod, hCod⟩

  --------------------------------------------------------------------
  -- D and H lie on the same ray from O.
  -- Hence D and H are on the same side of OX.
  --------------------------------------------------------------------

  have hRayODD :
      HilbertSameRay Geo O D D :=
    hilbert_sameRay_refl
      Geo O D hRayODH.1

  have hDHsame :
      HilbertSameSide Geo D H lineOX :=
    hilbert_sameRay_points_sameSide
      Geo
      O D D H X
      lineOD lineOX
      hOod hDod
      hOox hXox
      hXoffOD
      hRayODD
      hRayODH

  --------------------------------------------------------------------
  -- Therefore D and C are on the same side of OX.
  --------------------------------------------------------------------

  have hDCsame :
      HilbertSameSide Geo D C lineOX :=
    hilbert_sameSide_trans
      Geo D H C lineOX
      hDHsame
      hHCsame

  --------------------------------------------------------------------
  -- Assume the reverse ordering:
  -- ray OX meets DC.
  --------------------------------------------------------------------

  intro hReverse

  rcases hReverse with
    ⟨K, hDKC, hRayOXK⟩

  have hKox :
      HilbertIncidence.OnLine K lineOX :=
    hilbert_collinear_on_line
      Geo O X K lineOX
      hOX
      hOox hXox
      hRayOXK.2.2.1

  --------------------------------------------------------------------
  -- Then D and C are on opposite sides of OX.
  --------------------------------------------------------------------

  have hOpp :
      HilbertOppositeSide Geo D C lineOX :=
    ⟨hDCsame.1,
      hDCsame.2.1,
      ⟨K, hDKC, hKox⟩⟩

  --------------------------------------------------------------------
  -- Contradiction.
  --------------------------------------------------------------------

  exact
    (hilbert_oppositeSide_not_sameSide
      Geo D C lineOX hOpp)
      hDCsame

/--
Hilbert Theorem 16, existence part.

If two nondegenerate angles are congruent and a ray lies in the
interior of the first angle, then there exists a corresponding
interior ray in the second angle which divides the two angles into
pairwise congruent component angles.

For the present development only the existence statement is needed.
The uniqueness clause of Hilbert's original Theorem 16 is not included.
-/
theorem hilbert_interior_subangle_transport
    [HilbertCongruence Geo]
    (O X C D A' O' B' : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hAOB : ¬ PrimCollinear Geo A' O' B')
    (hInside : HilbertRayMeetsSegment Geo O D X C)
    (hWhole :
      Geo.AngleCongruent X O C A' O' B') :
    ∃ D' : Geo.Point,
      HilbertRayMeetsSegment Geo O' D' A' B' ∧
      Geo.AngleCongruent C O D B' O' D' := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hO'B' : O' ≠ B' :=
    hilbert_noncollinear_ne_first
      Geo O' B' A'
      (fun h =>
        hAOB
          (PrimCollinearRotate Geo A' B' O'
            (PrimCollinearSymm Geo O' B' A' h)))

  have hA'O' : A' ≠ O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hAOB

  --------------------------------------------------------------------
  -- The component angle COD is nondegenerate.
  --------------------------------------------------------------------

  have hCOD :
      ¬ PrimCollinear Geo C O D := by
    intro hCODcol

    have hOD : O ≠ D :=
      hRayODH.1.symm

    have hOH : O ≠ H :=
      hRayODH.2.1.symm

    have hODH :
        PrimCollinear Geo O D H :=
      hRayODH.2.2.1

    have hCOH :
        PrimCollinear Geo C O H :=
      hilbert_primCollinear_trans
        Geo C O D H
        hOD
        hCODcol
        hODH

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hHC : H ≠ C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.1

    have hHCO :
        PrimCollinear Geo H C O :=
      PrimCollinearRotate Geo H O C
        (PrimCollinearSymm Geo C O H hCOH)

    have hXHO :
        PrimCollinear Geo X H O :=
      hilbert_primCollinear_trans
        Geo X H C O
        hHC
        hXHCcol
        hHCO

    have hXOH :
        PrimCollinear Geo X O H :=
      PrimCollinearRotate Geo X H O hXHO

    have hOHC :
        PrimCollinear Geo O H C :=
      PrimCollinearCycle Geo C O H hCOH

    have hXOCcol :
        PrimCollinear Geo X O C :=
      hilbert_primCollinear_trans
        Geo X O H C
        hOH
        hXOH
        hOHC

    exact hXOC hXOCcol

  --------------------------------------------------------------------
  -- Construct the copy of angle COD on ray O'B', on the side
  -- containing A'.
  --------------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through O' B' hO'B' with
    ⟨base', hO'base, hB'base⟩

  have hA'base :
      ¬ HilbertIncidence.OnLine A' base' := by
    intro hA'base
    exact hAOB
      ⟨base', hA'base, hO'base, hB'base⟩

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        C O D
        B' O' A'
        hCOD
        hO'B'.symm
        base'
        hB'base
        hO'base
        hA'base with
    ⟨D', hD'A'Same, hSubAngle, hUnique⟩

  refine ⟨D', ?_, hSubAngle⟩

  --------------------------------------------------------------------
  -- Prepare Theorem 15.
  --------------------------------------------------------------------

  have hOC : O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo O C X
      (fun h =>
        hXOC
          (PrimCollinearRotate Geo X C O
            (PrimCollinearSymm Geo O C X h)))

  rcases HilbertPlaneIncidence.line_through O C hOC with
    ⟨base, hObase, hCbase⟩

  have hDoff :
      ¬ HilbertIncidence.OnLine D base := by
    intro hDbase
    exact hCOD
      ⟨base, hCbase, hObase, hDbase⟩

  have hXoff :
      ¬ HilbertIncidence.OnLine X base := by
    intro hXbase
    exact hXOC
      ⟨base, hXbase, hObase, hCbase⟩

  have hDOC :
      Geo.AngleCongruent D O C D' O' B' :=
    AngleCongruentReverse
      Geo
      C O D
      B' O' D'
      hSubAngle

  have hCOX :
      Geo.AngleCongruent C O X B' O' A' :=
    AngleCongruentReverse
      Geo
      X O C
      A' O' B'
      hWhole

  have hRayDXC :
      HilbertRayMeetsSegment Geo O D X C :=
    ⟨H, hXHC, hRayODH⟩

  --------------------------------------------------------------------
  -- Theorem 15 gives the other pair of component angles.
  --------------------------------------------------------------------

  have hOther :
      Geo.AngleCongruent D O X D' O' A' :=
    hilbert_angle_addition_sameSide_case1
      Geo
      D O C X
      D' O' B' A'
      base base'
      hOC
      hO'B'
      hObase
      hCbase
      hO'base
      hB'base
      hDoff
      hXoff
      hD'A'Same.1
      hA'base
      hD'A'Same
      hRayDXC
      hDOC
      hCOX

  --------------------------------------------------------------------
  -- DOX is nondegenerate.
  --------------------------------------------------------------------

  have hDOX :
      ¬ PrimCollinear Geo D O X := by
    intro hDOXcol

    have hOD : O ≠ D :=
      hRayODH.1.symm

    have hOH : O ≠ H :=
      hRayODH.2.1.symm

    have hODH :
        PrimCollinear Geo O D H :=
      hRayODH.2.2.1

    have hXOD :
        PrimCollinear Geo X O D :=
      PrimCollinearSymm Geo D O X hDOXcol

    have hXOH :
        PrimCollinear Geo X O H :=
      hilbert_primCollinear_trans
        Geo X O D H
        hOD
        hXOD
        hODH

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hHX : H ≠ X :=
      (HilbertOrder.between_incidence
        X H C hXHC).1.symm

    have hOHX :
        PrimCollinear Geo O H X :=
      PrimCollinearCycle Geo X O H hXOH

    have hXHO :
        PrimCollinear Geo X H O :=
      PrimCollinearSymm Geo O H X hOHX

    have hHXC :
        PrimCollinear Geo H X C :=
      PrimCollinearSwap Geo X H C hXHCcol

    have hOHC :
        PrimCollinear Geo O H C :=
      hilbert_primCollinear_trans
        Geo O H X C
        hHX
        hOHX
        hHXC

    have hXOCcol :
        PrimCollinear Geo X O C :=
      hilbert_primCollinear_trans
        Geo X O H C
        hOH
        hXOH
        hOHC

    exact hXOC hXOCcol

  --------------------------------------------------------------------
  -- D', O', A' must also be noncollinear.
  --
  -- We already reduce a hypothetical collinear configuration to the
  -- statement that D' and A' determine the same ray from O'.
  -- The final contradiction with hOther / hDOX is still to be supplied.
  --------------------------------------------------------------------

  have hD'O'A' :
      ¬ PrimCollinear Geo D' O' A' := by
    intro hCol

    have hO'D' : O' ≠ D' := by
      intro h
      subst D'
      exact hD'A'Same.1 hO'base

    have hO'A' : O' ≠ A' :=
      hA'O'.symm

    have hNotBetween :
        ¬ Geo.Between D' O' A' := by
      intro hBetween

      have hOpp :
          HilbertOppositeSide Geo D' A' base' :=
        ⟨hD'A'Same.1,
         hD'A'Same.2.1,
         ⟨O', hBetween, hO'base⟩⟩

      exact
        (hilbert_oppositeSide_not_sameSide
          Geo D' A' base' hOpp)
          hD'A'Same

    have hSameRay :
        HilbertSameRay Geo O' D' A' :=
      ⟨hO'D'.symm,
       hO'A'.symm,
       PrimCollinearSwap Geo D' O' A' hCol,
       hNotBetween⟩

    -- Remaining local contradiction:
    -- hSameRay makes the two sides of angle D'O'A' the same ray,
    -- whereas hOther identifies it with the nondegenerate angle DOX.
    have hSameRay :
    HilbertSameRay Geo O' D' A' :=
  ⟨hO'D'.symm,
   hO'A'.symm,
   PrimCollinearSwap Geo D' O' A' hCol,
   hNotBetween⟩

-- Remaining local contradiction:
-- hSameRay makes the two sides of angle D'O'A' the same ray,
-- whereas hOther identifies it with the nondegenerate angle DOX.
    have hB'D'_B'A' :
        Geo.Angle B' O' D' = Geo.Angle B' O' A' :=
      hilbert_angle_eq_of_sameRay_second
        Geo O' B' D' A' hSameRay

    have hSubAngle' :
        Geo.AngleCongruent C O D B' O' A' := by
      unfold Geometry.Geo.AngleCongruent at hSubAngle ⊢
      rw [← hB'D'_B'A']
      exact hSubAngle

    have hWhole' :
        Geo.AngleCongruent X O C B' O' A' := by
      unfold Geometry.Geo.AngleCongruent at hWhole ⊢
      rw [← Geo.angle_swap A' O' B']
      exact hWhole

    have hSubWhole :
        Geo.AngleCongruent C O D X O C :=
      Geo.angle_congruent_transitivity
        C O D
        B' O' A'
        X O C
        hSubAngle'
        (Geo.angle_congruent_symmetry
          X O C
          B' O' A'
          hWhole')

    exact
      (hilbert_interior_subangle_not_congruent_whole
        Geo O D X C
        hXOC
        hRayDXC)
        hSubWhole



  --------------------------------------------------------------------
  -- Ray order in the target angle.
  --------------------------------------------------------------------

  rcases
      hilbert_sameSide_rays_order
        Geo
        O' D' B' A'
        base'
        hO'B'
        hO'base
        hB'base
        hD'A'Same.1
        hA'base
        hD'A'Same
        hD'O'A' with
    hTarget | hReverse

  --------------------------------------------------------------------
  -- Desired ordering.
  --------------------------------------------------------------------

  · exact hTarget

  --------------------------------------------------------------------
  -- The reverse ordering must be excluded.
  --------------------------------------------------------------------

  ·
    -- hReverse :
    -- HilbertRayMeetsSegment Geo O' A' D' B'
    sorry





theorem hilbert_exterior_angle_aux
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    ∃ M E : Geo.Point,
      Geo.Between A M C ∧
      Geo.Congruent A M M C ∧
      Geo.Between B M E ∧
      Geo.Congruent B M M E ∧
      Geo.AngleCongruent B A C M C E := by

  ----------------------------------------------------------------------
  -- Midpoint M of AC.
  ----------------------------------------------------------------------

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertMidpointExists Geo A C hAC with
    ⟨M, hMid⟩

  rcases hMid with
    ⟨hAMC, hAMMC⟩

  ----------------------------------------------------------------------
  -- B is not M.
  ----------------------------------------------------------------------

  have hBM : B ≠ M := by
    intro hBM
    subst M

    have hABCcol :
        PrimCollinear Geo A B C :=
      (HilbertOrder.between_incidence
        A B C hAMC).2.2.2.1

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Extend BM beyond M to E with BM ≅ ME.
  ----------------------------------------------------------------------

  rcases ExtendSegmentBeyond Geo B M hBM with
    ⟨E, hBME, hBMME⟩

  ----------------------------------------------------------------------
  -- Basic incidence data from A-M-C.
  ----------------------------------------------------------------------

  have hAMCdata :=
    HilbertOrder.between_incidence A M C hAMC

  have hAM : A ≠ M :=
    hAMCdata.1

  have hMC : M ≠ C :=
    hAMCdata.2.1

  have hAMCcol : PrimCollinear Geo A M C :=
    hAMCdata.2.2.2.1

  ----------------------------------------------------------------------
  -- Triangle AMB is noncollinear.
  ----------------------------------------------------------------------

  have hAMBnc : ¬ PrimCollinear Geo A M B := by
    intro hAMB

    have hCMA : PrimCollinear Geo C M A :=
      PrimCollinearSymm Geo A M C hAMCcol

    have hMAB : PrimCollinear Geo M A B :=
      PrimCollinearSwap Geo A M B hAMB

    have hCMB : PrimCollinear Geo C M B :=
      hilbert_primCollinear_trans
        Geo C M A B
        hAM.symm
        hCMA
        hMAB

    have hACM : PrimCollinear Geo A C M :=
      PrimCollinearRotate Geo A M C hAMCcol

    have hACB : PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo A C M B
        hMC.symm
        hACM
        hCMB

    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  ----------------------------------------------------------------------
  -- Vertical angles at M.
  ----------------------------------------------------------------------

  have hVertical :
      Geo.AngleCongruent A M B C M E :=
    hilbert_vertical_angles
      Geo A M B C E
      hAMC
      hBME
      hAMBnc

  ----------------------------------------------------------------------
  -- Triangle CME is also noncollinear.
  ----------------------------------------------------------------------

  have hBMEdata :=
    HilbertOrder.between_incidence B M E hBME

  have hME : M ≠ E :=
    hBMEdata.2.1

  have hBMEcol : PrimCollinear Geo B M E :=
    hBMEdata.2.2.2.1

  have hCME_nc : ¬ PrimCollinear Geo C M E := by
    intro hCME

    have hMEB : PrimCollinear Geo M E B :=
      PrimCollinearCycle Geo B M E hBMEcol

    have hCMB : PrimCollinear Geo C M B :=
      hilbert_primCollinear_trans
        Geo C M E B
        hME
        hCME
        hMEB

    have hMCB : PrimCollinear Geo M C B :=
      PrimCollinearSwap Geo C M B hCMB

    have hAMB : PrimCollinear Geo A M B :=
      hilbert_primCollinear_trans
        Geo A M C B
        hMC
        hAMCcol
        hMCB

    exact hAMBnc hAMB

  ----------------------------------------------------------------------
  -- Put the side congruences in the orientation required by SAS:
  --
  -- MA ≅ MC
  -- MB ≅ ME
  ----------------------------------------------------------------------

  have hMAMC : Geo.Congruent M A M C :=
    (Geo.congruent_reverse_first
      A M M C).mp hAMMC

  have hMBME : Geo.Congruent M B M E :=
    (Geo.congruent_reverse_first
      B M M E).mp hBMME

  ----------------------------------------------------------------------
  -- Reorient noncollinearity for triangles MAB and MCE.
  ----------------------------------------------------------------------

  have hMABnc : ¬ PrimCollinear Geo M A B := by
    intro h
    exact hAMBnc
      (PrimCollinearSwap Geo M A B h)

  have hMCEnc : ¬ PrimCollinear Geo M C E := by
    intro h
    exact hCME_nc
      (PrimCollinearSwap Geo M C E h)

  ----------------------------------------------------------------------
  -- SAS:
  --
  -- triangle MAB ≅ triangle MCE
  --
  -- hence angle MAB ≅ angle MCE.
  ----------------------------------------------------------------------

  have hSAS :=
    hilbert_sas_remaining_angles
      Geo
      M A B
      M C E
      hMABnc
      hMCEnc
      hMAMC
      hMBME
      hVertical

  have hMAB_MCE :
      Geo.AngleCongruent M A B M C E :=
    hSAS.1

  ----------------------------------------------------------------------
  -- Since A-M-C, rays AM and AC are the same.
  -- Therefore angle MAB = angle CAB = angle BAC.
  ----------------------------------------------------------------------

  have hRayAMC : HilbertSameRay Geo A M C :=
    hilbert_sameRay_of_between
      Geo A M C hAMC

  have hMAB_CAB :
      Geo.Angle M A B = Geo.Angle C A B :=
    hilbert_angle_eq_of_sameRay_first
      Geo A M C B hRayAMC

  have hBAC_MAB :
      Geo.Angle B A C = Geo.Angle M A B := by
    calc
      Geo.Angle B A C = Geo.Angle C A B :=
        Geo.angle_swap B A C
      _ = Geo.Angle M A B :=
        hMAB_CAB.symm

  ----------------------------------------------------------------------
  -- Transport the SAS angle equality to BAC.
  ----------------------------------------------------------------------

  have hBAC_MCE :
      Geo.AngleCongruent B A C M C E := by
    unfold Geometry.Geo.AngleCongruent at hMAB_MCE ⊢
    rw [hBAC_MAB]
    exact hMAB_MCE

 --xact ⟨M, E, hAMC, hBME, hBAC_MCE⟩
  exact
  ⟨M, E,
    hAMC,
    hAMMC,
    hBME,
    hBMME,
    hBAC_MCE⟩

theorem hilbert_exterior_angle_meets_AD
    [HilbertCongruence Geo]
    (A B C D E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hBCD : Geo.Between B C D)
    (hParallel : Geo.Parallel A B C E) :
    ∃ H : Geo.Point,
      Geo.Between A H D ∧
      PrimCollinear Geo C E H := by

  have hBCDdata :=
    HilbertOrder.between_incidence B C D hBCD

  have hBC : B ≠ C :=
    hBCDdata.1

  have hCD : C ≠ D :=
    hBCDdata.2.1

  have hBD : B ≠ D :=
    hBCDdata.2.2.1

  have hBCDcol : PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  have hAB : A ≠ B :=
    hParallel.1

  have hCE : C ≠ E :=
    hParallel.2.1

  ----------------------------------------------------------------------
  -- ABD is a genuine triangle.
  ----------------------------------------------------------------------

  have hBDA : ¬ PrimCollinear Geo B D A := by
    intro hBDAcol

    have hCDB : PrimCollinear Geo C D B :=
      PrimCollinearCycle Geo B C D hBCDcol

    have hDBA : PrimCollinear Geo D B A :=
      PrimCollinearSwap Geo B D A hBDAcol

    have hCDA : PrimCollinear Geo C D A :=
      hilbert_primCollinear_trans
        Geo C D B A
        hBD.symm
        hCDB
        hDBA

    have hBCA : PrimCollinear Geo B C A :=
      hilbert_primCollinear_trans
        Geo B C D A
        hCD
        hBCDcol
        hCDA

    have hCAB : PrimCollinear Geo C A B :=
      PrimCollinearCycle Geo B C A hBCA

    have hABCcol : PrimCollinear Geo A B C :=
      PrimCollinearCycle Geo C A B hCAB

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Lines AB and CE.
  ----------------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨lineAB, hAab, hBab⟩

  rcases HilbertPlaneIncidence.line_through C E hCE with
    ⟨lineCE, hCce, hEce⟩

  ----------------------------------------------------------------------
  -- A and B cannot lie on CE because AB || CE.
  ----------------------------------------------------------------------

  have hAce : ¬ HilbertIncidence.OnLine A lineCE := by
    intro hAce

    have hAinAB : A ∈ Geo.PointLine A B := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo A B A lineAB
          hAB hAab hBab).2 hAab

    have hAinCE : A ∈ Geo.PointLine C E := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo C E A lineCE
          hCE hCce hEce).2 hAce

    exact
      Set.disjoint_left.mp hParallel.2.2
        hAinAB hAinCE

  have hBce : ¬ HilbertIncidence.OnLine B lineCE := by
    intro hBce

    have hBinAB : B ∈ Geo.PointLine A B := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo A B B lineAB
          hAB hAab hBab).2 hBab

    have hBinCE : B ∈ Geo.PointLine C E := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo C E B lineCE
          hCE hCce hEce).2 hBce

    exact
      Set.disjoint_left.mp hParallel.2.2
        hBinAB hBinCE

  ----------------------------------------------------------------------
  -- D is not on CE either.
  ----------------------------------------------------------------------

  have hDce : ¬ HilbertIncidence.OnLine D lineCE := by
    intro hDce

    have hCDB : PrimCollinear Geo C D B :=
      PrimCollinearCycle Geo B C D hBCDcol

    have hBce' : HilbertIncidence.OnLine B lineCE :=
      hilbert_collinear_on_line
        Geo C D B
        lineCE
        hCD
        hCce
        hDce
        hCDB

    exact hBce hBce'

  ----------------------------------------------------------------------
  -- CE meets side BD at C.
  ----------------------------------------------------------------------

  have hMeetsBD :
      HilbertSegmentMeetsLine Geo B D lineCE :=
    ⟨C, hBCD, hCce⟩

  ----------------------------------------------------------------------
  -- Pasch in triangle BDA.
  --
  -- Since CE enters through BD, it must leave through BA or DA.
  ----------------------------------------------------------------------

  rcases HilbertOrder.pasch
      (Geo := Geo)
      B D A
      hBDA
      lineCE
      hBce
      hDce
      hAce
      hMeetsBD with
    hMeetsBA | hMeetsDA

  ----------------------------------------------------------------------
  -- The BA alternative contradicts AB || CE.
  ----------------------------------------------------------------------

  · rcases hMeetsBA with
      ⟨X, hBXA, hXce⟩

    have hXab :
        HilbertIncidence.OnLine X lineAB :=
      hilbert_between_on_line
        Geo B X A
        lineAB
        hBab hAab
        hBXA

    have hXinAB : X ∈ Geo.PointLine A B := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo A B X lineAB
          hAB hAab hBab).2 hXab

    have hXinCE : X ∈ Geo.PointLine C E := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo C E X lineCE
          hCE hCce hEce).2 hXce

    exact
      False.elim
        (Set.disjoint_left.mp hParallel.2.2
          hXinAB hXinCE)

  ----------------------------------------------------------------------
  -- Therefore CE meets DA.
  ----------------------------------------------------------------------

  · rcases hMeetsDA with
      ⟨H, hDHA, hHce⟩

    have hAHD : Geo.Between A H D :=
      (HilbertOrder.between_incidence
        D H A hDHA).2.2.2.2

    have hCEH : PrimCollinear Geo C E H :=
      ⟨lineCE, hCce, hEce, hHce⟩

    exact ⟨H, hAHD, hCEH⟩


theorem hilbert_exterior_angle_sameRay
    [HilbertCongruence Geo]
    (A B C D M E H : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hBCD : Geo.Between B C D)
    (hAHD : Geo.Between A H D)
    (hCEH : PrimCollinear Geo C E H) :
    HilbertSameRay Geo C E H := by

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertPlaneIncidence.line_through A C hAC with
    ⟨lineAC, hAac, hCac⟩

  have hMac : HilbertIncidence.OnLine M lineAC :=
    hilbert_between_on_line
      Geo A M C lineAC
      hAac hCac hAMC

  ----------------------------------------------------------------------
  -- Triangle BED is noncollinear.
  ----------------------------------------------------------------------

  have hBED : ¬ PrimCollinear Geo B E D := by
    rintro ⟨l, hBl, hEl, hDl⟩

    have hMl : HilbertIncidence.OnLine M l :=
      hilbert_between_on_line
        Geo B M E l
        hBl hEl hBME

    have hCl : HilbertIncidence.OnLine C l :=
      hilbert_between_on_line
        Geo B C D l
        hBl hDl hBCD

    have hMC : M ≠ C :=
      (HilbertOrder.between_incidence
        A M C hAMC).2.1

    have hAl : HilbertIncidence.OnLine A l :=
      hilbert_collinear_on_line
        Geo M C A l
        hMC
        hMl hCl
        (PrimCollinearCycle Geo A M C
          (HilbertOrder.between_incidence
            A M C hAMC).2.2.2.1)

    exact hABC ⟨l, hAl, hBl, hCl⟩

  ----------------------------------------------------------------------
  -- AC meets BE at M and BD at C.
  -- Hence E and D lie on the same side of AC.
  ----------------------------------------------------------------------

  have hEDsame :
      HilbertSameSide Geo E D lineAC :=
    hilbert_third_side_endpoints_sameSide
      Geo
      B E D
      M C
      lineAC
      hBED
      hBME
      hBCD
      hMac
      hCac

  ----------------------------------------------------------------------
  -- D is off AC.
  ----------------------------------------------------------------------

  have hDac : ¬ HilbertIncidence.OnLine D lineAC := by
    intro hDac

    have hBCDcol :
        PrimCollinear Geo B C D :=
      (HilbertOrder.between_incidence
        B C D hBCD).2.2.2.1

    have hCD : C ≠ D :=
      (HilbertOrder.between_incidence
        B C D hBCD).2.1

    have hBac : HilbertIncidence.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo C D B lineAC
        hCD
        hCac hDac
        (PrimCollinearCycle Geo B C D hBCDcol)

    exact hABC ⟨lineAC, hAac, hBac, hCac⟩

  ----------------------------------------------------------------------
  -- H and D are on the same side of AC.
  ----------------------------------------------------------------------

  have hAD : A ≠ D :=
    (HilbertOrder.between_incidence
      A H D hAHD).2.2.1

  rcases HilbertPlaneIncidence.line_through A D hAD with
    ⟨lineAD, hAad, hDad⟩

  have hHad : HilbertIncidence.OnLine H lineAD :=
    hilbert_between_on_line
      Geo A H D lineAD
      hAad hDad hAHD

  have hHac : ¬ HilbertIncidence.OnLine H lineAC := by
    intro hHac

    have hAH : A ≠ H :=
      (HilbertOrder.between_incidence
        A H D hAHD).1

    have hEq : lineAD = lineAC :=
      HilbertPlaneIncidence.line_unique
        A H hAH
        lineAD lineAC
        hAad hHad
        hAac hHac

    exact hDac (hEq ▸ hDad)

  have hAHDsame : HilbertSameRay Geo A H D :=
    hilbert_sameRay_of_between
      Geo A H D hAHD

  have hADHsame : HilbertSameRay Geo A D H :=
    hilbert_sameRay_symm
      Geo A H D hAHDsame

  have hADDsame : HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hHDsame :
      HilbertSameSide Geo H D lineAC :=
    hilbert_sameRay_points_sameSide
      Geo
      A D H D C
      lineAD lineAC
      hAad hDad
      hAac hCac
      (by
        intro hCad
        have hEq : lineAD = lineAC :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            lineAD lineAC
            hAad hCad
            hAac hCac
        exact hDac (hEq ▸ hDad))
      hADHsame
      hADDsame

  ----------------------------------------------------------------------
  -- E and H are therefore on the same side of AC.
  ----------------------------------------------------------------------

  have hDHsame :
      HilbertSameSide Geo D H lineAC :=
    hilbert_sameSide_symm
      Geo H D lineAC hHDsame

  have hEHsame :
      HilbertSameSide Geo E H lineAC :=
    hilbert_sameSide_trans
      Geo E D H lineAC
      hEDsame
      hDHsame

  ----------------------------------------------------------------------
  -- Build SameRay(C,E,H).
  ----------------------------------------------------------------------

  have hEC : E ≠ C := by
    intro h
    subst E
    exact hEHsame.1 hCac

  have hHC : H ≠ C := by
    intro h
    subst H
    exact hEHsame.2.1 hCac

  refine
    ⟨hEC,
      hHC,
      hCEH,
      ?_⟩

  intro hECH

  have hOpp :
      HilbertOppositeSide Geo E H lineAC :=
    ⟨hEHsame.1,
      hEHsame.2.1,
      ⟨C, hECH, hCac⟩⟩

  exact
    (hilbert_oppositeSide_not_sameSide
      Geo E H lineAC hOpp)
      hEHsame

theorem hilbert_exterior_angle_inside
    [HilbertCongruence Geo]
    (A B C D M E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hBCD : Geo.Between B C D)
    (hParallel : Geo.Parallel A B C E) :
    HilbertRayMeetsSegment Geo C E A D := by

  rcases hilbert_exterior_angle_meets_AD
      Geo A B C D E
      hABC
      hBCD
      hParallel with
    ⟨H, hAHD, hCEH⟩

  have hRay :
      HilbertSameRay Geo C E H :=
    hilbert_exterior_angle_sameRay
      Geo A B C D M E H
      hABC
      hAMC
      hBME
      hBCD
      hAHD
      hCEH

  exact ⟨H, hAHD, hRay⟩

theorem hilbert_exterior_angle_aux_parallel
    [HilbertCongruence Geo]
    (A B C M E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hAngle : Geo.AngleCongruent B A C M C E) :
    Geo.Parallel A B C E := by

  ----------------------------------------------------------------------
  -- The transversal AC.
  ----------------------------------------------------------------------

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertPlaneIncidence.line_through A C hAC with
    ⟨lineAC, hAac, hCac⟩

  have hMac :
      HilbertIncidence.OnLine M lineAC :=
    hilbert_between_on_line
      Geo A M C lineAC
      hAac hCac hAMC

  ----------------------------------------------------------------------
  -- B is off AC.
  ----------------------------------------------------------------------

  have hBoff :
      ¬ HilbertIncidence.OnLine B lineAC := by
    intro hBac
    exact hABC
      ⟨lineAC, hAac, hBac, hCac⟩

  ----------------------------------------------------------------------
  -- E is off AC.
  ----------------------------------------------------------------------

  have hBMEdata :=
    HilbertOrder.between_incidence B M E hBME

  have hME : M ≠ E :=
    hBMEdata.2.1

  have hEoff :
      ¬ HilbertIncidence.OnLine E lineAC := by
    intro hEac

    have hBac :
        HilbertIncidence.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo M E B
        lineAC
        hME
        hMac hEac
        (PrimCollinearCycle Geo B M E
          hBMEdata.2.2.2.1)

    exact hBoff hBac

  ----------------------------------------------------------------------
  -- Since B-M-E, B and E lie on opposite sides of AC.
  ----------------------------------------------------------------------

  have hOppBE :
      HilbertOppositeSide Geo B E lineAC :=
    ⟨hBoff,
      hEoff,
      ⟨M, hBME, hMac⟩⟩

  ----------------------------------------------------------------------
  -- Convert angle BAC to angle MAB.
  --
  -- A-M-C means rays AM and AC coincide.
  ----------------------------------------------------------------------

  have hRayAMC :
      HilbertSameRay Geo A M C :=
    hilbert_sameRay_of_between
      Geo A M C hAMC

  have hMAB_BAC :
      Geo.Angle M A B = Geo.Angle B A C := by
    calc
      Geo.Angle M A B = Geo.Angle B A M := by
        exact Geo.angle_swap M A B
      _ = Geo.Angle B A C :=
        hilbert_angle_eq_of_sameRay_second
          Geo A B M C hRayAMC

  have hAlternate :
      Geo.AngleCongruent M A B M C E := by
    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [hMAB_BAC]
    exact hAngle

  ----------------------------------------------------------------------
  -- Equal alternate angles imply parallel lines.
  -- This is the neutral direction of Hilbert Theorem 30.
  ----------------------------------------------------------------------

  exact
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo A B C M E lineAC
      hAMC
      hAac hCac
      hOppBE
      hAlternate

/--
Full quantitative form of Hilbert's exterior-angle theorem
(Theorem 22), first remote interior angle.

If `A` lies between `B` and `D`, then `CAD` is an exterior
angle of triangle `ABC`.  The theorem states that the remote
interior angle `ACB` is strictly smaller than `CAD`.

The earlier theorem

`hilbert_exterior_angle_not_congruent`

was intentionally proved only in the weaker form needed for the
alternate-angle criterion.  It is retained unchanged.  The present
theorem restores the strict angle comparison required by Euclid I.16.

In the notation of `HilbertAngleLess`, the conclusion is

    angle ACB < angle CAD.
-/
theorem hilbert_exterior_angle_less
    [HilbertCongruence Geo]
    (A B C D M E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hBCD : Geo.Between B C D)
    (hAngle : Geo.AngleCongruent B A C M C E)
    (hParallel : Geo.Parallel A B C E) :
    HilbertAngleLess Geo B A C A C D := by

  ----------------------------------------------------------------------
  -- First angle BAC is nondegenerate in the required orientation.
  ----------------------------------------------------------------------

  have hBACnc : ¬ PrimCollinear Geo B A C := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  ----------------------------------------------------------------------
  -- Exterior angle ACD is nondegenerate.
  ----------------------------------------------------------------------

  have hBCDdata :=
    HilbertOrder.between_incidence B C D hBCD

  have hCD : C ≠ D :=
    hBCDdata.2.1

  have hBCDcol : PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  have hACDnc : ¬ PrimCollinear Geo A C D := by
    intro hACD

    have hCDB : PrimCollinear Geo C D B :=
      PrimCollinearCycle Geo B C D hBCDcol

    have hACB : PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo A C D B
        hCD
        hACD
        hCDB

    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  ----------------------------------------------------------------------
  -- Since A-M-C, rays CM and CA coincide.
  -- Hence angle MCE = angle ACE.
  ----------------------------------------------------------------------

  have hCMA : Geo.Between C M A :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.2

  have hRayCMA : HilbertSameRay Geo C M A :=
    hilbert_sameRay_of_between
      Geo C M A hCMA

  have hMCE_ACE :
      Geo.Angle M C E = Geo.Angle A C E :=
    hilbert_angle_eq_of_sameRay_first
      Geo C M A E hRayCMA

  have hBAC_ACE :
      Geo.AngleCongruent B A C A C E := by
    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [← hMCE_ACE]
    exact hAngle

  ----------------------------------------------------------------------
  -- Ray CE meets the open segment AD.
  ----------------------------------------------------------------------

  have hInside :
      HilbertRayMeetsSegment Geo C E A D :=
    hilbert_exterior_angle_inside
      Geo A B C D M E
      hABC
      hAMC
      hBME
      hBCD
      hParallel

  ----------------------------------------------------------------------
  -- Definition of HilbertAngleLess.
  -- Witness X = E.
  ----------------------------------------------------------------------

  exact
    ⟨hBACnc,
      hACDnc,
      ⟨E,
        hInside,
        hBAC_ACE⟩⟩

theorem hilbert_angleLess_transport_right
    [HilbertCongruence Geo]
    (A O B C P D C' P' D' : Geo.Point)
    (hLess :
      HilbertAngleLess Geo A O B C P D)
    (hTarget :
      ¬ PrimCollinear Geo C' P' D')
    (hWhole :
      Geo.AngleCongruent C P D C' P' D') :
    HilbertAngleLess Geo A O B C' P' D' := by

  rcases hLess with
    ⟨hAOB, hCPD, X, hInside, hAngle⟩

  ----------------------------------------------------------------------
  -- Reverse the source and target whole angles.
  ----------------------------------------------------------------------

  have hWholeRev :
      Geo.AngleCongruent D P C D' P' C' :=
    (Geo.angle_congruent_reverse_second
      D P C C' P' D').mp
      ((Geo.angle_congruent_reverse_first
        C P D C' P' D').mp hWhole)

  ----------------------------------------------------------------------
  -- Reverse the open segment CD.
  ----------------------------------------------------------------------

  rcases hInside with
    ⟨H, hCHD, hRayPXH⟩

  have hDHC :
      Geo.Between D H C :=
    (HilbertOrder.between_incidence
      C H D hCHD).2.2.2.2

  have hInsideRev :
      HilbertRayMeetsSegment Geo P X D C :=
    ⟨H, hDHC, hRayPXH⟩

  ----------------------------------------------------------------------
  -- Transport the interior ray to the congruent target angle.
  ----------------------------------------------------------------------

  rcases
      hilbert_interior_subangle_transport
        Geo
        P D C X
        D' P' C'
        (by
          intro h
          exact hCPD
            (PrimCollinearSymm Geo D P C h))
        (by
          intro h
          exact hTarget
            (PrimCollinearSymm Geo D' P' C' h))
        hInsideRev
        hWholeRev with
    ⟨Y, hInsideTargetRev, hSubAngle⟩

  ----------------------------------------------------------------------
  -- Reverse target segment D'C'.
  ----------------------------------------------------------------------

  rcases hInsideTargetRev with
    ⟨K, hD'KC', hRayP'YK⟩

  have hC'KD' :
      Geo.Between C' K D' :=
    (HilbertOrder.between_incidence
      D' K C' hD'KC').2.2.2.2

  have hInsideTarget :
      HilbertRayMeetsSegment Geo P' Y C' D' :=
    ⟨K, hC'KD', hRayP'YK⟩

  ----------------------------------------------------------------------
  -- The transported subangle already has the required orientation.
  ----------------------------------------------------------------------

  have hSubAngle' :
      Geo.AngleCongruent C P X C' P' Y :=
    hSubAngle

  ----------------------------------------------------------------------
  -- Compose with the original witness angle.
  ----------------------------------------------------------------------

  have hFinal :
      Geo.AngleCongruent A O B C' P' Y :=
    Geo.angle_congruent_transitivity
      A O B
      C P X
      C' P' Y
      hAngle
      hSubAngle'

  ----------------------------------------------------------------------
  -- Definition of HilbertAngleLess.
  ----------------------------------------------------------------------

  exact
    ⟨hAOB,
      hTarget,
      ⟨Y,
        hInsideTarget,
        hFinal⟩⟩

end Geometry

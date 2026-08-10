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
    sorry

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
    (A B C D : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hBAD : Geo.Between B A D) :
    HilbertAngleLess Geo A C B C A D := by

  have hACB :
      ¬ PrimCollinear Geo A C B :=
    fun h =>
      hABC (PrimCollinearRotate Geo A C B h)

  have hCAD :
      ¬ PrimCollinear Geo C A D := by
    intro h

    have hBADcol :
        PrimCollinear Geo B A D :=
      (HilbertOrder.between_incidence
        B A D hBAD).2.2.2.1

    have hAD : A ≠ D :=
      (HilbertOrder.between_incidence
        B A D hBAD).2.1

    have hDAC :
        PrimCollinear Geo D A C :=
      PrimCollinearSymm Geo C A D h

    have hADC :
        PrimCollinear Geo A D C :=
      PrimCollinearSwap Geo D A C hDAC

    have hBAC :
        PrimCollinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo B A D C
        hAD
        hBADcol
        hADC

    exact hABC
      (PrimCollinearSwap Geo B A C hBAC)

  refine ⟨hACB, hCAD, ?_⟩
  have hCA : C ≠ A :=
    (hilbert_noncollinear_ne_first
      Geo C A D hCAD)

  rcases HilbertPlaneIncidence.line_through C A hCA with
    ⟨base, hCbase, hAbase⟩

  have hDbase :
      ¬ HilbertIncidence.OnLine D base := by
    intro hDbase
    exact hCAD
      ⟨base, hCbase, hAbase, hDbase⟩

  rcases HilbertCongruence.angle_construction
      (Geo := Geo)
      A C B
      C A D
      hACB
      hCA
      base
      hCbase
      hAbase
      hDbase with
    ⟨X, hXDSame, hAngleX, _⟩
  have hXAD :
      ¬ PrimCollinear Geo X A D := by
    intro hXADcol

    have hAX : A ≠ X := by
      intro h
      subst X
      exact hXDSame.1 hAbase

    have hAD : A ≠ D := by
      intro h
      subst D
      exact hXDSame.2.1 hAbase

    have hAXDcol :
    PrimCollinear Geo A X D :=
  PrimCollinearSwap Geo X A D hXADcol

    have hNotXAD :
        ¬ Geo.Between X A D := by
      intro hXADbetween

      have hOpp :
          HilbertOppositeSide Geo X D base :=
        ⟨hXDSame.1,
         hXDSame.2.1,
         ⟨A, hXADbetween, hAbase⟩⟩

      exact
        (hilbert_oppositeSide_not_sameSide
          Geo X D base hOpp)
          hXDSame

    have hAXDRay :
        HilbertSameRay Geo A X D :=
      ⟨hAX.symm,
       hAD.symm,
       hAXDcol,
       hNotXAD⟩

    have hAngleEq :
        Geo.Angle C A X = Geo.Angle C A D :=
      hilbert_angle_eq_of_sameRay_second
        Geo A C X D hAXDRay

    have hExterior :
        Geo.AngleCongruent C A D A C B := by
      have hSym :
          Geo.AngleCongruent C A X A C B :=
        Geometry.Geo.angle_congruent_symmetry
          Geo A C B C A X hAngleX

      unfold Geometry.Geo.AngleCongruent at hSym ⊢
      rw [← hAngleEq]
      exact hSym

    exact
      (hilbert_exterior_angle_not_congruent
        Geo A B C D hABC hBAD)
        hExterior
  rcases
      hilbert_sameSide_rays_order
        Geo
        A X C D
        base
        hCA.symm
        hAbase
        hCbase
        hXDSame.1
        hDbase
        hXDSame
        hXAD with
    hAXmeetsDC | hADmeetsXC

  · rcases hAXmeetsDC with
      ⟨Y, hDYC, hAXY⟩

    have hCYD :
        Geo.Between C Y D :=
      (HilbertOrder.between_incidence
        D Y C hDYC).2.2.2.2

    exact
      ⟨X,
       ⟨Y, hCYD, hAXY⟩,
       hAngleX⟩

  ·
    -- The remaining Hilbert Theorem 22 case:
    -- ray AD lies inside angle XAC.
    sorry

end Geometry

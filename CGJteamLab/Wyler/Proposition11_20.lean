import CGJteamLab.HilbertTrihedralAngleMetric
import CGJteamLab.HilbertWylerAxioms

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Local compatibility adapter exposing the plane-incidence parent already
contained in `HilbertCongruence`.

This is only the inherited parent projection; it introduces no new
axiom and no new geometric data.  It is kept local to this module so
that the global typeclass graph is unchanged.
-/
local instance hilbertPlaneIncidence_of_hilbertCongruence_XI20
    [H : HilbertIncidence Geo]
    [HC : HilbertCongruence Geo] :
    HilbertPlaneIncidence Geo :=
  HC.toHilbertOrder.toHilbertPlaneIncidence

/--
XI.20: the complete local remainder lemma in the Hilbert-Wyler route.

Let O; X,Y,Z be a proper trihedral configuration.  Suppose OW is an
interior ray of angle XOY and

    angle ZOX ~= angle XOW.

The point where ray OW meets XY is called H.  Instead of moving H along
the interior ray, lay off on the third ray OZ a point D such that

    OD ~= OH.

Then:

* SAS gives DX ~= HX;
* triangle DXY and I.20 give HY < DY;
* I.25 gives angle HOY < angle DOY;
* same-ray transport returns to the original rays OW and OZ.

Hence

    angle WOY < angle ZOY.

This is the metric-geometric core needed by Euclid XI.20.

The only spatial incidence used below is the common Hilbert-Wyler core:
three noncollinear points determine a plane, and a plane containing two
distinct points of a line contains the whole line.  Wyler I.7 itself is
not used in this proof.
-/
theorem hilbert_XI20_trihedral_remainder_less_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    [A : HilbertWylerAxioms Geo]
    (O X Y Z W : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O X Y Z)
    (hInside :
      HilbertRayMeetsSegment Geo O W X Y)
    (hAngle :
      Geo.AngleCongruent Z O X X O W) :
    HilbertAngleLess Geo W O Y Z O Y := by

  have hXOY :
      Not (PrimCollinear Geo X O Y) :=
    hTri.1

  have hYOZ :
      Not (PrimCollinear Geo Y O Z) :=
    hTri.2.1

  have hZOX :
      Not (PrimCollinear Geo Z O X) :=
    hTri.2.2.1

  have hNoncoplanar :
      Not
        (exists pi : S.Plane,
          S.OnPlane O pi /\
          S.OnPlane X pi /\
          S.OnPlane Y pi /\
          S.OnPlane Z pi) :=
    hTri.2.2.2

  --------------------------------------------------------------------
  -- H is the actual intersection of the interior ray OW with XY.
  --------------------------------------------------------------------

  rcases hInside with
    ⟨H,
      hXHY,
      hRayOWH⟩

  have hHO :
      H ≠ O :=
    hRayOWH.2.1

  have hRayOHH :
      HilbertSameRay Geo O H H :=
    hilbert_sameRay_refl
      Geo O H hHO

  have hInsideH :
      HilbertRayMeetsSegment Geo O H X Y :=
    ⟨H,
      hXHY,
      hRayOHH⟩

  have hXOH :
      Not (PrimCollinear Geo X O H) :=
    (hilbert_interior_angle_less
      Geo
      O H X Y
      hXOY
      hInsideH).1

  --------------------------------------------------------------------
  -- Lay off OD ~= OH on the third ray OZ.
  --------------------------------------------------------------------

  have hZO :
      Z ≠ O :=
    hilbert_noncollinear_ne_first
      Geo Z O X hZOX

  have hOZ :
      O ≠ Z :=
    hZO.symm

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O H
        O Z
        hOZ
    with
    ⟨D,
      hRayOZD,
      hOD_OH⟩

  have hDO :
      D ≠ O :=
    hRayOZD.2.1

  have hOD :
      O ≠ D :=
    hDO.symm

  --------------------------------------------------------------------
  -- D lies on the same ray as Z, so DOX is a proper face angle.
  --------------------------------------------------------------------

  have hDOX :
      Not (PrimCollinear Geo D O X) := by
    intro hDOXcol

    have hZOD :
        PrimCollinear Geo Z O D :=
      PrimCollinearSwap
        Geo O Z D
        hRayOZD.2.2.1

    have hODX :
        PrimCollinear Geo O D X :=
      PrimCollinearSwap
        Geo D O X hDOXcol

    have hZOXcol :
        PrimCollinear Geo Z O X :=
      hilbert_primCollinear_trans
        Geo
        Z O D X
        hOD
        hZOD
        hODX

    exact hZOX hZOXcol

  --------------------------------------------------------------------
  -- Transport the copied angle from W to H and from Z to D.
  --------------------------------------------------------------------

  have hAngleZ_D :
      Geo.Angle Z O X =
        Geo.Angle D O X :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O Z D X
      hRayOZD

  have hAngleW_H :
      Geo.Angle X O W =
        Geo.Angle X O H :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      O X W H
      hRayOWH

  have hAngleDOX_XOH :
      Geo.AngleCongruent D O X X O H := by
    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [← hAngleZ_D, ← hAngleW_H]
    exact hAngle

  --------------------------------------------------------------------
  -- SAS: DX ~= HX.
  --------------------------------------------------------------------

  have hDX_HX :
      Geo.Congruent D X H X :=
    hilbert_XI20_sas_base_congruent
      Geo
      O X D H
      hDOX
      hXOH
      hOD_OH
      hAngleDOX_XOH

  have hDX_XH :
      Geo.Congruent D X X H :=
    (Geo.congruent_reverse_second
      D X H X).mp
      hDX_HX

  --------------------------------------------------------------------
  -- The genuinely spatial point:
  -- D, X, Y cannot be collinear.
  --
  -- Otherwise D lies in the plane OXY.  Since O,D,Z are collinear
  -- and O != D, the same plane would contain Z, contradicting the
  -- trihedral noncoplanarity.
  --------------------------------------------------------------------

  have hOXY :
      Not (PrimCollinear Geo O X Y) := by
    intro h
    exact
      hXOY
        (PrimCollinearSwap
          Geo O X Y h)

  rcases
      A.plane_through
        O X Y
        hOXY
    with
    ⟨pi,
      hOpi,
      hXpi,
      hYpi⟩

  have hDXY :
      Not (PrimCollinear Geo D X Y) := by
    intro hDXYcol

    have hXYO :
        Not (PrimCollinear Geo X Y O) := by
      intro h
      exact
        hXOY
          (PrimCollinearRotate
            Geo X Y O h)

    have hXY :
        X ≠ Y :=
      hilbert_noncollinear_ne_first
        Geo X Y O hXYO

    rcases
        HilbertPlaneIncidence.line_through
          X Y hXY
    with
    ⟨l,
      hXl,
      hYl⟩

    have hXYD :
        PrimCollinear Geo X Y D :=
      PrimCollinearCycle
        Geo D X Y hDXYcol

    have hDl :
        HilbertIncidence.OnLine D l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hXY
        hXl
        hYl
        hXYD

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      A.line_in_plane
        X Y hXY
        l hXl hYl
        pi hXpi hYpi

    have hDpi :
        S.OnPlane D pi :=
      hlpi D hDl

    rcases
        HilbertPlaneIncidence.line_through
          O D hOD
    with
    ⟨m,
      hOm,
      hDm⟩

    have hODZ :
        PrimCollinear Geo O D Z :=
      PrimCollinearRotate
        Geo O Z D
        hRayOZD.2.2.1

    have hZm :
        HilbertIncidence.OnLine Z m :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hOD
        hOm
        hDm
        hODZ

    have hmpi :
        HilbertLineInPlane Geo m pi :=
      A.line_in_plane
        O D hOD
        m hOm hDm
        pi hOpi hDpi

    have hZpi :
        S.OnPlane Z pi :=
      hmpi Z hZm

    exact
      hNoncoplanar
        ⟨pi,
          hOpi,
          hXpi,
          hYpi,
          hZpi⟩

  --------------------------------------------------------------------
  -- I.20 plus cancellation: HY < DY.
  --------------------------------------------------------------------

  have hHY_DY :
      HilbertSegmentLess Geo H Y D Y :=
    hilbert_XI20_remainder_side_less
      Geo
      X Y D H
      hDXY
      hXHY
      hDX_XH

  --------------------------------------------------------------------
  -- Prepare the two proper angles HOY and DOY.
  --------------------------------------------------------------------

  have hYOX :
      Not (PrimCollinear Geo Y O X) := by
    intro h
    exact
      hXOY
        (PrimCollinearSymm
          Geo Y O X h)

  have hYHX :
      Geo.Between Y H X :=
    (HilbertOrder.between_incidence
      X H Y hXHY).2.2.2.2

  have hInsideHrev :
      HilbertRayMeetsSegment Geo O H Y X :=
    ⟨H,
      hYHX,
      hRayOHH⟩

  have hYOH :
      Not (PrimCollinear Geo Y O H) :=
    (hilbert_interior_angle_less
      Geo
      O H Y X
      hYOX
      hInsideHrev).1

  have hOHY :
      Not (PrimCollinear Geo O H Y) := by
    intro h
    have hHOY :
        PrimCollinear Geo H O Y :=
      PrimCollinearSwap
        Geo O H Y h
    exact
      hYOH
        (PrimCollinearSymm
          Geo H O Y hHOY)

  have hZOY :
      Not (PrimCollinear Geo Z O Y) := by
    intro h
    exact
      hYOZ
        (PrimCollinearSymm
          Geo Z O Y h)

  have hDOY :
      Not (PrimCollinear Geo O D Y) := by
    intro hODYcol

    have hZOD :
        PrimCollinear Geo Z O D :=
      PrimCollinearSwap
        Geo O Z D
        hRayOZD.2.2.1

    have hODY :
        PrimCollinear Geo O D Y :=
      hODYcol

    have hZOYcol :
        PrimCollinear Geo Z O Y :=
      hilbert_primCollinear_trans
        Geo
        Z O D Y
        hOD
        hZOD
        hODY

    exact hZOY hZOYcol

  --------------------------------------------------------------------
  -- I.25: angle HOY < angle DOY.
  --------------------------------------------------------------------

  have hHOY_DOY :
      HilbertAngleLess Geo H O Y D O Y :=
    hilbert_XI20_remainder_angle_less
      Geo
      O Y D H
      hDOY
      hOHY
      hOD_OH
      hHY_DY

  --------------------------------------------------------------------
  -- Return from H,D to the original rays W,Z.
  --------------------------------------------------------------------

  have hInsideWrev :
      HilbertRayMeetsSegment Geo O W Y X :=
    ⟨H,
      hYHX,
      hRayOWH⟩

  have hYOW :
      Not (PrimCollinear Geo Y O W) :=
    (hilbert_interior_angle_less
      Geo
      O W Y X
      hYOX
      hInsideWrev).1

  have hWOY :
      Not (PrimCollinear Geo W O Y) := by
    intro h
    exact
      hYOW
        (PrimCollinearSymm
          Geo W O Y h)

  have hAngleW_H_left :
      Geo.Angle W O Y =
        Geo.Angle H O Y :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O W H Y
      hRayOWH

  have hWOY_HOY :
      Geo.AngleCongruent W O Y H O Y := by
    unfold Geometry.Geo.AngleCongruent
    rw [hAngleW_H_left]
    exact
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        H O Y
        (by
          intro h
          exact
            hOHY
              (PrimCollinearSwap
                Geo H O Y h))

  have hWOY_DOY :
      HilbertAngleLess Geo W O Y D O Y :=
    hilbert_angleLess_transport_left
      Geo
      H O Y
      W O Y
      D O Y
      hHOY_DOY
      hWOY
      hWOY_HOY

  have hAngleZ_D_target :
      Geo.Angle Z O Y =
        Geo.Angle D O Y :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O Z D Y
      hRayOZD

  have hDOY_ZOY :
      Geo.AngleCongruent D O Y Z O Y := by
    unfold Geometry.Geo.AngleCongruent
    rw [hAngleZ_D_target]
    exact
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        D O Y
        (by
          intro hDOY'
          exact
            hDOY
              (PrimCollinearSwap
                Geo D O Y hDOY'))

  exact
    hilbert_angleLess_transport_right
      Geo
      W O Y
      D O Y
      Z O Y
      hWOY_DOY
      hZOY
      hDOY_ZOY

/--
XI.20, one complete cyclic inequality in the Hilbert-Wyler route.

For a proper trihedral configuration O; X,Y,Z prove

    angle ZOX + angle ZOY > angle XOY.

The proof is formally identical at the planar comparison layer to the
Hilbert route.  The only different ingredient is the remainder lemma,
whose spatial step uses the common Hilbert-Wyler incidence core.
-/
theorem hilbert_XI20_one_cyclic_inequality_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    [A : HilbertWylerAxioms Geo]
    (O X Y Z : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O X Y Z) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      Z O X
      Z O Y
      X O Y := by

  have hXOY :
      Not (PrimCollinear Geo X O Y) :=
    hTri.1

  have hYOZ :
      Not (PrimCollinear Geo Y O Z) :=
    hTri.2.1

  have hZOX :
      Not (PrimCollinear Geo Z O X) :=
    hTri.2.2.1

  have hZOY :
      Not (PrimCollinear Geo Z O Y) := by
    intro h
    exact
      hYOZ
        (PrimCollinearSymm
          Geo Z O Y h)

  rcases
      angle_trichotomy
        (Geo := Geo)
        Z O X
        X O Y
        hZOX
        hXOY
    with
    hEq | hFirstLess | hTargetLess

  ·
    have hEqTargetFirst :
        Geo.AngleCongruent X O Y Z O X :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        Z O X
        X O Y
        hEq

    exact
      hilbertTwoAnglesGreaterThanAngle_of_first_equal
        Geo
        Z O X
        Z O Y
        X O Y
        hZOX
        hZOY
        hXOY
        hEqTargetFirst

  ·
    exact
      hilbert_XI20_two_angles_greater_of_first_less
        Geo
        O X Y Z
        hFirstLess
        (fun W hInside hAngle =>
          hilbert_XI20_trihedral_remainder_less_wyler
            Geo
            O X Y Z W
            hTri
            hInside
            hAngle)

  ·
    exact
      hilbertTwoAnglesGreaterThanAngle_of_first_greater
        Geo
        Z O X
        Z O Y
        X O Y
        hZOX
        hZOY
        hXOY
        hTargetLess


/--
Euclid XI.20 in Hilbert-Wyler form.

For a proper trihedral angle with vertex O and rays OA, OB, OC,
any two face angles are together greater than the third.

The theorem uses only:
* the neutral planar metric core;
* the common point-line-plane incidence fragment of `HilbertWylerAxioms`.

In particular, the proof does not use Wyler I.7, Smith I.5, exchange,
or an ambient dimension bound.
-/
theorem euclid_proposition_11_20_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    [A : HilbertWylerAxioms Geo]
    (O A B C : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    HilbertTrihedralAngleInequalities
      Geo O A B C := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hTri.1

  have hBOC :
      Not (PrimCollinear Geo B O C) :=
    hTri.2.1

  have hCOA :
      Not (PrimCollinear Geo C O A) :=
    hTri.2.2.1

  have hNoncoplanar :
      Not
        (exists pi : S.Plane,
          S.OnPlane O pi /\
          S.OnPlane A pi /\
          S.OnPlane B pi /\
          S.OnPlane C pi) :=
    hTri.2.2.2

  have hAOC :
      Not (PrimCollinear Geo A O C) := by
    intro h
    exact
      hCOA
        (PrimCollinearSymm
          Geo A O C h)

  have hCOB :
      Not (PrimCollinear Geo C O B) := by
    intro h
    exact
      hBOC
        (PrimCollinearSymm
          Geo C O B h)

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hTri_ACB :
      HilbertTrihedralConfiguration
        Geo O A C B := by
    refine
      ⟨hAOC,
        hCOB,
        hBOA,
        ?_⟩

    rintro
      ⟨pi,
        hOpi,
        hApi,
        hCpi,
        hBpi⟩

    exact
      hNoncoplanar
        ⟨pi,
          hOpi,
          hApi,
          hBpi,
          hCpi⟩

  have hTri_BAC :
      HilbertTrihedralConfiguration
        Geo O B A C := by
    refine
      ⟨hBOA,
        hAOC,
        hCOB,
        ?_⟩

    rintro
      ⟨pi,
        hOpi,
        hBpi,
        hApi,
        hCpi⟩

    exact
      hNoncoplanar
        ⟨pi,
          hOpi,
          hApi,
          hBpi,
          hCpi⟩

  have hTri_CBA :
      HilbertTrihedralConfiguration
        Geo O C B A := by
    refine
      ⟨hCOB,
        hBOA,
        hAOC,
        ?_⟩

    rintro
      ⟨pi,
        hOpi,
        hCpi,
        hBpi,
        hApi⟩

    exact
      hNoncoplanar
        ⟨pi,
          hOpi,
          hApi,
          hBpi,
          hCpi⟩

  have h1raw :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        B O A
        B O C
        A O C :=
    hilbert_XI20_one_cyclic_inequality_wyler
      Geo
      O A C B
      hTri_ACB

  have h1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        B O C
        A O C :=
    hilbertTwoAnglesGreaterThanAngle_swap_first
      Geo
      B O A
      B O C
      A O C
      h1raw

  have h2raw :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C O B
        C O A
        B O A :=
    hilbert_XI20_one_cyclic_inequality_wyler
      Geo
      O B A C
      hTri_BAC

  have h2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        B O C
        C O A
        B O A :=
    hilbertTwoAnglesGreaterThanAngle_swap_first
      Geo
      C O B
      C O A
      B O A
      h2raw

  have h3raw :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O C
        A O B
        C O B :=
    hilbert_XI20_one_cyclic_inequality_wyler
      Geo
      O C B A
      hTri_CBA

  have h3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C O A
        A O B
        C O B :=
    hilbertTwoAnglesGreaterThanAngle_swap_first
      Geo
      A O C
      A O B
      C O B
      h3raw

  exact
    ⟨h1,
      h2,
      h3⟩

end Geometry

import CGJteamLab.Proposition11_5
import CGJteamLab.Proposition27

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Spatial symmetry of line-line perpendicularity.
-/
theorem hilbert_space_linesPerpendicularAt_symm
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m : Geo.Line)
    (O : Geo.Point)
    (hPerp :
      HilbertLinesPerpendicularAt Geo l m O) :
    HilbertLinesPerpendicularAt Geo m l O := by

  have hlm : Ne l m :=
    hilbert_linesPerpendicularAt_ne
      Geo l m O hPerp

  have hOl : H.OnLine O l :=
    hPerp.1

  have hOm : H.OnLine O m :=
    hPerp.2.1

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm
        O hOl hOm
    with
    ⟨rho, hlrho, hmrho, _hUniqueRho⟩

  let lp : PlaneLine Geo rho :=
    ⟨l, hlrho⟩

  let mp : PlaneLine Geo rho :=
    ⟨m, hmrho⟩

  let Op : PlanePoint Geo rho :=
    ⟨O, hlrho O hOl⟩

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho) lp mp Op :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      rho lp mp Op).mpr
      hPerp

  rcases hPerpPlane with
    ⟨hOlp, hOmp,
     A, B,
     hAO, hBO,
     hAlp, hBmp,
     hNonAOB,
     hRightAOB⟩

  have hNonBOA :
      Not (PrimCollinear
        (PlaneGeo Geo rho) B Op A) := by
    intro h
    exact
      hNonAOB
        (PrimCollinearSymm
          (PlaneGeo Geo rho)
          B Op A h)

  have hRightBOA :
      HilbertRightAngle
        (PlaneGeo Geo rho) B Op A :=
    hilbert_XI4_right_angle_swap
      (PlaneGeo Geo rho)
      A Op B
      hNonAOB
      hRightAOB

  have hPerpPlaneSymm :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho) mp lp Op :=
    ⟨hOmp, hOlp,
     B, A,
     hBO, hAO,
     hBmp, hAlp,
     hNonBOA,
     hRightBOA⟩

  exact
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      rho mp lp Op).mp
      hPerpPlaneSymm


/--
XI.6 auxiliary construction in the reference plane.

For distinct B,D in pi and an arbitrary ambient segment AB, construct:
* d = BD in pi,
* e through D in pi with e perpendicular to d,
* E on e with DE congruent to AB.

This is the synthetic replacement for Euclid's construction
"draw DE perpendicular to BD and make DE equal to AB".
-/
theorem hilbert_XI6_auxiliary_perpendicular_equal_segment
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B D : Geo.Point)
    (hBpi : S.OnPlane B pi)
    (hDpi : S.OnPlane D pi)
    (hBD : Ne B D) :
    exists d e : Geo.Line,
      exists E : Geo.Point,
        H.OnLine B d /\
        H.OnLine D d /\
        HilbertLineInPlane Geo d pi /\
        H.OnLine D e /\
        H.OnLine E e /\
        Ne E D /\
        HilbertLineInPlane Geo e pi /\
        HilbertLinesPerpendicularAt Geo e d D /\
        Geo.Congruent D E A B := by

  let Bp : PlanePoint Geo pi :=
    ⟨B, hBpi⟩

  let Dp : PlanePoint Geo pi :=
    ⟨D, hDpi⟩

  have hBDp : Ne Bp Dp := by
    intro h
    apply hBD
    exact congrArg Subtype.val h

  ----------------------------------------------------------------------
  -- d = BD inside PlaneGeo(pi).
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo pi)
        Bp Dp hBDp
    with
    ⟨dp, hBdp, hDdp⟩

  ----------------------------------------------------------------------
  -- Extend BD beyond D and erect a right angle at D in PlaneGeo(pi).
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo pi)
        Bp Dp hBDp
    with
    ⟨Xp, hBDX⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        (PlaneGeo Geo pi)
        Bp Dp Xp hBDX
    with
    ⟨Yp, hNonBDY, hRightBDY⟩

  have hDYp : Ne Dp Yp := by
    intro h
    subst Yp
    apply hNonBDY
    exact
      ⟨dp, hBdp, hDdp, hDdp⟩

  ----------------------------------------------------------------------
  -- e = DY inside PlaneGeo(pi).
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo pi)
        Dp Yp hDYp
    with
    ⟨ep, hDep, hYep⟩

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) dp ep Dp :=
    ⟨hDdp, hDep,
     Bp, Yp,
     hBDp, hDYp.symm,
     hBdp, hYep,
     hNonBDY,
     hRightBDY⟩

  have hPerpAmbientDE :
      HilbertLinesPerpendicularAt
        Geo dp.1 ep.1 D :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      pi dp ep Dp).mp
      hPerpPlane

  have hPerpAmbientED :
      HilbertLinesPerpendicularAt
        Geo ep.1 dp.1 D :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      dp.1 ep.1 D
      hPerpAmbientDE

  ----------------------------------------------------------------------
  -- Lay off AB on the ray DY.  The spatial congruence axiom may copy
  -- an ambient segment whose endpoint A need not lie in pi.
  ----------------------------------------------------------------------

  have hDY : Ne D Yp.1 := by
    intro h
    apply hDYp
    exact Subtype.ext h

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        A B D Yp.1 hDY
    with
    ⟨E, hRayDE, hDEAB⟩

  have hEpi : S.OnPlane E pi :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      pi
      D Yp.1 E
      hDY
      hDpi Yp.2
      hRayDE.2.2.1

  have hEe : H.OnLine E ep.1 :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hDY
      hDep
      hYep
      hRayDE.2.2.1

  exact
    ⟨dp.1, ep.1, E,
     hBdp,
     hDdp,
     dp.2,
     hDep,
     hEe,
     hRayDE.2.1,
     ep.2,
     hPerpAmbientED,
     hDEAB⟩

/--
Noncollinearity is preserved when the first arm is replaced by a point
on the same ambient ray.

This is incidence-only once the same-ray data are available.
-/
theorem hilbert_XI6_noncollinear_sameRay_first
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A A' O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRay : HilbertSameRay Geo O A A') :
    Not (PrimCollinear Geo A' O B) := by

  intro hA'OB

  have hAOA' :
      PrimCollinear Geo A O A' :=
    PrimCollinearSwap
      Geo O A A' hRay.2.2.1

  have hOA'B :
      PrimCollinear Geo O A' B :=
    PrimCollinearSwap
      Geo A' O B hA'OB

  have hAOBcol :
      PrimCollinear Geo A O B :=
    hilbert_primCollinear_trans
      Geo
      A O A' B
      hRay.2.1.symm
      hAOA'
      hOA'B

  exact hAOB hAOBcol


/--
Noncollinearity is preserved when the second arm is replaced by a point
on the same ambient ray.
-/
theorem hilbert_XI6_noncollinear_sameRay_second
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A O B B' : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRay : HilbertSameRay Geo O B B') :
    Not (PrimCollinear Geo A O B') := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm Geo B O A h)

  have hB'OA :
      Not (PrimCollinear Geo B' O A) :=
    hilbert_XI6_noncollinear_sameRay_first
      (Geo := Geo)
      B B' O A
      hBOA hRay

  intro h
  exact
    hB'OA
      (PrimCollinearSymm Geo A O B' h)


/--
Ambient angle congruence when the second arm is moved along the same ray.

The first-arm version is already available from XI.4.
-/
theorem hilbert_XI6_space_angle_sameRay_second_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A O B B' : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRay : HilbertSameRay Geo O B B') :
    Geo.AngleCongruent A O B A O B' := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm Geo B O A h)

  have hSwap :
      Geo.AngleCongruent B O A B' O A :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      B B' O A
      hBOA hRay

  have hFirst :
      Geo.AngleCongruent A O B B' O A :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      B O A
      B' O A).mp
      hSwap

  exact
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      B' O A).mp
      hFirst


/--
Spatial Hilbert Theorem 14, with the second linear-pair configuration
carried by one explicit target plane `sigma`.

If A-O-C and A'-O'-C' are linear pairs and
angle AOB is congruent to angle A'O'B', then the adjacent angles
BOC and B'O'C' are congruent.

The proof follows the existing planar Hilbert Theorem 14 proof.
All order reasoning on the source rays is performed in the explicit
source plane `rho`; all cross-plane metric comparisons use
`HilbertSpaceCongruence`.
-/
theorem hilbert_XI6_space_adjacent_angles_congruent_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (A O B C : Geo.Point)
    (A' O' B' C' : PlanePoint Geo sigma)
    (hAOC : Geo.Between A O C)
    (hA'O'C' : Geo.Between A'.1 O'.1 C'.1)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'O'B' :
      Not (PrimCollinear Geo A'.1 O'.1 B'.1))
    (hAngle :
      Geo.AngleCongruent
        A O B
        A'.1 O'.1 B'.1) :
    Geo.AngleCongruent
      B O C
      B'.1 O'.1 C'.1 := by

  have hAOCData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O C hAOC

  have hA'O'C'Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A'.1 O'.1 C'.1 hA'O'C'

  have hOA : Ne O A :=
    hAOCData.1.symm

  have hOC : Ne O C :=
    hAOCData.2.1

  have hOBA :
      Not (PrimCollinear Geo O B A) := by
    intro h
    exact
      hAOB
        (PrimCollinearCycle
          Geo B A O
          (PrimCollinearCycle
            Geo O B A h))

  have hOB : Ne O B :=
    hilbert_noncollinear_ne_first
      Geo O B A hOBA

  ----------------------------------------------------------------------
  -- Source plane rho containing A,O,B and therefore also C.
  ----------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A O B hAOB
    with
    ⟨rho, hArho, hOrho, hBrho⟩

  have hCrho : S.OnPlane C rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      A O C
      hAOCData.1
      hArho hOrho
      hAOCData.2.2.2.1

  ----------------------------------------------------------------------
  -- On the source rays lay off the three target radial segments.
  ----------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O'.1 A'.1
        O A
        hOA
    with
    ⟨X, hAX, hOX⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O'.1 B'.1
        O B
        hOB
    with
    ⟨Y, hBY, hOY⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O'.1 C'.1
        O C
        hOC
    with
    ⟨Z, hCZ, hOZ⟩

  have hXrho : S.OnPlane X rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      O A X
      hOA
      hOrho hArho
      hAX.2.2.1

  have hYrho : S.OnPlane Y rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      O B Y
      hOB
      hOrho hBrho
      hBY.2.2.1

  have hZrho : S.OnPlane Z rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      O C Z
      hOC
      hOrho hCrho
      hCZ.2.2.1

  let Ap : PlanePoint Geo rho :=
    ⟨A, hArho⟩
  let Op : PlanePoint Geo rho :=
    ⟨O, hOrho⟩
  let Bp : PlanePoint Geo rho :=
    ⟨B, hBrho⟩
  let Cp : PlanePoint Geo rho :=
    ⟨C, hCrho⟩
  let Xp : PlanePoint Geo rho :=
    ⟨X, hXrho⟩
  let Yp : PlanePoint Geo rho :=
    ⟨Y, hYrho⟩
  let Zp : PlanePoint Geo rho :=
    ⟨Z, hZrho⟩

  have hAXPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op Ap Xp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Op Ap Xp).mpr
    simpa [Op, Ap, Xp] using hAX

  have hBYPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op Bp Yp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Op Bp Yp).mpr
    simpa [Op, Bp, Yp] using hBY

  have hCZPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op Cp Zp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Op Cp Zp).mpr
    simpa [Op, Cp, Zp] using hCZ

  have hAOCPlane :
      (PlaneGeo Geo rho).Between Ap Op Cp := by
    change Geo.Between A O C
    exact hAOC

  ----------------------------------------------------------------------
  -- Normalize the source angle AOB to XOY.
  ----------------------------------------------------------------------

  have hAOB_XOB :
      Geo.AngleCongruent A O B X O B :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      A X O B
      hAOB hAX

  have hXOB :
      Not (PrimCollinear Geo X O B) :=
    hilbert_XI6_noncollinear_sameRay_first
      (Geo := Geo)
      A X O B
      hAOB hAX

  have hXOB_XOY :
      Geo.AngleCongruent X O B X O Y :=
    hilbert_XI6_space_angle_sameRay_second_congruent
      (Geo := Geo)
      X O B Y
      hXOB hBY

  have hAOB_XOY :
      Geo.AngleCongruent A O B X O Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O B
      X O B
      X O Y
      hAOB_XOB
      hXOB_XOY

  have hXOY_AOB :
      Geo.AngleCongruent X O Y A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      X O Y
      hAOB_XOY

  have hAngleXOY :
      Geo.AngleCongruent
        X O Y
        A'.1 O'.1 B'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X O Y
      A O B
      A'.1 O'.1 B'.1
      hXOY_AOB
      hAngle

  have hXOY :
      Not (PrimCollinear Geo X O Y) :=
    hilbert_XI6_noncollinear_sameRay_second
      (Geo := Geo)
      X O B Y
      hXOB hBY

  have hOXY :
      Not (PrimCollinear Geo O X Y) := by
    intro h
    exact
      hXOY
        (PrimCollinearSwap Geo O X Y h)

  have hO'A'B' :
      Not (PrimCollinear
        Geo O'.1 A'.1 B'.1) := by
    intro h
    exact
      hA'O'B'
        (PrimCollinearSwap
          Geo O'.1 A'.1 B'.1 h)

  ----------------------------------------------------------------------
  -- First spatial SAS: triangles OXY and O'A'B'.
  ----------------------------------------------------------------------

  have hFirstAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      O X Y
      O'.1 A'.1 B'.1
      hOXY
      hO'A'B'
      hOX
      hOY
      hAngleXOY

  have hO'A'B'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma)
        O' A' B') := by
    intro h
    exact
      hO'A'B'
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma O' A' B' h)

  have hFirstThird :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      O X Y
      O' A' B'
      hOXY
      hO'A'B'Plane
      hOX
      hOY
      hAngleXOY

  have hXY :
      Geo.Congruent X Y A'.1 B'.1 :=
    hFirstThird.1

  ----------------------------------------------------------------------
  -- Transport A-O-C to X-O-Z inside rho and add the two radial pieces.
  ----------------------------------------------------------------------

  have hXOZPlane :
      (PlaneGeo Geo rho).Between Xp Op Zp :=
    hilbert_between_transport_sameRays
      (PlaneGeo Geo rho)
      Ap Op Cp
      Xp Zp
      hAOCPlane
      hAXPlane
      hCZPlane

  have hXOZ :
      Geo.Between X O Z := by
    change Geo.Between X O Z at hXOZPlane
    exact hXOZPlane

  have hXO :
      Geo.Congruent X O A'.1 O'.1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      X O O'.1 A'.1).mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        O X O'.1 A'.1).mp hOX)

  have hXZ :
      Geo.Congruent X Z A'.1 C'.1 :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      X O Z
      A'.1 O'.1 C'.1
      hXOZ
      hA'O'C'
      hXO
      hOZ

  ----------------------------------------------------------------------
  -- Normalize the included angle at X.
  ----------------------------------------------------------------------

  have hZOX :
      Geo.Between Z O X :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X O Z hXOZ).2.2.2.2

  have hZOXPlane :
      (PlaneGeo Geo rho).Between Zp Op Xp := by
    change Geo.Between Z O X
    exact hZOX

  have hRayXOZPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Xp Op Zp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo rho)
      Xp Op Zp hXOZPlane

  have hRayXOZ :
      HilbertSameRay Geo X O Z := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Xp Op Zp).mp
        hRayXOZPlane
    simpa [Xp, Op, Zp] using h

  have hOXY_ZXY :
      Geo.AngleCongruent O X Y Z X Y :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      O Z X Y
      hOXY hRayXOZ

  have hAtXLeft :
      Geo.AngleCongruent O X Y Y X Z :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      O X Y
      Z X Y).mp
      hOXY_ZXY

  have hA'O'C'Plane :
      (PlaneGeo Geo sigma).Between A' O' C' := by
    change Geo.Between A'.1 O'.1 C'.1
    exact hA'O'C'

  have hRayA'O'C'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A' O' C' :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      A' O' C' hA'O'C'Plane

  have hRayA'O'C' :
      HilbertSameRay
        Geo A'.1 O'.1 C'.1 := by
    exact
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma A' O' C').mp
        hRayA'O'C'Plane

  have hO'A'B'_C'A'B' :
      Geo.AngleCongruent
        O'.1 A'.1 B'.1
        C'.1 A'.1 B'.1 :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      O'.1 C'.1 A'.1 B'.1
      hO'A'B'
      hRayA'O'C'

  have hAtXRight :
      Geo.AngleCongruent
        O'.1 A'.1 B'.1
        B'.1 A'.1 C'.1 :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      O'.1 A'.1 B'.1
      C'.1 A'.1 B'.1).mp
      hO'A'B'_C'A'B'

  have hYXZ_OXY :
      Geo.AngleCongruent Y X Z O X Y :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O X Y
      Y X Z
      hAtXLeft

  have hYXZ_O'A'B' :
      Geo.AngleCongruent
        Y X Z
        O'.1 A'.1 B'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      Y X Z
      O X Y
      O'.1 A'.1 B'.1
      hYXZ_OXY
      hFirstAngles.1

  have hAngleXYZ :
      Geo.AngleCongruent
        Y X Z
        B'.1 A'.1 C'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      Y X Z
      O'.1 A'.1 B'.1
      B'.1 A'.1 C'.1
      hYXZ_O'A'B'
      hAtXRight

  ----------------------------------------------------------------------
  -- Nondegeneracy of the second SAS triangles.
  ----------------------------------------------------------------------

  have hXYZ :
      Not (PrimCollinear Geo X Y Z) := by
    intro h

    have hXOZData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ

    have hXZY :
        PrimCollinear Geo X Z Y :=
      PrimCollinearRotate Geo X Y Z h

    have hOXYcol :
        PrimCollinear Geo O X Y :=
      hilbert_primCollinear_trans
        Geo
        O X Z Y
        hXOZData.2.2.1
        (PrimCollinearSwap
          Geo X O Z
          hXOZData.2.2.2.1)
        hXZY

    exact
      hXOY
        (PrimCollinearSwap Geo O X Y hOXYcol)

  have hA'B'C' :
      Not (PrimCollinear
        Geo A'.1 B'.1 C'.1) := by
    intro h

    have hO'A'C' :
        PrimCollinear
          Geo O'.1 A'.1 C'.1 :=
      PrimCollinearSwap
        Geo A'.1 O'.1 C'.1
        hA'O'C'Data.2.2.2.1

    have hA'C'B' :
        PrimCollinear
          Geo A'.1 C'.1 B'.1 :=
      PrimCollinearRotate
        Geo A'.1 B'.1 C'.1 h

    have hO'A'B'col :
        PrimCollinear
          Geo O'.1 A'.1 B'.1 :=
      hilbert_primCollinear_trans
        Geo
        O'.1 A'.1 C'.1 B'.1
        hA'O'C'Data.2.2.1
        hO'A'C'
        hA'C'B'

    exact
      hA'O'B'
        (PrimCollinearSwap
          Geo O'.1 A'.1 B'.1
          hO'A'B'col)

  have hA'B'C'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma)
        A' B' C') := by
    intro h
    exact
      hA'B'C'
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma A' B' C' h)

  ----------------------------------------------------------------------
  -- Second spatial SAS: triangles XYZ and A'B'C'.
  ----------------------------------------------------------------------

  have hSecond :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      X Y Z
      A' B' C'
      hXYZ
      hA'B'C'Plane
      hXY
      hXZ
      hAngleXYZ

  ----------------------------------------------------------------------
  -- Normalize the angle at Z for the final SAS.
  ----------------------------------------------------------------------

  have hRayZOXPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Zp Op Xp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo rho)
      Zp Op Xp hZOXPlane

  have hRayZOX :
      HilbertSameRay Geo Z O X := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Zp Op Xp).mp
        hRayZOXPlane
    simpa [Zp, Op, Xp] using h

  have hC'O'A' :
      Geo.Between C'.1 O'.1 A'.1 :=
    hA'O'C'Data.2.2.2.2

  have hC'O'A'Plane :
      (PlaneGeo Geo sigma).Between C' O' A' := by
    change Geo.Between C'.1 O'.1 A'.1
    exact hC'O'A'

  have hRayC'O'A'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) C' O' A' :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      C' O' A' hC'O'A'Plane

  have hRayC'O'A' :
      HilbertSameRay
        Geo C'.1 O'.1 A'.1 :=
    (planeGeo_sameRay_iff_ambient
      (Geo := Geo)
      sigma C' O' A').mp
      hRayC'O'A'Plane

  have hZOY :
      Not (PrimCollinear Geo Z O Y) := by
    intro h

    have hXOZData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ

    exact
      hXOY
        (hilbert_primCollinear_trans
          Geo
          X O Z Y
          hXOZData.2.1
          hXOZData.2.2.2.1
          (PrimCollinearSwap
            Geo Z O Y h))

  have hOZY :
      Not (PrimCollinear Geo O Z Y) := by
    intro h
    exact
      hZOY
        (PrimCollinearSwap Geo O Z Y h)

  have hOZY_XZY :
      Geo.AngleCongruent O Z Y X Z Y :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      O X Z Y
      hOZY hRayZOX

  have hO'C'B' :
      Not (PrimCollinear
        Geo O'.1 C'.1 B'.1) := by
    intro h

    have hA'O'C'col :
        PrimCollinear
          Geo A'.1 O'.1 C'.1 :=
      hA'O'C'Data.2.2.2.1

    have hA'O'B'col :
        PrimCollinear
          Geo A'.1 O'.1 B'.1 :=
      hilbert_primCollinear_trans
        Geo
        A'.1 O'.1 C'.1 B'.1
        hA'O'C'Data.2.1
        hA'O'C'col
        h

    exact hA'O'B' hA'O'B'col

  have hO'C'B'_A'C'B' :
      Geo.AngleCongruent
        O'.1 C'.1 B'.1
        A'.1 C'.1 B'.1 :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      O'.1 A'.1 C'.1 B'.1
      hO'C'B'
      hRayC'O'A'

  have hA'C'B'_O'C'B' :
      Geo.AngleCongruent
        A'.1 C'.1 B'.1
        O'.1 C'.1 B'.1 :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O'.1 C'.1 B'.1
      A'.1 C'.1 B'.1
      hO'C'B'_A'C'B'

  have hOZY_A'C'B' :
      Geo.AngleCongruent
        O Z Y
        A'.1 C'.1 B'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O Z Y
      X Z Y
      A'.1 C'.1 B'.1
      hOZY_XZY
      hSecond.2

  have hAngleOZY :
      Geo.AngleCongruent
        O Z Y
        O'.1 C'.1 B'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O Z Y
      A'.1 C'.1 B'.1
      O'.1 C'.1 B'.1
      hOZY_A'C'B'
      hA'C'B'_O'C'B'

  ----------------------------------------------------------------------
  -- Final spatial SAS.
  ----------------------------------------------------------------------

  have hC'O'B' :
      Not (PrimCollinear
        Geo C'.1 O'.1 B'.1) := by
    intro h
    exact
      hO'C'B'
        (PrimCollinearSwap
          Geo C'.1 O'.1 B'.1 h)

  have hZO :
      Geo.Congruent
        Z O C'.1 O'.1 :=
    CongruentReverseBoth
      Geo
      O Z O'.1 C'.1
      hOZ

  have hZY :
      Geo.Congruent
        Z Y C'.1 B'.1 :=
    CongruentReverseBoth
      Geo
      Y Z B'.1 C'.1
      hSecond.1

  have hFinal :
      Geo.AngleCongruent
        Z O Y
        C'.1 O'.1 B'.1 :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      Z O Y
      C'.1 O'.1 B'.1
      hZOY
      hC'O'B'
      hZO
      hZY
      hAngleOZY

  ----------------------------------------------------------------------
  -- Normalize back from ZOY to BOC and from C'O'B' to B'O'C'.
  ----------------------------------------------------------------------

  have hCOB :
      Not (PrimCollinear Geo C O B) := by
    intro h

    have hOCB :
        PrimCollinear Geo O C B :=
      PrimCollinearSwap
        Geo C O B h

    have hAOBcol :
        PrimCollinear Geo A O B :=
      hilbert_primCollinear_trans
        Geo
        A O C B
        hOC
        hAOCData.2.2.2.1
        hOCB

    exact hAOB hAOBcol

  have hCOB_ZOB :
      Geo.AngleCongruent C O B Z O B :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      C Z O B
      hCOB hCZ

  have hBOC_ZOB :
      Geo.AngleCongruent B O C Z O B :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      C O B
      Z O B).mp
      hCOB_ZOB

  have hZOB :
      Not (PrimCollinear Geo Z O B) :=
    hilbert_XI6_noncollinear_sameRay_first
      (Geo := Geo)
      C Z O B
      hCOB hCZ

  have hZOB_ZOY :
      Geo.AngleCongruent Z O B Z O Y :=
    hilbert_XI6_space_angle_sameRay_second_congruent
      (Geo := Geo)
      Z O B Y
      hZOB hBY

  have hSourceNorm :
      Geo.AngleCongruent B O C Z O Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O C
      Z O B
      Z O Y
      hBOC_ZOB
      hZOB_ZOY

  have hTargetRefl :
      Geo.AngleCongruent
        C'.1 O'.1 B'.1
        C'.1 O'.1 B'.1 :=
    HilbertSpaceCongruence.angle_congruence_reflexive
      (Geo := Geo)
      C'.1 O'.1 B'.1
      hC'O'B'

  have hTargetNorm :
      Geo.AngleCongruent
        C'.1 O'.1 B'.1
        B'.1 O'.1 C'.1 :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      C'.1 O'.1 B'.1
      C'.1 O'.1 B'.1).mp
      hTargetRefl

  have hAlmost :
      Geo.AngleCongruent
        B O C
        C'.1 O'.1 B'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O C
      Z O Y
      C'.1 O'.1 B'.1
      hSourceNorm
      hFinal

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O C
      C'.1 O'.1 B'.1
      B'.1 O'.1 C'.1
      hAlmost
      hTargetNorm


/--
Spatial Hilbert Theorem 21: all nondegenerate right angles are congruent.

The source right angle is ambient.  The target right angle is carried by
one explicit plane `sigma`.

The proof copies the source angle onto the target base ray, uses the
spatial Hilbert Theorem 14 proved above to show that the copied angle is
again right, and then uses uniqueness of the perpendicular direction in
the target `PlaneGeo` together with the same-side information from angle
construction.
-/
theorem hilbert_XI6_space_right_angles_congruent_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (A O B : Geo.Point)
    (A' O' B' : PlanePoint Geo sigma)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'O'B' :
      Not (PrimCollinear Geo A'.1 O'.1 B'.1))
    (hRightA : HilbertRightAngle Geo A O B)
    (hRightB :
      HilbertRightAngle Geo A'.1 O'.1 B'.1) :
    Geo.AngleCongruent
      A O B
      A'.1 O'.1 B'.1 := by

  ----------------------------------------------------------------------
  -- Expose the two supplementary witnesses from the definitions of
  -- the two right angles.
  ----------------------------------------------------------------------

  rcases hRightA with
    ⟨C, hAOC, hRightAeq⟩

  rcases hRightB with
    ⟨C0, hA'O'C0, hRightBeq⟩

  have hA'O'C0Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A'.1 O'.1 C0 hA'O'C0

  have hA'O' : Ne A'.1 O'.1 :=
    hA'O'C0Data.1

  have hO'C0 : Ne O'.1 C0 :=
    hA'O'C0Data.2.1

  have hC0sigma : S.OnPlane C0 sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      A'.1 O'.1 C0
      hA'O'
      A'.2 O'.2
      hA'O'C0Data.2.2.2.1

  let C0p : PlanePoint Geo sigma :=
    ⟨C0, hC0sigma⟩

  ----------------------------------------------------------------------
  -- The target base line A'O' inside sigma.
  ----------------------------------------------------------------------

  have hA'O'p : Ne A' O' := by
    intro h
    apply hA'O'
    exact congrArg Subtype.val h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        A' O' hA'O'p
    with
    ⟨basep, hA'base, hO'base⟩

  have hB'off :
      Not (H.OnLine B'.1 basep.1) := by
    intro hB'base
    exact
      hA'O'B'
        ⟨basep.1,
         hA'base,
         hO'base,
         hB'base⟩

  ----------------------------------------------------------------------
  -- Copy the source angle AOB onto the target ray O'A', choosing the
  -- half-plane containing B'.
  ----------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        A O B
        A'.1 O'.1 B'.1
        hAOB
        hA'O'
        sigma
        basep.1
        basep.2
        hA'base
        hO'base
        B'.2
        hB'off
    with
    ⟨K, hKBSpace, hCopy, _hUniqueCopy⟩

  have hKsigma : S.OnPlane K sigma :=
    hKBSpace.1

  let Kp : PlanePoint Geo sigma :=
    ⟨K, hKsigma⟩

  have hKoff :
      Not (H.OnLine K basep.1) :=
    hKBSpace.2.2.1

  have hA'O'K :
      Not (PrimCollinear Geo A'.1 O'.1 K) := by
    intro hCol

    have hKbase :
        H.OnLine K basep.1 :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hA'O'
        hA'base
        hO'base
        hCol

    exact hKoff hKbase

  ----------------------------------------------------------------------
  -- Hilbert 14: the supplementary angle to the copied angle is
  -- congruent to the supplementary angle to the source angle.
  ----------------------------------------------------------------------

  have hSupp :
      Geo.AngleCongruent
        B O C
        K O'.1 C0 :=
    hilbert_XI6_space_adjacent_angles_congruent_in_plane
      (Geo := Geo)
      sigma
      A O B C
      A' O' Kp C0p
      hAOC
      hA'O'C0
      hAOB
      hA'O'K
      hCopy

  have hCopySym :
      Geo.AngleCongruent
        A'.1 O'.1 K
        A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      A'.1 O'.1 K
      hCopy

  have hK_AFC :
      Geo.AngleCongruent
        A'.1 O'.1 K
        B O C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A'.1 O'.1 K
      A O B
      B O C
      hCopySym
      hRightAeq

  have hKRightEq :
      Geo.AngleCongruent
        A'.1 O'.1 K
        K O'.1 C0 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A'.1 O'.1 K
      B O C
      K O'.1 C0
      hK_AFC
      hSupp

  have hRightK :
      HilbertRightAngle
        Geo A'.1 O'.1 K :=
    ⟨C0, hA'O'C0, hKRightEq⟩

  ----------------------------------------------------------------------
  -- Pull both right angles into PlaneGeo(sigma).
  ----------------------------------------------------------------------

  have hA'O'KPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' O' Kp) := by
    intro h
    exact
      hA'O'K
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma A' O' Kp h)

  have hA'O'B'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' O' B') := by
    intro h
    exact
      hA'O'B'
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma A' O' B' h)

  have hRightKPlane :
      HilbertRightAngle
        (PlaneGeo Geo sigma) A' O' Kp :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma A' O' Kp).mpr
      hRightK

  have hRightBPlane :
      HilbertRightAngle
        (PlaneGeo Geo sigma) A' O' B' :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma A' O' B').mpr
      ⟨C0, hA'O'C0, hRightBeq⟩

  ----------------------------------------------------------------------
  -- In one plane, two right-angle second arms from the same first arm
  -- are collinear.
  ----------------------------------------------------------------------

  have hKBcol :
      PrimCollinear
        (PlaneGeo Geo sigma) Kp O' B' :=
    hilbert_XI4_two_right_angles_same_first_arm_collinear
      (PlaneGeo Geo sigma)
      A' O' Kp B'
      basep
      hA'O'p
      hA'base
      hO'base
      hA'O'KPlane
      hA'O'B'Plane
      hRightKPlane
      hRightBPlane

  ----------------------------------------------------------------------
  -- Angle construction put K and B' in the same half-plane bounded by
  -- A'O'.  Together with their collinearity with O', this rules out
  -- O' lying between them, hence they determine the same ray.
  ----------------------------------------------------------------------

  have hKBSamePlane :
      HilbertSameSide
        (PlaneGeo Geo sigma)
        Kp B' basep :=
    (planeGeo_sameSide_iff_space
      (Geo := Geo)
      sigma Kp B' basep).mpr
      hKBSpace

  have hKO' : Ne Kp O' := by
    intro h
    have hKOval : K = O'.1 :=
      congrArg Subtype.val h
    subst K
    exact hKoff hO'base

  have hB'O' : Ne B' O' := by
    intro h
    have hB'Oval : B'.1 = O'.1 :=
      congrArg Subtype.val h
    subst B'
    exact hB'off hO'base

  have hNotBetween :
      Not ((PlaneGeo Geo sigma).Between Kp O' B') := by
    intro hBetween

    have hOpp :
        HilbertOppositeSide
          (PlaneGeo Geo sigma)
          Kp B' basep :=
      ⟨hKBSamePlane.1,
       hKBSamePlane.2.1,
       ⟨O', hBetween, hO'base⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        (PlaneGeo Geo sigma)
        Kp B' basep
        hOpp)
        hKBSamePlane

  have hRayKBPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma)
        O' Kp B' :=
    ⟨hKO',
     hB'O',
     PrimCollinearSwap
       (PlaneGeo Geo sigma)
       Kp O' B' hKBcol,
     hNotBetween⟩

  have hRayKB :
      HilbertSameRay
        Geo O'.1 K B'.1 :=
    (planeGeo_sameRay_iff_ambient
      (Geo := Geo)
      sigma O' Kp B').mp
      hRayKBPlane

  ----------------------------------------------------------------------
  -- Replace the copied second arm K by the target second arm B'.
  ----------------------------------------------------------------------

  have hCopyToTarget :
      Geo.AngleCongruent
        A'.1 O'.1 K
        A'.1 O'.1 B'.1 :=
    hilbert_XI6_space_angle_sameRay_second_congruent
      (Geo := Geo)
      A'.1 O'.1 K B'.1
      hA'O'K
      hRayKB

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O B
      A'.1 O'.1 K
      A'.1 O'.1 B'.1
      hCopy
      hCopyToTarget


/--
Spatial normalization of line-line perpendicularity to arbitrary chosen
nonvertex points on the two carriers.

This is the ambient 3D wrapper around the planar XI.4 normalizer.
-/
theorem hilbert_XI6_space_linesPerpendicularAt_right_angle_of_points
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m : Geo.Line)
    (O A B : Geo.Point)
    (hPerp : HilbertLinesPerpendicularAt Geo l m O)
    (hAO : Ne A O)
    (hBO : Ne B O)
    (hAl : H.OnLine A l)
    (hBm : H.OnLine B m) :
    Not (PrimCollinear Geo A O B) /\
    HilbertRightAngle Geo A O B := by

  have hlm : Ne l m :=
    hilbert_linesPerpendicularAt_ne
      Geo l m O hPerp

  have hOl : H.OnLine O l :=
    hPerp.1

  have hOm : H.OnLine O m :=
    hPerp.2.1

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm
        O hOl hOm
    with
    ⟨rho, hlrho, hmrho, _hUnique⟩

  let lp : PlaneLine Geo rho :=
    ⟨l, hlrho⟩

  let mp : PlaneLine Geo rho :=
    ⟨m, hmrho⟩

  let Op : PlanePoint Geo rho :=
    ⟨O, hlrho O hOl⟩

  let Ap : PlanePoint Geo rho :=
    ⟨A, hlrho A hAl⟩

  let Bp : PlanePoint Geo rho :=
    ⟨B, hmrho B hBm⟩

  have hAOPlane : Ne Ap Op := by
    intro h
    apply hAO
    exact congrArg Subtype.val h

  have hBOPlane : Ne Bp Op := by
    intro h
    apply hBO
    exact congrArg Subtype.val h

  have hlpmp : Ne lp mp := by
    intro h
    apply hlm
    exact congrArg Subtype.val h

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho) lp mp Op :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      rho lp mp Op).mpr
      hPerp

  have hNorm :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      lp mp
      Op Ap Bp
      hlpmp
      hPerpPlane
      hAOPlane
      hBOPlane
      hAl
      hBm

  have hNonAmbient :
      Not (PrimCollinear Geo A O B) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      rho Ap Op Bp hNorm.1

  have hRightAmbient :
      HilbertRightAngle Geo A O B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      rho Ap Op Bp).mp
      hNorm.2

  exact ⟨hNonAmbient, hRightAmbient⟩



/--
First metric step of Euclid XI.6.

Let l be perpendicular to pi at B and let D be a second point of pi.
Choose A != B on l.  In pi construct d = BD and e through D
perpendicular to d, then lay off DE congruent AB.

Spatial SAS on triangles BAD and DEB gives

    AD congruent EB.

The theorem returns the whole auxiliary configuration because the next
XI.6 step (spatial SSS) reuses it.
-/
theorem hilbert_XI6_first_SAS
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l : Geo.Line)
    (B D : Geo.Point)
    (hDpi : S.OnPlane D pi)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B) :
    exists A d e E,
      Ne A B /\
      H.OnLine A l /\
      H.OnLine B d /\
      H.OnLine D d /\
      HilbertLineInPlane Geo d pi /\
      H.OnLine D e /\
      H.OnLine E e /\
      Ne E D /\
      HilbertLineInPlane Geo e pi /\
      HilbertLinesPerpendicularAt Geo e d D /\
      Geo.Congruent D E A B /\
      Geo.Congruent A D E B := by

  have hBpi : S.OnPlane B pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).2

  have hBl : H.OnLine B l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).1

  ----------------------------------------------------------------------
  -- Choose A on the first normal l.
  ----------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l B
    with
    ⟨A, hAB, hAl⟩

  ----------------------------------------------------------------------
  -- Euclid's auxiliary construction in pi:
  -- d = BD, e through D perpendicular d, DE ~= AB.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI6_auxiliary_perpendicular_equal_segment
        (Geo := Geo)
        pi
        A B D
        hBpi hDpi hBD
    with
    ⟨d, e, E,
     hBd, hDd, hdpi,
     hDe, hEe, hED,
     hepi, hPerpED, hDEAB⟩

  have hDE : Ne D E :=
    hED.symm

  have hEpi : S.OnPlane E pi :=
    hepi E hEe

  ----------------------------------------------------------------------
  -- l is perpendicular to d at B because d lies in pi.
  ----------------------------------------------------------------------

  have hPerpLd :
      HilbertLinesPerpendicularAt Geo l d B :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hLperp
      hdpi
      hBd

  ----------------------------------------------------------------------
  -- Normalize both perpendicularities to the points A,B,D,E.
  ----------------------------------------------------------------------

  have hABD :=
    hilbert_XI6_space_linesPerpendicularAt_right_angle_of_points
      (Geo := Geo)
      l d
      B A D
      hPerpLd
      hAB
      hBD.symm
      hAl
      hDd

  have hNonABD :
      Not (PrimCollinear Geo A B D) :=
    hABD.1

  have hRightABD :
      HilbertRightAngle Geo A B D :=
    hABD.2

  have hEDB :=
    hilbert_XI6_space_linesPerpendicularAt_right_angle_of_points
      (Geo := Geo)
      e d
      D E B
      hPerpED
      hED
      hBD
      hEe
      hBd

  have hNonEDB :
      Not (PrimCollinear Geo E D B) :=
    hEDB.1

  have hRightEDB :
      HilbertRightAngle Geo E D B :=
    hEDB.2

  ----------------------------------------------------------------------
  -- Target triangle DEB lives in pi.
  ----------------------------------------------------------------------

  let Dp : PlanePoint Geo pi :=
    ⟨D, hDpi⟩

  let Ep : PlanePoint Geo pi :=
    ⟨E, hEpi⟩

  let Bp : PlanePoint Geo pi :=
    ⟨B, hBpi⟩

  have hNonDEB :
      Not (PrimCollinear Geo D E B) := by
    intro h
    exact
      hNonEDB
        (PrimCollinearSwap Geo D E B h)

  have hNonDEBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo pi) Dp Ep Bp) := by
    intro h
    exact
      hNonDEB
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi Dp Ep Bp h)

  ----------------------------------------------------------------------
  -- The included right angles are congruent by spatial Hilbert 21.
  ----------------------------------------------------------------------

  have hAngle :
      Geo.AngleCongruent
        A B D
        E D B :=
    hilbert_XI6_space_right_angles_congruent_in_plane
      (Geo := Geo)
      pi
      A B D
      Ep Dp Bp
      hNonABD
      hNonEDB
      hRightABD
      hRightEDB

  ----------------------------------------------------------------------
  -- Corresponding sides for SAS:
  -- BA ~= DE and BD ~= DB.
  ----------------------------------------------------------------------

  have hABDE :
      Geo.Congruent A B D E :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      D E A B
      hDE
      hDEAB

  have hBADE :
      Geo.Congruent B A D E :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      A B D E).mp
      hABDE

  have hBDBD :
      Geo.Congruent B D B D :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      B D hBD

  have hBDDB :
      Geo.Congruent B D D B :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B D B D).mp
      hBDBD

  have hNonBAD :
      Not (PrimCollinear Geo B A D) := by
    intro h
    exact
      hNonABD
        (PrimCollinearSwap Geo B A D h)

  ----------------------------------------------------------------------
  -- Spatial SAS:
  --
  --   triangle BAD
  --   triangle DEB
  --
  -- gives AD ~= EB.
  ----------------------------------------------------------------------

  have hSAS :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      pi
      B A D
      Dp Ep Bp
      hNonBAD
      hNonDEBPlane
      hBADE
      hBDDB
      hAngle

  exact
    ⟨A, d, e, E,
     hAB,
     hAl,
     hBd,
     hDd,
     hdpi,
     hDe,
     hEe,
     hED,
     hepi,
     hPerpED,
     hDEAB,
     hSAS.1⟩


/--
Transport rightness from an ambient right angle to a congruent angle
carried by one explicit target plane.

No global `HilbertCongruence Geo` instance is installed.  Instead we:
* construct an auxiliary right angle inside the target `PlaneGeo`;
* compare it with the ambient source right angle by spatial Hilbert 21;
* perform the actual right-angle transport inside the target plane.
-/
theorem hilbert_XI6_space_right_angle_transport_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (A O B : Geo.Point)
    (A' O' B' : PlanePoint Geo sigma)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'O'B' :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' O' B'))
    (hRight : HilbertRightAngle Geo A O B)
    (hAngle :
      Geo.AngleCongruent
        A O B
        A'.1 O'.1 B'.1) :
    HilbertRightAngle Geo A'.1 O'.1 B'.1 := by

  have hA'O'B'Ambient :
      Not (PrimCollinear Geo A'.1 O'.1 B'.1) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma A' O' B' hA'O'B'

  have hA'O' : Ne A' O' :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo sigma)
      A' O' B'
      hA'O'B'

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo sigma)
        A' O' hA'O'
    with
    ⟨C', hA'O'C'⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        (PlaneGeo Geo sigma)
        A' O' C' hA'O'C'
    with
    ⟨X', hNonAuxPlane, hRightAuxPlane⟩

  have hRightAuxAmbient :
      HilbertRightAngle
        Geo A'.1 O'.1 X'.1 :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma A' O' X').mp
      hRightAuxPlane

  have hNonAuxAmbient :
      Not (PrimCollinear
        Geo A'.1 O'.1 X'.1) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma A' O' X' hNonAuxPlane

  have hSourceAux :
      Geo.AngleCongruent
        A O B
        A'.1 O'.1 X'.1 :=
    hilbert_XI6_space_right_angles_congruent_in_plane
      (Geo := Geo)
      sigma
      A O B
      A' O' X'
      hAOB
      hNonAuxAmbient
      hRight
      hRightAuxAmbient

  have hTargetSource :
      Geo.AngleCongruent
        A'.1 O'.1 B'.1
        A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      A'.1 O'.1 B'.1
      hAngle

  have hTargetAuxAmbient :
      Geo.AngleCongruent
        A'.1 O'.1 B'.1
        A'.1 O'.1 X'.1 :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A'.1 O'.1 B'.1
      A O B
      A'.1 O'.1 X'.1
      hTargetSource
      hSourceAux

  have hAuxTargetAmbient :
      Geo.AngleCongruent
        A'.1 O'.1 X'.1
        A'.1 O'.1 B'.1 :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A'.1 O'.1 B'.1
      A'.1 O'.1 X'.1
      hTargetAuxAmbient

  have hAuxTargetPlane :
      (PlaneGeo Geo sigma).AngleCongruent
        A' O' X'
        A' O' B' :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      sigma
      A' O' X'
      A' O' B').mpr
      hAuxTargetAmbient

  have hRightTargetPlane :
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        A' O' B' :=
    hilbert_right_angle_transport
      (PlaneGeo Geo sigma)
      A' O' X'
      A' O' B'
      hNonAuxPlane
      hA'O'B'
      hRightAuxPlane
      hAuxTargetPlane

  exact
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma A' O' B').mp
      hRightTargetPlane


/--
Second metric step of Euclid XI.6.

Starting from the auxiliary configuration and the first SAS conclusion

    AD congruent EB,

the triangles

    DEA
    BAE

have three corresponding congruent sides:

    DE congruent BA,
    EA congruent AE,
    DA congruent BE.

Spatial SSS therefore gives

    angle EDA congruent angle ABE.

Since AB is perpendicular to the reference plane pi and BE lies in pi,
angle ABE is right.  Hence angle EDA is right as well.
-/
theorem hilbert_XI6_second_SSS_right_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l : Geo.Line)
    (B D : Geo.Point)
    (hDpi : S.OnPlane D pi)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B) :
    exists A d e E,
      Ne A B /\
      H.OnLine A l /\
      H.OnLine B d /\
      H.OnLine D d /\
      HilbertLineInPlane Geo d pi /\
      H.OnLine D e /\
      H.OnLine E e /\
      Ne E D /\
      HilbertLineInPlane Geo e pi /\
      HilbertLinesPerpendicularAt Geo e d D /\
      Geo.Congruent D E A B /\
      Geo.Congruent A D E B /\
      HilbertRightAngle Geo E D A := by

  rcases
      hilbert_XI6_first_SAS
        (Geo := Geo)
        pi l B D
        hDpi hBD hLperp
    with
    ⟨A, d, e, E,
     hAB, hAl,
     hBd, hDd, hdpi,
     hDe, hEe, hED,
     hepi, hPerpED,
     hDEAB, hADEB⟩

  have hBpi : S.OnPlane B pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).2

  have hEpi : S.OnPlane E pi :=
    hepi E hEe

  ----------------------------------------------------------------------
  -- Build the plane line g = BE inside pi.
  ----------------------------------------------------------------------

  have hBE : Ne B E := by
    intro hEq
    subst E

    have hEDB :=
      hilbert_XI6_space_linesPerpendicularAt_right_angle_of_points
        (Geo := Geo)
        e d
        D B B
        hPerpED
        hED
        hBD
        hEe
        hBd

    exact hEDB.1
      ⟨d, hBd, hDd, hBd⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        B E hBE
    with
    ⟨g, hBg, hEg⟩

  have hgpi :
      HilbertLineInPlane Geo g pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B E hBE
      g hBg hEg
      pi hBpi hEpi

  ----------------------------------------------------------------------
  -- AB is perpendicular to every plane line through B, hence to BE.
  ----------------------------------------------------------------------

  have hPerpLg :
      HilbertLinesPerpendicularAt Geo l g B :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hLperp
      hgpi
      hBg

  have hABE :=
    hilbert_XI6_space_linesPerpendicularAt_right_angle_of_points
      (Geo := Geo)
      l g
      B A E
      hPerpLg
      hAB
      hBE.symm
      hAl
      hEg

  have hNonABE :
      Not (PrimCollinear Geo A B E) :=
    hABE.1

  have hRightABE :
      HilbertRightAngle Geo A B E :=
    hABE.2

  have hNonBAE :
      Not (PrimCollinear Geo B A E) := by
    intro h
    exact
      hNonABE
        (PrimCollinearSwap Geo B A E h)

  ----------------------------------------------------------------------
  -- The target triangle BAE has its own explicit carrier plane sigma.
  ----------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        B A E hNonBAE
    with
    ⟨sigma, hBsigma, hAsigma, hEsigma⟩

  let Bsigma : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Asigma : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let Esigma : PlanePoint Geo sigma :=
    ⟨E, hEsigma⟩

  have hNonBAEPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma)
        Bsigma Asigma Esigma) := by
    intro h
    exact
      hNonBAE
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma Bsigma Asigma Esigma h)

  ----------------------------------------------------------------------
  -- A is not in the reference plane pi.
  ----------------------------------------------------------------------

  have hlNotPi :
      Not (HilbertLineInPlane Geo l pi) :=
    hilbert_linePerpendicularPlaneAt_not_in_plane
      (Geo := Geo)
      l pi B hLperp

  have hApi : Not (S.OnPlane A pi) := by
    intro hApi

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        A B hAB
        l hAl
        (HilbertLinePerpendicularPlaneAt.incidence
          (Geo := Geo)
          hLperp).1
        pi hApi hBpi

    exact hlNotPi hlpi

  ----------------------------------------------------------------------
  -- Therefore D,E,A are noncollinear: D and E lie in pi, A does not.
  ----------------------------------------------------------------------

  have hDE : Ne D E :=
    hED.symm

  have hNonDEA :
      Not (PrimCollinear Geo D E A) := by
    intro hDEA

    have hAe : H.OnLine A e :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hDE
        hDe
        hEe
        hDEA

    exact hApi (hepi A hAe)

  ----------------------------------------------------------------------
  -- Three corresponding sides for SSS.
  ----------------------------------------------------------------------

  have hDEBA :
      Geo.Congruent D E B A :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      D E A B).mp
      hDEAB

  have hEAEA :
      Geo.Congruent E A E A :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      E A
      (by
        intro hEq
        subst A
        exact hApi hEpi)

  have hEAAE :
      Geo.Congruent E A A E :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      E A E A).mp
      hEAEA

  have hDAEB :
      Geo.Congruent D A E B :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      A D E B).mp
      hADEB

  have hDABE :
      Geo.Congruent D A B E :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      D A E B).mp
      hDAEB

  ----------------------------------------------------------------------
  -- Spatial SSS:
  --
  --   source: DEA
  --   target: BAE  (carried by sigma)
  --
  -- gives angle EDA ~= ABE.
  ----------------------------------------------------------------------

  have hSSS :=
    hilbert_space_sss_angleA_in_plane
      (Geo := Geo)
      sigma
      D E A
      Bsigma Asigma Esigma
      hNonDEA
      hNonBAEPlane
      hDEBA
      hEAAE
      hDABE

  have hAngleEDA_ABE :
      Geo.AngleCongruent E D A A B E :=
    hSSS

  have hAngleABE_EDA :
      Geo.AngleCongruent A B E E D A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E D A
      A B E
      hAngleEDA_ABE

  have hNonEDA :
      Not (PrimCollinear Geo E D A) := by
    intro h
    exact
      hNonDEA
        (PrimCollinearSwap Geo E D A h)

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        E D A hNonEDA
    with
    ⟨tau, hEtau, hDtau, hAtau⟩

  let Etau : PlanePoint Geo tau :=
    ⟨E, hEtau⟩

  let Dtau : PlanePoint Geo tau :=
    ⟨D, hDtau⟩

  let Atau : PlanePoint Geo tau :=
    ⟨A, hAtau⟩

  have hNonEDAPlane :
      Not (PrimCollinear
        (PlaneGeo Geo tau) Etau Dtau Atau) := by
    intro h
    exact
      hNonEDA
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          tau Etau Dtau Atau h)

  have hRightEDA :
      HilbertRightAngle Geo E D A :=
    hilbert_XI6_space_right_angle_transport_in_plane
      (Geo := Geo)
      tau
      A B E
      Etau Dtau Atau
      hNonABE
      hNonEDAPlane
      hRightABE
      hAngleABE_EDA

  exact
    ⟨A, d, e, E,
     hAB,
     hAl,
     hBd,
     hDd,
     hdpi,
     hDe,
     hEe,
     hED,
     hepi,
     hPerpED,
     hDEAB,
     hADEB,
     hRightEDA⟩


/--
Core coplanarity step of Euclid XI.6.

If l and m are perpendicular to the same plane pi at distinct feet
B and D, then l and m are coplanar.

This is the exact place where Proposition XI.5 enters the proof.

The construction provides:
* d = BD in pi,
* e through D in pi with e perpendicular d,
* A on l,
* a = DA,
* e perpendicular a, from the preceding SAS/SSS argument,
* e perpendicular m, because m is perpendicular to pi.

Thus e is perpendicular at D to the three lines d, a, m.
Proposition XI.5 puts d, a, m in one plane sigma.  Since sigma contains
A and B, it also contains l.
-/
theorem hilbert_XI6_normals_to_same_plane_coplanar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B)
    (hMperp :
      HilbertLinePerpendicularPlaneAt
        Geo m pi D) :
    exists sigma : S.Plane,
      HilbertLineInPlane Geo l sigma /\
      HilbertLineInPlane Geo m sigma := by

  rcases
      hilbert_XI6_second_SSS_right_angle
        (Geo := Geo)
        pi l B D
        (HilbertLinePerpendicularPlaneAt.incidence
          (Geo := Geo)
          hMperp).2
        hBD
        hLperp
    with
    ⟨A, d, e, E,
     hAB, hAl,
     hBd, hDd, hdpi,
     hDe, hEe, hED,
     hepi, hPerpED,
     hDEAB, hADEB,
     hRightEDA⟩

  have hBpi : S.OnPlane B pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).2

  have hBl : H.OnLine B l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).1

  have hDpi : S.OnPlane D pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hMperp).2

  have hDm : H.OnLine D m :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hMperp).1

  ----------------------------------------------------------------------
  -- A is outside the reference plane pi.
  ----------------------------------------------------------------------

  have hlNotPi :
      Not (HilbertLineInPlane Geo l pi) :=
    hilbert_linePerpendicularPlaneAt_not_in_plane
      (Geo := Geo)
      l pi B hLperp

  have hApi : Not (S.OnPlane A pi) := by
    intro hApi

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        A B hAB
        l hAl hBl
        pi hApi hBpi

    exact hlNotPi hlpi

  have hAD : Ne A D := by
    intro hEq
    subst A
    exact hApi hDpi

  have hDA : Ne D A :=
    hAD.symm

  ----------------------------------------------------------------------
  -- a = DA.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        D A hDA
    with
    ⟨a, hDa, hAa⟩

  ----------------------------------------------------------------------
  -- e perpendicular a at D, using the right angle EDA obtained above.
  ----------------------------------------------------------------------

  have hDE : Ne D E :=
    hED.symm

  have hNonEDA :
      Not (PrimCollinear Geo E D A) := by
    intro hEDA

    have hDEA :
        PrimCollinear Geo D E A :=
      PrimCollinearSwap
        Geo E D A hEDA

    have hAe : H.OnLine A e :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hDE
        hDe
        hEe
        hDEA

    exact hApi (hepi A hAe)

  have hPerpEA :
      HilbertLinesPerpendicularAt
        Geo e a D :=
    ⟨hDe, hDa,
     E, A,
     hED, hAD,
     hEe, hAa,
     hNonEDA,
     hRightEDA⟩

  ----------------------------------------------------------------------
  -- e perpendicular m at D because e lies in pi.
  ----------------------------------------------------------------------

  have hPerpME :
      HilbertLinesPerpendicularAt
        Geo m e D :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hMperp
      hepi
      hDe

  have hPerpEM :
      HilbertLinesPerpendicularAt
        Geo e m D :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      m e D
      hPerpME

  ----------------------------------------------------------------------
  -- d and a are distinct.  Otherwise A would lie on d and hence in pi.
  ----------------------------------------------------------------------

  have hda : Ne d a := by
    intro hEq
    subst a
    exact hApi (hdpi A hAa)

  ----------------------------------------------------------------------
  -- XI.5: d, a, m are coplanar.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_5
        (Geo := Geo)
        e d a m
        D
        hda
        hPerpED
        hPerpEA
        hPerpEM
    with
    ⟨sigma,
     hdsigma,
     hasigma,
     hmsigma⟩

  ----------------------------------------------------------------------
  -- sigma contains A (on a) and B (on d), hence it contains l = AB.
  ----------------------------------------------------------------------

  have hAsigma : S.OnPlane A sigma :=
    hasigma A hAa

  have hBsigma : S.OnPlane B sigma :=
    hdsigma B hBd

  have hlsigma :
      HilbertLineInPlane Geo l sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      sigma hAsigma hBsigma

  exact
    ⟨sigma,
     hlsigma,
     hmsigma⟩


/--
Two ambient spatial lines are parallel when they are coplanar and
disjoint.

The coplanarity clause is essential: ambient disjointness alone would
also classify skew lines as parallel.
-/
def HilbertSpaceLinesParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l m : Geo.Line) : Prop :=
  exists sigma : S.Plane,
    HilbertLineInPlane Geo l sigma /\
    HilbertLineInPlane Geo m sigma /\
    HilbertLinesDisjoint Geo l m


/--
Planar end of Euclid XI.6 after the spatial coplanarity step.

Two coplanar lines perpendicular to the same transversal at distinct
feet are disjoint.

The proof is carried out entirely inside `PlaneGeo sigma` and concludes
with Euclid I.27.
-/
theorem hilbert_XI6_coplanar_normals_disjoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi sigma : S.Plane)
    (l m : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hlsigma : HilbertLineInPlane Geo l sigma)
    (hmsigma : HilbertLineInPlane Geo m sigma)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B)
    (hMperp :
      HilbertLinePerpendicularPlaneAt
        Geo m pi D) :
    HilbertLinesDisjoint Geo l m := by

  have hBl : H.OnLine B l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).1

  have hDm : H.OnLine D m :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hMperp).1

  have hBpi : S.OnPlane B pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hLperp).2

  have hDpi : S.OnPlane D pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hMperp).2

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hDsigma : S.OnPlane D sigma :=
    hmsigma D hDm

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Dp : PlanePoint Geo sigma :=
    ⟨D, hDsigma⟩

  have hBDp : Ne Bp Dp := by
    intro h
    apply hBD
    exact congrArg Subtype.val h

  ----------------------------------------------------------------------
  -- d = BD inside sigma.  Since B,D also lie in pi, the same ambient
  -- line d lies in the reference plane pi.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        Bp Dp hBDp
    with
    ⟨dp, hBdp, hDdp⟩

  have hdpi :
      HilbertLineInPlane Geo dp.1 pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B D hBD
      dp.1 hBdp hDdp
      pi hBpi hDpi

  ----------------------------------------------------------------------
  -- Both normals are perpendicular to d.
  ----------------------------------------------------------------------

  have hPerpLd :
      HilbertLinesPerpendicularAt Geo l dp.1 B :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hLperp
      hdpi
      hBdp

  have hPerpMd :
      HilbertLinesPerpendicularAt Geo m dp.1 D :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hMperp
      hdpi
      hDdp

  let lp : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  let mp : PlaneLine Geo sigma :=
    ⟨m, hmsigma⟩

  have hPerpLpDp :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma) lp dp Bp :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma lp dp Bp).mpr
      hPerpLd

  have hPerpMpDp :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma) mp dp Dp :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma mp dp Dp).mpr
      hPerpMd

  ----------------------------------------------------------------------
  -- Choose one nonfoot point A on l and one nonfoot point C on m.
  ----------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l B
    with
    ⟨A, hAB, hAl⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        m D
    with
    ⟨C, hCD, hCm⟩

  have hAsigma : S.OnPlane A sigma :=
    hlsigma A hAl

  have hCsigma : S.OnPlane C sigma :=
    hmsigma C hCm

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨C, hCsigma⟩

  have hABp : Ne Ap Bp := by
    intro h
    apply hAB
    exact congrArg Subtype.val h

  have hCDp : Ne Cp Dp := by
    intro h
    apply hCD
    exact congrArg Subtype.val h

  have hNormA :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo sigma)
      lp dp
      Bp Ap Dp
      (hilbert_linesPerpendicularAt_ne
        (PlaneGeo Geo sigma)
        lp dp Bp hPerpLpDp)
      hPerpLpDp
      hABp
      hBDp.symm
      hAl
      hDdp

  have hNormC :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo sigma)
      mp dp
      Dp Cp Bp
      (hilbert_linesPerpendicularAt_ne
        (PlaneGeo Geo sigma)
        mp dp Dp hPerpMpDp)
      hPerpMpDp
      hCDp
      hBDp
      hCm
      hBdp

  have hAoff :
      Not (HilbertIncidence.OnLine Ap dp) := by
    intro hAd
    exact
      hNormA.1
        ⟨dp, hAd, hBdp, hDdp⟩

  have hCoff :
      Not (HilbertIncidence.OnLine Cp dp) := by
    intro hCd
    exact
      hNormC.1
        ⟨dp, hCd, hDdp, hBdp⟩

  ----------------------------------------------------------------------
  -- Choose X on l so that X and C lie on opposite sides of d.
  --
  -- If A and C are already opposite, take X=A.
  -- Otherwise extend A-B beyond B to X; then X is opposite A, hence
  -- opposite C because A and C are on the same side.
  ----------------------------------------------------------------------

  obtain
      ⟨Xp, hXB, hXlp, hXoff, hOppXC, hRightXBD⟩ :
      exists Xp : PlanePoint Geo sigma,
        Ne Xp Bp /\
        PlaneOnLine Geo Xp lp /\
        Not (PlaneOnLine Geo Xp dp) /\
        HilbertOppositeSide
          (PlaneGeo Geo sigma) Xp Cp dp /\
        HilbertRightAngle
          (PlaneGeo Geo sigma) Xp Bp Dp := by

    by_cases hSame :
        HilbertSameSide
          (PlaneGeo Geo sigma) Ap Cp dp

    · rcases
          HilbertOrder.between_extension
            (Geo := PlaneGeo Geo sigma)
            Ap Bp hABp
        with
        ⟨Xp, hABX⟩

      have hABXData :=
        HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo sigma)
          Ap Bp Xp hABX

      have hXB : Ne Xp Bp :=
        hABXData.2.1.symm

      have hABXcol :
          PrimCollinear
            (PlaneGeo Geo sigma) Ap Bp Xp :=
        hABXData.2.2.2.1

      have hXlp :
          PlaneOnLine Geo Xp lp :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := PlaneGeo Geo sigma)
          hABp
          hAl
          hBl
          hABXcol

      have hXoff :
          Not (PlaneOnLine Geo Xp dp) := by
        intro hXd

        have hEq : lp = dp :=
          HilbertPlaneIncidence.line_unique
            (Geo := PlaneGeo Geo sigma)
            Bp Xp hXB.symm
            lp dp
            hBl hXlp
            hBdp hXd

        have hAd :
            HilbertIncidence.OnLine Ap dp := by
          rw [← hEq]
          exact hAl

        exact hAoff hAd

      have hOppAX :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Ap Xp dp :=
        ⟨hAoff,
         hXoff,
         ⟨Bp, hABX, hBdp⟩⟩

      have hOppXA :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Xp Ap dp :=
        hilbert_oppositeSide_symm
          (PlaneGeo Geo sigma)
          Ap Xp dp hOppAX

      have hOppXC :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Xp Cp dp :=
        hilbert_oppositeSide_transport_right
          (PlaneGeo Geo sigma)
          Xp Ap Cp dp
          hOppXA
          hSame

      have hNormX :=
        hilbert_XI4_linesPerpendicularAt_right_angle_of_points
          (PlaneGeo Geo sigma)
          lp dp
          Bp Xp Dp
          (hilbert_linesPerpendicularAt_ne
            (PlaneGeo Geo sigma)
            lp dp Bp hPerpLpDp)
          hPerpLpDp
          hXB
          hBDp.symm
          hXlp
          hDdp

      exact
        ⟨Xp,
         hXB,
         (show PlaneOnLine Geo Xp lp from hXlp),
         (show Not (PlaneOnLine Geo Xp dp) from hXoff),
         hOppXC,
         hNormX.2⟩

    · have hOppAC :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Ap Cp dp :=
        hilbert_oppositeSide_of_not_sameSide
          (PlaneGeo Geo sigma)
          Ap Cp dp
          hAoff hCoff hSame

      exact
        ⟨Ap,
         hABp,
         (show PlaneOnLine Geo Ap lp from hAl),
         (show Not (PlaneOnLine Geo Ap dp) from hAoff),
         hOppAC,
         hNormA.2⟩

  ----------------------------------------------------------------------
  -- The two selected right angles are congruent (spatial Hilbert 21).
  ----------------------------------------------------------------------

  have hNonXBDPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Xp Bp Dp) := by
    intro h
    exact
      hXoff
        (hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := PlaneGeo Geo sigma)
          hBDp
          hBdp
          hDdp
          (PrimCollinearCycle
            (PlaneGeo Geo sigma)
            Xp Bp Dp h))

  have hNonCDBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Cp Dp Bp) :=
    hNormC.1

  have hNonXBDAmbient :
      Not (PrimCollinear Geo Xp.1 B D) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma Xp Bp Dp hNonXBDPlane

  have hNonCDBAmbient :
      Not (PrimCollinear Geo C D B) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma Cp Dp Bp hNonCDBPlane

  have hRightXBDAmbient :
      HilbertRightAngle Geo Xp.1 B D :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma Xp Bp Dp).mp
      hRightXBD

  have hRightCDBAmbient :
      HilbertRightAngle Geo C D B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma Cp Dp Bp).mp
      hNormC.2

  have hRightAnglesAmbient :
      Geo.AngleCongruent
        Xp.1 B D
        C D B :=
    hilbert_XI6_space_right_angles_congruent_in_plane
      (Geo := Geo)
      sigma
      Xp.1 B D
      Cp Dp Bp
      hNonXBDAmbient
      hNonCDBAmbient
      hRightXBDAmbient
      hRightCDBAmbient

  have hRightAnglesPlane :
      (PlaneGeo Geo sigma).AngleCongruent
        Xp Bp Dp
        Cp Dp Bp :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      sigma
      Xp Bp Dp
      Cp Dp Bp).mpr
      hRightAnglesAmbient

  have hReversed :
      (PlaneGeo Geo sigma).AngleCongruent
        Dp Bp Xp
        Bp Dp Cp :=
    AngleCongruentReverse
      (PlaneGeo Geo sigma)
      Xp Bp Dp
      Cp Dp Bp
      hRightAnglesPlane

  ----------------------------------------------------------------------
  -- Choose M between B and D and rewrite the transversal arms to M.
  ----------------------------------------------------------------------

  rcases
      hilbert_between_exists
        (PlaneGeo Geo sigma)
        Bp Dp hBDp
    with
    ⟨Mp, hBMD⟩

  have hDMB :
      (PlaneGeo Geo sigma).Between
        Dp Mp Bp :=
    (HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo sigma)
      Bp Mp Dp hBMD).2.2.2.2

  have hRayBMD :
      HilbertSameRay
        (PlaneGeo Geo sigma) Bp Mp Dp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      Bp Mp Dp hBMD

  have hRayDMB :
      HilbertSameRay
        (PlaneGeo Geo sigma) Dp Mp Bp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      Dp Mp Bp hDMB

  have hLeft :
      (PlaneGeo Geo sigma).Angle Mp Bp Xp =
      (PlaneGeo Geo sigma).Angle Dp Bp Xp :=
    hilbert_angle_eq_of_sameRay_first
      (PlaneGeo Geo sigma)
      Bp Mp Dp Xp hRayBMD

  have hRight :
      (PlaneGeo Geo sigma).Angle Mp Dp Cp =
      (PlaneGeo Geo sigma).Angle Bp Dp Cp :=
    hilbert_angle_eq_of_sameRay_first
      (PlaneGeo Geo sigma)
      Dp Mp Bp Cp hRayDMB

  have hAlternate :
      (PlaneGeo Geo sigma).AngleCongruent
        Mp Bp Xp
        Mp Dp Cp := by
    unfold Geometry.Geo.AngleCongruent
      at hReversed ⊢
    rw [hLeft, hRight]
    exact hReversed

  ----------------------------------------------------------------------
  -- I.27 in PlaneGeo(sigma).
  ----------------------------------------------------------------------

  have hParallel :
      (PlaneGeo Geo sigma).Parallel
        Bp Xp Dp Cp :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      (PlaneGeo Geo sigma)
      Bp Xp Dp Mp Cp
      dp
      hBMD
      hBdp
      hDdp
      hOppXC
      hAlternate

  ----------------------------------------------------------------------
  -- Convert point-pair parallelism in sigma to disjointness of the
  -- actual ambient carriers l and m.
  ----------------------------------------------------------------------

  intro hMeet

  rcases hMeet with
    ⟨P, hPl, hPm⟩

  have hPsigma : S.OnPlane P sigma :=
    hlsigma P hPl

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hPsigma⟩

  have hPBX :
      Pp ∈ (PlaneGeo Geo sigma).PointLine Bp Xp :=
    (hilbert_mem_pointLine_iff_onLine
      (PlaneGeo Geo sigma)
      Bp Xp Pp lp
      hParallel.1
      hBl hXlp).mpr
      hPl

  have hPDC :
      Pp ∈ (PlaneGeo Geo sigma).PointLine Dp Cp :=
    (hilbert_mem_pointLine_iff_onLine
      (PlaneGeo Geo sigma)
      Dp Cp Pp mp
      hParallel.2.1
      hDm hCm).mpr
      hPm

  exact
    Set.disjoint_left.mp
      hParallel.2.2
      hPBX
      hPDC


/--
Euclid XI.6.

If two distinct-foot lines are perpendicular to the same plane, then
they are parallel in space: they are coplanar and disjoint.
-/
theorem euclid_proposition_11_6
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B)
    (hMperp :
      HilbertLinePerpendicularPlaneAt
        Geo m pi D) :
    HilbertSpaceLinesParallel Geo l m := by

  rcases
      hilbert_XI6_normals_to_same_plane_coplanar
        (Geo := Geo)
        pi l m B D
        hBD
        hLperp
        hMperp
    with
    ⟨sigma, hlsigma, hmsigma⟩

  have hDisjoint :
      HilbertLinesDisjoint Geo l m :=
    hilbert_XI6_coplanar_normals_disjoint
      (Geo := Geo)
      pi sigma
      l m
      B D
      hBD
      hlsigma
      hmsigma
      hLperp
      hMperp

  exact
    ⟨sigma,
     hlsigma,
     hmsigma,
     hDisjoint⟩

end Geometry

import CGJteamLab.HilbertThreeAnglesFourRight
import CGJteamLab.HilbertAngleSumComparison
import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Spatial angle-comparison transport

Production consolidation of the reusable 3D transport machinery
developed while proving Euclid XI.23.

The file contains only proposition-independent spatial infrastructure:
between-point transport, ray/segment transport, subangle transport,
angle-order transport, transport of the XI.20-style two-angle comparison,
spatial Hilbert T14, transport of the three-angle four-right bound, and
ambient-to-PlaneGeo repackaging.

No XI.23-specific construction is included here.
-/

/--
If H lies strictly between X and C, XC is congruent to UV, and U,V lie
in the explicit plane sigma, then there is H1 in sigma with

    U-H1-V,
    XH ~= UH1,
    HC ~= H1V.

The construction uses spatial III.1-III.3. The only planar reasoning is
performed in the already available slice `PlaneGeo Geo sigma`.
-/
theorem hilbert_space_between_point_transport_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (X H C U V : Geo.Point)
    (hUsigma : S.OnPlane U sigma)
    (hVsigma : S.OnPlane V sigma)
    (hXHC : Geo.Between X H C)
    (hXC_UV : Geo.Congruent X C U V)
    (hUV : Ne U V) :
    exists H1 : Geo.Point,
      S.OnPlane H1 sigma /\
      Geo.Between U H1 V /\
      Geo.Congruent X H U H1 /\
      Geo.Congruent H C H1 V := by

  have hXHCdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X H C hXHC

  have hXH : Ne X H :=
    hXHCdata.1

  have hHC : Ne H C :=
    hXHCdata.2.1

  have hXC : Ne X C :=
    hXHCdata.2.2.1

  --------------------------------------------------------------------
  -- Lay off XH on ray UV.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        X H
        U V
        hUV with
    ⟨H1, hRayUVH1, hUH1_XH⟩

  have hUH1 : Ne U H1 :=
    hRayUVH1.2.1.symm

  have hH1sigma :
      S.OnPlane H1 sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      U V H1
      hUV
      hUsigma hVsigma
      hRayUVH1.2.2.1

  have hXH_UH1 :
      Geo.Congruent X H U H1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      U H1 X H
      hUH1
      hUH1_XH

  --------------------------------------------------------------------
  -- Extend U-H1 and lay off HC beyond H1.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo)
        U H1 hUH1 with
    ⟨T, hUH1T⟩

  have hH1T : Ne H1 T :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      U H1 T hUH1T).2.1

  have hTsigma :
      S.OnPlane T sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      U H1 T
      hUH1
      hUsigma hH1sigma
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        U H1 T hUH1T).2.2.2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        H C
        H1 T
        hH1T with
    ⟨V1, hRayH1TV1, hH1V1_HC⟩

  have hH1V1 : Ne H1 V1 :=
    hRayH1TV1.2.1.symm

  have hV1sigma :
      S.OnPlane V1 sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      H1 T V1
      hH1T
      hH1sigma hTsigma
      hRayH1TV1.2.2.1

  have hHC_H1V1 :
      Geo.Congruent H C H1 V1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      H1 V1 H C
      hH1V1
      hH1V1_HC

  --------------------------------------------------------------------
  -- All target-side points are now in sigma. Use PlaneGeo only for
  -- the order transport U-H1-T -> U-H1-V1.
  --------------------------------------------------------------------

  let Up : PlanePoint Geo sigma :=
    ⟨U, hUsigma⟩

  let Vp : PlanePoint Geo sigma :=
    ⟨V, hVsigma⟩

  let H1p : PlanePoint Geo sigma :=
    ⟨H1, hH1sigma⟩

  let Tp : PlanePoint Geo sigma :=
    ⟨T, hTsigma⟩

  let V1p : PlanePoint Geo sigma :=
    ⟨V1, hV1sigma⟩

  have hUpH1p : Ne Up H1p := by
    intro hEq
    exact hUH1
      (congrArg Subtype.val hEq)

  have hH1pTp : Ne H1p Tp := by
    intro hEq
    exact hH1T
      (congrArg Subtype.val hEq)

  have hUH1TPlane :
      (PlaneGeo Geo sigma).Between Up H1p Tp := by
    apply
      (planeGeo_between
        (Geo := Geo) sigma Up H1p Tp).mpr
    simpa [Up, H1p, Tp] using hUH1T

  have hRayH1TV1Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) H1p Tp V1p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma H1p Tp V1p).mpr
    simpa [H1p, Tp, V1p] using hRayH1TV1

  have hRayH1UUPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) H1p Up Up :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      H1p Up
      hUpH1p

  have hUH1V1Plane :
      (PlaneGeo Geo sigma).Between Up H1p V1p :=
    hilbert_between_transport_sameRays
      (PlaneGeo Geo sigma)
      Up H1p Tp
      Up V1p
      hUH1TPlane
      hRayH1UUPlane
      hRayH1TV1Plane

  have hUH1V1 :
      Geo.Between U H1 V1 := by
    have h :=
      (planeGeo_between
        (Geo := Geo) sigma Up H1p V1p).mp
        hUH1V1Plane
    simpa [Up, H1p, V1p] using h

  --------------------------------------------------------------------
  -- Add the two transported parts. This gives XC ~= UV1.
  --------------------------------------------------------------------

  have hXC_UV1 :
      Geo.Congruent X C U V1 :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      X H C
      U H1 V1
      hXHC
      hUH1V1
      hXH_UH1
      hHC_H1V1

  have hUV_UV1 :
      Geo.Congruent U V U V1 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      X C
      U V
      U V1
      hXC_UV
      hXC_UV1

  have hUV1_UV :
      Geo.Congruent U V1 U V :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      U V U V1
      hUV
      hUV_UV1

  --------------------------------------------------------------------
  -- V and V1 lie on the same ray from U. In PlaneGeo sigma they are
  -- two layoff points at the same distance from U, hence V1 = V.
  --------------------------------------------------------------------

  have hRayUVH1Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Up Vp H1p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Up Vp H1p).mpr
    simpa [Up, Vp, H1p] using hRayUVH1

  have hRayUH1VPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Up H1p Vp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo sigma)
      Up Vp H1p
      hRayUVH1Plane

  have hRayUH1V1Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Up H1p V1p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      Up H1p V1p
      hUH1V1Plane

  have hRayUVV1Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Up Vp V1p :=
    hilbert_sameRay_common_reference
      (PlaneGeo Geo sigma)
      Up H1p Vp V1p
      hRayUH1VPlane
      hRayUH1V1Plane

  have hUpVp : Ne Up Vp := by
    intro hEq
    exact hUV
      (congrArg Subtype.val hEq)

  have hRayUVVPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Up Vp Vp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      Up Vp
      hUpVp.symm

  have hUVrefl :
      Geo.Congruent U V U V :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      U V hUV

  have hUVreflPlane :
      (PlaneGeo Geo sigma).Congruent
        Up Vp Up Vp := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma Up Vp Up Vp).mpr
    simpa [Up, Vp] using hUVrefl

  have hUV1_UVPlane :
      (PlaneGeo Geo sigma).Congruent
        Up V1p Up Vp := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma Up V1p Up Vp).mpr
    simpa [Up, V1p, Vp] using hUV1_UV

  have hVeqV1Plane : Vp = V1p :=
    hilbert_segment_construction_unique
      (PlaneGeo Geo sigma)
      Up Vp
      Up Vp
      Vp V1p
      hRayUVVPlane
      hRayUVV1Plane
      hUVreflPlane
      hUV1_UVPlane

  have hVeqV1 : V = V1 :=
    congrArg Subtype.val hVeqV1Plane

  subst V1

  exact
    ⟨H1,
      hH1sigma,
      hUH1V1,
      hXH_UH1,
      hHC_H1V1⟩

/--
If ray OR meets segment AB, and A,B are moved along the same two rays
from O to A',B', then ray OR still meets A'B'.

All six named points lie in one explicit plane `sigma`. The proof moves
the configuration to `PlaneGeo Geo sigma`, applies the existing planar
same-ray theorem there, and forgets the plane subtype again.
-/
theorem hilbert_space_ray_meets_segment_sameRays_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (O R A B A' B' : Geo.Point)
    (hOsigma : S.OnPlane O sigma)
    (hRsigma : S.OnPlane R sigma)
    (hAsigma : S.OnPlane A sigma)
    (hBsigma : S.OnPlane B sigma)
    (hA'sigma : S.OnPlane A' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (hMeet : HilbertRayMeetsSegment Geo O R A B)
    (hAA' : HilbertSameRay Geo O A A')
    (hBB' : HilbertSameRay Geo O B B')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'OB' : Not (PrimCollinear Geo A' O B')) :
    HilbertRayMeetsSegment Geo O R A' B' := by

  let Op : PlanePoint Geo sigma :=
    ⟨O, hOsigma⟩

  let Rp : PlanePoint Geo sigma :=
    ⟨R, hRsigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let A'p : PlanePoint Geo sigma :=
    ⟨A', hA'sigma⟩

  let B'p : PlanePoint Geo sigma :=
    ⟨B', hB'sigma⟩

  --------------------------------------------------------------------
  -- Properness of the two ambient angles becomes properness in sigma.
  --------------------------------------------------------------------

  have hAOBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ap Op Bp) := by
    intro hCol
    apply hAOB
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ap Op Bp hCol
    simpa [Ap, Op, Bp] using h

  have hA'OB'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A'p Op B'p) := by
    intro hCol
    apply hA'OB'
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma A'p Op B'p hCol
    simpa [A'p, Op, B'p] using h

  --------------------------------------------------------------------
  -- Same-ray data bridge directly to PlaneGeo.
  --------------------------------------------------------------------

  have hAA'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Op Ap A'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Op Ap A'p).mpr
    simpa [Op, Ap, A'p] using hAA'

  have hBB'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Op Bp B'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Op Bp B'p).mpr
    simpa [Op, Bp, B'p] using hBB'

  --------------------------------------------------------------------
  -- Convert the original ray-segment intersection to PlaneGeo sigma.
  --------------------------------------------------------------------

  rcases hMeet with
    ⟨X, hAXB, hRayORX⟩

  have hAXBdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A X B hAXB

  have hAB : Ne A B :=
    hAXBdata.2.2.1

  have hAXBcol :
      PrimCollinear Geo A X B :=
    hAXBdata.2.2.2.1

  have hABXcol :
      PrimCollinear Geo A B X := by
    rcases hAXBcol with ⟨l, hAl, hXl, hBl⟩
    exact ⟨l, hAl, hBl, hXl⟩

  have hXsigma :
      S.OnPlane X sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      A B X
      hAB
      hAsigma hBsigma
      hABXcol

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hXsigma⟩

  have hAXBPlane :
      (PlaneGeo Geo sigma).Between Ap Xp Bp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        sigma Ap Xp Bp).mpr
    simpa [Ap, Xp, Bp] using hAXB

  have hRayORXPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Op Rp Xp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Op Rp Xp).mpr
    simpa [Op, Rp, Xp] using hRayORX

  have hMeetPlane :
      HilbertRayMeetsSegment
        (PlaneGeo Geo sigma)
        Op Rp Ap Bp :=
    ⟨Xp, hAXBPlane, hRayORXPlane⟩

  --------------------------------------------------------------------
  -- Use the existing planar theorem inside the explicit plane.
  --------------------------------------------------------------------

  have hResultPlane :
      HilbertRayMeetsSegment
        (PlaneGeo Geo sigma)
        Op Rp A'p B'p :=
    hilbert_ray_meets_segment_sameRays
      (PlaneGeo Geo sigma)
      Op Rp
      Ap Bp
      A'p B'p
      hMeetPlane
      hAA'Plane
      hBB'Plane
      hAOBPlane
      hA'OB'Plane

  --------------------------------------------------------------------
  -- Forget the PlaneGeo subtype.
  --------------------------------------------------------------------

  rcases hResultPlane with
    ⟨Yp, hA'YB'Plane, hRayORYPlane⟩

  have hA'YB' :
      Geo.Between A' Yp.1 B' := by
    have h :=
      (planeGeo_between
        (Geo := Geo)
        sigma A'p Yp B'p).mp
        hA'YB'Plane
    simpa [A'p, B'p] using h

  have hRayORY :
      HilbertSameRay Geo O R Yp.1 := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Op Rp Yp).mp
        hRayORYPlane
    simpa [Op, Rp] using h

  exact
    ⟨Yp.1,
      hA'YB',
      hRayORY⟩

/--
Inside one explicit plane, moving both sides of an angle along the same
two ambient rays preserves ambient angle congruence.
-/
theorem hilbert_space_angleCongruent_of_sameRays_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B A1 B1 : Geo.Point)
    (hAsigma : S.OnPlane A sigma)
    (hOsigma : S.OnPlane O sigma)
    (hBsigma : S.OnPlane B sigma)
    (hA1sigma : S.OnPlane A1 sigma)
    (hB1sigma : S.OnPlane B1 sigma)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hAA1 : HilbertSameRay Geo O A A1)
    (hBB1 : HilbertSameRay Geo O B B1) :
    Geo.AngleCongruent A O B A1 O B1 := by

  let Ap : PlanePoint Geo sigma := ⟨A, hAsigma⟩
  let Op : PlanePoint Geo sigma := ⟨O, hOsigma⟩
  let Bp : PlanePoint Geo sigma := ⟨B, hBsigma⟩
  let A1p : PlanePoint Geo sigma := ⟨A1, hA1sigma⟩
  let B1p : PlanePoint Geo sigma := ⟨B1, hB1sigma⟩

  have hAOBPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Ap Op Bp) := by
    intro h
    apply hAOB
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma Ap Op Bp h
    simpa [Ap, Op, Bp] using hAmb

  have hAA1Plane :
      HilbertSameRay (PlaneGeo Geo sigma) Op Ap A1p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Op Ap A1p).mpr
    simpa [Op, Ap, A1p] using hAA1

  have hBB1Plane :
      HilbertSameRay (PlaneGeo Geo sigma) Op Bp B1p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Op Bp B1p).mpr
    simpa [Op, Bp, B1p] using hBB1

  have hFirst :
      (PlaneGeo Geo sigma).Angle Ap Op Bp =
      (PlaneGeo Geo sigma).Angle A1p Op Bp :=
    hilbert_angle_eq_of_sameRay_first
      (PlaneGeo Geo sigma)
      Op Ap A1p Bp
      hAA1Plane

  have hSecond :
      (PlaneGeo Geo sigma).Angle A1p Op Bp =
      (PlaneGeo Geo sigma).Angle A1p Op B1p :=
    hilbert_angle_eq_of_sameRay_second
      (PlaneGeo Geo sigma)
      Op A1p Bp B1p
      hBB1Plane

  have hEq :
      (PlaneGeo Geo sigma).Angle Ap Op Bp =
      (PlaneGeo Geo sigma).Angle A1p Op B1p :=
    hFirst.trans hSecond

  have hRefl :
      (PlaneGeo Geo sigma).AngleCongruent
        Ap Op Bp Ap Op Bp :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo sigma)
      Ap Op Bp hAOBPlane

  have hPlane :
      (PlaneGeo Geo sigma).AngleCongruent
        Ap Op Bp A1p Op B1p := by
    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [hEq.symm]
    exact hRefl

  have hAmbient :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      sigma
      Ap Op Bp
      A1p Op B1p).mp
      hPlane

  simpa [Ap, Op, Bp, A1p, B1p] using hAmbient


/--
Spatial counterpart of `hilbert_interior_subangle_transport`.

The source angle may lie in an arbitrary spatial plane.  The target
angle is carried by the explicit plane `sigma`.  The result is an
interior ray of the target angle with the corresponding component angle
congruent to the source component.

No global `HilbertCongruence Geo` instance is used.
-/


theorem hilbert_space_interior_subangle_transport_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (O X C D A' O' B' : Geo.Point)
    (hA'sigma : S.OnPlane A' sigma)
    (hO'sigma : S.OnPlane O' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hAOB : Not (PrimCollinear Geo A' O' B'))
    (hInside : HilbertRayMeetsSegment Geo O D X C)
    (hWhole : Geo.AngleCongruent X O C A' O' B') :
    exists D' : Geo.Point,
      S.OnPlane D' sigma /\
      HilbertRayMeetsSegment Geo O' D' A' B' /\
      Geo.AngleCongruent C O D B' O' D' := by

  --------------------------------------------------------------------
  -- The source angle determines its own plane rho.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        X O C hXOC
    with
    ⟨rho, hXrho, hOrho, hCrho⟩

  have hXO : Ne X O :=
    hilbert_noncollinear_ne_first
      Geo X O C hXOC

  have hOX : Ne O X := hXO.symm

  have hOC : Ne O C := by
    intro h
    subst C
    apply hXOC
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) X O hXO with
      ⟨l, hXl, hOl⟩
    exact ⟨l, hXl, hOl, hOl⟩

  have hA'O' : Ne A' O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hAOB

  have hO'A' : Ne O' A' := hA'O'.symm

  have hO'B' : Ne O' B' := by
    intro h
    subst B'
    apply hAOB
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) A' O' hA'O' with
      ⟨l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hO'l⟩

  have hA'B' : Ne A' B' := by
    intro h
    subst B'
    apply hAOB
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) A' O' hA'O' with
      ⟨l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hA'l⟩

  --------------------------------------------------------------------
  -- The original interior-ray point D also lies in rho.
  --------------------------------------------------------------------

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hXHCdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) X H C hXHC

  have hXC : Ne X C :=
    hXHCdata.2.2.1

  have hXHCcol :
      PrimCollinear Geo X H C :=
    hXHCdata.2.2.2.1

  have hXCHcol :
      PrimCollinear Geo X C H := by
    rcases hXHCcol with ⟨l, hXl, hHl, hCl⟩
    exact ⟨l, hXl, hCl, hHl⟩

  have hHrho :
      S.OnPlane H rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho X C H
      hXC
      hXrho hCrho
      hXCHcol

  have hOH : Ne O H :=
    hRayODH.2.1.symm

  have hOHDcol :
      PrimCollinear Geo O H D := by
    rcases hRayODH.2.2.1 with ⟨l, hOl, hDl, hHl⟩
    exact ⟨l, hOl, hHl, hDl⟩

  have hDrho :
      S.OnPlane D rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho O H D
      hOH
      hOrho hHrho
      hOHDcol

  --------------------------------------------------------------------
  -- Normalize the two source rays to the lengths O'A' and O'B'.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' A'
        O X
        hOX
    with
    ⟨X0, hRayX0, hOX0_O'A'⟩

  have hOX0 : Ne O X0 :=
    hRayX0.2.1.symm

  have hX0rho :
      S.OnPlane X0 rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho O X X0
      hOX
      hOrho hXrho
      hRayX0.2.2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' B'
        O C
        hOC
    with
    ⟨C0, hRayC0, hOC0_O'B'⟩

  have hOC0 : Ne O C0 :=
    hRayC0.2.1.symm

  have hC0rho :
      S.OnPlane C0 rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho O C C0
      hOC
      hOrho hCrho
      hRayC0.2.2.1

  let Xp : PlanePoint Geo rho := ⟨X, hXrho⟩
  let Op : PlanePoint Geo rho := ⟨O, hOrho⟩
  let Cp : PlanePoint Geo rho := ⟨C, hCrho⟩
  let X0p : PlanePoint Geo rho := ⟨X0, hX0rho⟩
  let C0p : PlanePoint Geo rho := ⟨C0, hC0rho⟩

  have hXOCPlane :
      Not (PrimCollinear (PlaneGeo Geo rho) Xp Op Cp) := by
    intro h
    apply hXOC
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) rho Xp Op Cp h
    simpa [Xp, Op, Cp] using hAmb

  have hRayX0Plane :
      HilbertSameRay (PlaneGeo Geo rho) Op Xp X0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Op Xp X0p).mpr
    simpa [Op, Xp, X0p] using hRayX0

  have hRayC0Plane :
      HilbertSameRay (PlaneGeo Geo rho) Op Cp C0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Op Cp C0p).mpr
    simpa [Op, Cp, C0p] using hRayC0

  have hX0OC0Plane :
      Not (PrimCollinear (PlaneGeo Geo rho) X0p Op C0p) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      Xp Op Cp
      X0p C0p
      hXOCPlane
      hRayX0Plane
      hRayC0Plane

  have hX0OC0 :
      Not (PrimCollinear Geo X0 O C0) := by
    intro h
    apply hX0OC0Plane
    have hPlane :=
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho X0p Op C0p
        hRayX0.2.1
        h
    exact hPlane

  have hMoveWhole :
      Geo.AngleCongruent X O C X0 O C0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      X O C X0 C0
      hXrho hOrho hCrho hX0rho hC0rho
      hXOC
      hRayX0 hRayC0

  have hMoveWholeSymm :
      Geo.AngleCongruent X0 O C0 X O C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X O C
      X0 O C0
      hMoveWhole

  have hWhole0 :
      Geo.AngleCongruent X0 O C0 A' O' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X0 O C0
      X O C
      A' O' B'
      hMoveWholeSymm
      hWhole

  --------------------------------------------------------------------
  -- Big SAS: X0C0 ~= A'B' and the angle at X0 is transported.
  --------------------------------------------------------------------

  have hOX0C0 :
      Not (PrimCollinear Geo O X0 C0) := by
    intro h
    apply hX0OC0
    rcases h with ⟨l, hOl, hX0l, hC0l⟩
    exact ⟨l, hX0l, hOl, hC0l⟩

  let A'p : PlanePoint Geo sigma := ⟨A', hA'sigma⟩
  let O'p : PlanePoint Geo sigma := ⟨O', hO'sigma⟩
  let B'p : PlanePoint Geo sigma := ⟨B', hB'sigma⟩

  have hO'A'B'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p A'p B'p) := by
    intro h
    apply hAOB
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma O'p A'p B'p h
    rcases hAmb with ⟨l, hO'l, hA'l, hB'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hBig :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      O X0 C0
      O'p A'p B'p
      hOX0C0
      hO'A'B'Plane
      hOX0_O'A'
      hOC0_O'B'
      hWhole0

  have hX0C0_A'B' :
      Geo.Congruent X0 C0 A' B' := by
    simpa [A'p, B'p] using hBig.1

  have hBigAngleX0 :
      Geo.AngleCongruent O X0 C0 O' A' B' :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      O X0 C0
      O' A' B'
      hOX0C0
      (by
        intro h
        apply hAOB
        rcases h with ⟨l, hO'l, hA'l, hB'l⟩
        exact ⟨l, hA'l, hO'l, hB'l⟩)
      hOX0_O'A'
      hOC0_O'B'
      hWhole0

  --------------------------------------------------------------------
  -- Move the original interior ray to segment X0C0 in rho.
  --------------------------------------------------------------------

  have hInside0 :
      HilbertRayMeetsSegment Geo O D X0 C0 :=
    hilbert_space_ray_meets_segment_sameRays_in_plane
      (Geo := Geo)
      rho
      O D
      X C
      X0 C0
      hOrho hDrho
      hXrho hCrho
      hX0rho hC0rho
      ⟨H, hXHC, hRayODH⟩
      hRayX0
      hRayC0
      hXOC
      hX0OC0

  rcases hInside0 with
    ⟨H0, hX0H0C0, hRayODH0⟩

  have hX0H0C0data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X0 H0 C0 hX0H0C0

  have hX0C0 : Ne X0 C0 :=
    hX0H0C0data.2.2.1

  have hX0H0C0col :
      PrimCollinear Geo X0 H0 C0 :=
    hX0H0C0data.2.2.2.1

  have hX0C0H0col :
      PrimCollinear Geo X0 C0 H0 := by
    rcases hX0H0C0col with ⟨l, hX0l, hH0l, hC0l⟩
    exact ⟨l, hX0l, hC0l, hH0l⟩

  have hH0rho :
      S.OnPlane H0 rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho X0 C0 H0
      hX0C0
      hX0rho hC0rho
      hX0C0H0col

  let H0p : PlanePoint Geo rho := ⟨H0, hH0rho⟩

  have hX0H0C0Plane :
      (PlaneGeo Geo rho).Between X0p H0p C0p := by
    apply
      (planeGeo_between
        (Geo := Geo) rho X0p H0p C0p).mpr
    simpa [X0p, H0p, C0p] using hX0H0C0

  have hRayX0H0C0Plane :
      HilbertSameRay
        (PlaneGeo Geo rho) X0p H0p C0p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo rho)
      X0p H0p C0p
      hX0H0C0Plane

  have hRayX0C0H0Plane :
      HilbertSameRay
        (PlaneGeo Geo rho) X0p C0p H0p :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      X0p H0p C0p
      hRayX0H0C0Plane

  have hRayX0C0H0 :
      HilbertSameRay Geo X0 C0 H0 := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho X0p C0p H0p).mp
        hRayX0C0H0Plane
    simpa [X0p, C0p, H0p] using h

  --------------------------------------------------------------------
  -- Transport the split point to the target segment A'B'.
  --------------------------------------------------------------------

  rcases
      hilbert_space_between_point_transport_in_plane
        (Geo := Geo)
        sigma
        X0 H0 C0
        A' B'
        hA'sigma hB'sigma
        hX0H0C0
        hX0C0_A'B'
        hA'B'
    with
    ⟨H', hH'sigma, hA'H'B', hX0H0_A'H', hH0C0_H'B'⟩

  let H'p : PlanePoint Geo sigma := ⟨H', hH'sigma⟩

  have hA'H'B'Plane :
      (PlaneGeo Geo sigma).Between A'p H'p B'p := by
    apply
      (planeGeo_between
        (Geo := Geo) sigma A'p H'p B'p).mpr
    simpa [A'p, H'p, B'p] using hA'H'B'

  have hRayA'H'B'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p H'p B'p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      A'p H'p B'p
      hA'H'B'Plane

  have hRayA'B'H'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p B'p H'p :=
    hilbert_sameRay_symm
      (PlaneGeo Geo sigma)
      A'p H'p B'p
      hRayA'H'B'Plane

  have hRayA'B'H' :
      HilbertSameRay Geo A' B' H' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma A'p B'p H'p).mp
        hRayA'B'H'Plane
    simpa [A'p, B'p, H'p] using h

  --------------------------------------------------------------------
  -- Move the angle-at-X0 conclusion from C0/B' to H0/H'.
  --------------------------------------------------------------------

  have hX0O : Ne X0 O := hOX0.symm

  have hRayX0OOPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) X0p Op Op :=
    hilbert_sameRay_refl
      (PlaneGeo Geo rho)
      X0p Op
      (by
        intro h
        exact hX0O (congrArg Subtype.val h).symm)

  have hRayX0OO :
      HilbertSameRay Geo X0 O O := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho X0p Op Op).mp
        hRayX0OOPlane
    simpa [X0p, Op] using h

  have hOX0C0Proper :
      Not (PrimCollinear Geo O X0 C0) :=
    hOX0C0

  have hMoveSmallLeft :
      Geo.AngleCongruent O X0 C0 O X0 H0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      O X0 C0
      O H0
      hOrho hX0rho hC0rho
      hOrho hH0rho
      hOX0C0Proper
      hRayX0OO
      hRayX0C0H0

  have hA'O' : Ne A' O' := hA'O'

  have hRayA'O'O'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p O'p O'p :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      A'p O'p
      (by
        intro h
        exact hA'O' (congrArg Subtype.val h).symm)

  have hRayA'O'O' :
      HilbertSameRay Geo A' O' O' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma A'p O'p O'p).mp
        hRayA'O'O'Plane
    simpa [A'p, O'p] using h

  have hO'A'B' :
      Not (PrimCollinear Geo O' A' B') := by
    intro h
    apply hAOB
    rcases h with ⟨l, hO'l, hA'l, hB'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hMoveSmallRight :
      Geo.AngleCongruent O' A' B' O' A' H' :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma
      O' A' B'
      O' H'
      hO'sigma hA'sigma hB'sigma
      hO'sigma hH'sigma
      hO'A'B'
      hRayA'O'O'
      hRayA'B'H'

  have hMoveSmallLeftSymm :
      Geo.AngleCongruent O X0 H0 O X0 C0 :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O X0 C0
      O X0 H0
      hMoveSmallLeft

  have hTmpSmall :
      Geo.AngleCongruent O X0 H0 O' A' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O X0 H0
      O X0 C0
      O' A' B'
      hMoveSmallLeftSymm
      hBigAngleX0

  have hSmallAngle :
      Geo.AngleCongruent O X0 H0 O' A' H' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O X0 H0
      O' A' B'
      O' A' H'
      hTmpSmall
      hMoveSmallRight

  --------------------------------------------------------------------
  -- Noncollinearity for the small SAS triangles.
  --------------------------------------------------------------------

  have hOX0C0Plane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Op X0p C0p) := by
    intro h
    apply hOX0C0
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) rho Op X0p C0p h
    simpa [Op, X0p, C0p] using hAmb

  have hOX0H0Plane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Op X0p H0p) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      Op X0p C0p
      Op H0p
      hOX0C0Plane
      hRayX0OOPlane
      hRayX0C0H0Plane

  have hX0OH0 :
      Not (PrimCollinear Geo X0 O H0) := by
    intro h
    have hOX0H0 : PrimCollinear Geo O X0 H0 := by
      rcases h with ⟨l, hX0l, hOl, hH0l⟩
      exact ⟨l, hOl, hX0l, hH0l⟩
    apply hOX0H0Plane
    exact
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho Op X0p H0p
        hOX0
        hOX0H0

  have hO'A'H'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p A'p H'p) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      O'p A'p B'p
      O'p H'p
      hO'A'B'Plane
      hRayA'O'O'Plane
      hRayA'B'H'Plane

  --------------------------------------------------------------------
  -- Small SAS gives OH0 ~= O'H'.
  --------------------------------------------------------------------

  have hX0O_A'O' :
      Geo.Congruent X0 O A' O' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      X0 O
      O' A').mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        O X0
        O' A').mp
        hOX0_O'A')

  have hSmall :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      X0 O H0
      A'p O'p H'p
      hX0OH0
      (by
        intro h
        exact hO'A'H'Plane
          (by
            rcases h with ⟨l, hA'l, hO'l, hH'l⟩
            exact ⟨l, hO'l, hA'l, hH'l⟩))
      hX0O_A'O'
      hX0H0_A'H'
      hSmallAngle

  have hOH0_O'H' :
      Geo.Congruent O H0 O' H' := by
    simpa [O'p, H'p] using hSmall.1

  --------------------------------------------------------------------
  -- Final SSS for triangles O-C0-H0 and O'-B'-H'.
  --------------------------------------------------------------------

  have hC0H0_B'H' :
      Geo.Congruent C0 H0 B' H' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      C0 H0
      H' B').mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        H0 C0
        H' B').mp
        hH0C0_H'B')

  have hOC0H0 :
      Not (PrimCollinear Geo O C0 H0) := by
    intro hCol

    rcases hCol with ⟨l, hOl, hC0l, hH0l⟩
    rcases hX0H0C0col with ⟨m, hX0m, hH0m, hC0m⟩

    have hC0H0 : Ne C0 H0 :=
      hX0H0C0data.2.1.symm

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        C0 H0 hC0H0
        l m
        hC0l hH0l
        hC0m hH0m

    subst m

    exact hOX0C0
      ⟨l, hOl, hX0m, hC0l⟩

  have hO'B'H'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p B'p H'p) := by
    intro hCol

    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma O'p B'p H'p hCol

    rcases hAmb with ⟨l, hO'l, hB'l, hH'l⟩

    have hA'H'B'data :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A' H' B' hA'H'B'

    have hA'H' : Ne A' H' :=
      hA'H'B'data.1

    have hA'H'B'col :
      PrimCollinear Geo A' H' B' :=
      hA'H'B'data.2.2.2.1

    rcases hA'H'B'col with
      ⟨m, hA'm, hH'm, hB'm⟩

    have hH'B' : Ne H' B' :=
      hA'H'B'data.2.1

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        H' B' hH'B'
        l m
        hH'l hB'l
        hH'm hB'm

    subst m

    exact hAOB
      ⟨l, hA'm, hO'l, hB'l⟩

  have hSSS :=
    hilbert_space_sss_angleA_in_plane
      (Geo := Geo)
      sigma
      O C0 H0
      O'p B'p H'p
      hOC0H0
      hO'B'H'Plane
      hOC0_O'B'
      hC0H0_B'H'
      hOH0_O'H'

  have hC0OH0_B'O'H' :
      Geo.AngleCongruent C0 O H0 B' O' H' := by
    simpa [O'p, B'p, H'p] using hSSS

  --------------------------------------------------------------------
  -- Return from the normalized rays C0,H0 to the original rays C,D.
  --------------------------------------------------------------------

  have hC0OH0Plane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) C0p Op H0p) := by
    intro h
    apply hOC0H0
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) rho C0p Op H0p h
    simpa [C0p, Op, H0p] using
      (by
        rcases hAmb with ⟨l, hC0l, hOl, hH0l⟩
        exact (⟨l, hOl, hC0l, hH0l⟩ :
          PrimCollinear Geo O C0 H0))

  let Dp : PlanePoint Geo rho := ⟨D, hDrho⟩

  have hRayC0CPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op C0p Cp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      Op Cp C0p
      hRayC0Plane

  have hRayDH0Plane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op Dp H0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Op Dp H0p).mpr
    simpa [Op, Dp, H0p] using hRayODH0

  have hRayH0DPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op H0p Dp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      Op Dp H0p
      hRayDH0Plane

  have hCODPlane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Cp Op Dp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      C0p Op H0p
      Cp Dp
      hC0OH0Plane
      hRayC0CPlane
      hRayH0DPlane

  have hCOD :
      Not (PrimCollinear Geo C O D) := by
    intro h
    apply hCODPlane
    exact
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho Cp Op Dp
        hOC.symm
        h

  have hMoveFinal :
      Geo.AngleCongruent C O D C0 O H0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      C O D
      C0 H0
      hCrho hOrho hDrho
      hC0rho hH0rho
      hCOD
      hRayC0
      hRayODH0

  have hFinal :
      Geo.AngleCongruent C O D B' O' H' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C O D
      C0 O H0
      B' O' H'
      hMoveFinal
      hC0OH0_B'O'H'

  --------------------------------------------------------------------
  -- H' itself is a valid interior ray of A'O'B'.
  --------------------------------------------------------------------

  have hO'H' : Ne O' H' := by
    intro hEq
    subst H'
    have hCol :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A' O' B' hA'H'B').2.2.2.1
    exact hAOB hCol

  have hO'pH'p : Ne O'p H'p := by
    intro h
    exact hO'H' (congrArg Subtype.val h)

  have hRayO'H'H'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) O'p H'p H'p :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      O'p H'p hO'pH'p.symm

  have hRayO'H'H' :
      HilbertSameRay Geo O' H' H' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma O'p H'p H'p).mp
        hRayO'H'H'Plane
    simpa [O'p, H'p] using h

  exact
    ⟨H',
      hH'sigma,
      ⟨H', hA'H'B', hRayO'H'H'⟩,
      hFinal⟩

/--
Spatial counterpart of `hilbert_interior_subangle_transport`.

The source angle may lie in an arbitrary spatial plane.  The target
angle is carried by the explicit plane `sigma`.  The result is an
interior ray of the target angle with the corresponding component angle
congruent to the source component.

No global `HilbertCongruence Geo` instance is used.
-/
theorem hilbert_space_interior_subangle_transport_both_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (O X C D A' O' B' : Geo.Point)
    (hA'sigma : S.OnPlane A' sigma)
    (hO'sigma : S.OnPlane O' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hAOB : Not (PrimCollinear Geo A' O' B'))
    (hInside : HilbertRayMeetsSegment Geo O D X C)
    (hWhole : Geo.AngleCongruent X O C A' O' B') :
    exists D' : Geo.Point,
      S.OnPlane D' sigma /\
      HilbertRayMeetsSegment Geo O' D' A' B' /\
      (
        Geo.AngleCongruent C O D B' O' D' /\
        Geo.AngleCongruent X O D A' O' D'
      ) := by

  --------------------------------------------------------------------
  -- The source angle determines its own plane rho.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        X O C hXOC
    with
    ⟨rho, hXrho, hOrho, hCrho⟩

  have hXO : Ne X O :=
    hilbert_noncollinear_ne_first
      Geo X O C hXOC

  have hOX : Ne O X := hXO.symm

  have hOC : Ne O C := by
    intro h
    subst C
    apply hXOC
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) X O hXO with
      ⟨l, hXl, hOl⟩
    exact ⟨l, hXl, hOl, hOl⟩

  have hA'O' : Ne A' O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hAOB

  have hO'A' : Ne O' A' := hA'O'.symm

  have hO'B' : Ne O' B' := by
    intro h
    subst B'
    apply hAOB
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) A' O' hA'O' with
      ⟨l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hO'l⟩

  have hA'B' : Ne A' B' := by
    intro h
    subst B'
    apply hAOB
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) A' O' hA'O' with
      ⟨l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hA'l⟩

  --------------------------------------------------------------------
  -- The original interior-ray point D also lies in rho.
  --------------------------------------------------------------------

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hXHCdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) X H C hXHC

  have hXC : Ne X C :=
    hXHCdata.2.2.1

  have hXHCcol :
      PrimCollinear Geo X H C :=
    hXHCdata.2.2.2.1

  have hXCHcol :
      PrimCollinear Geo X C H := by
    rcases hXHCcol with ⟨l, hXl, hHl, hCl⟩
    exact ⟨l, hXl, hCl, hHl⟩

  have hHrho :
      S.OnPlane H rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho X C H
      hXC
      hXrho hCrho
      hXCHcol

  have hOH : Ne O H :=
    hRayODH.2.1.symm

  have hOHDcol :
      PrimCollinear Geo O H D := by
    rcases hRayODH.2.2.1 with ⟨l, hOl, hDl, hHl⟩
    exact ⟨l, hOl, hHl, hDl⟩

  have hDrho :
      S.OnPlane D rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho O H D
      hOH
      hOrho hHrho
      hOHDcol

  --------------------------------------------------------------------
  -- Normalize the two source rays to the lengths O'A' and O'B'.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' A'
        O X
        hOX
    with
    ⟨X0, hRayX0, hOX0_O'A'⟩

  have hOX0 : Ne O X0 :=
    hRayX0.2.1.symm

  have hX0rho :
      S.OnPlane X0 rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho O X X0
      hOX
      hOrho hXrho
      hRayX0.2.2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' B'
        O C
        hOC
    with
    ⟨C0, hRayC0, hOC0_O'B'⟩

  have hOC0 : Ne O C0 :=
    hRayC0.2.1.symm

  have hC0rho :
      S.OnPlane C0 rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho O C C0
      hOC
      hOrho hCrho
      hRayC0.2.2.1

  let Xp : PlanePoint Geo rho := ⟨X, hXrho⟩
  let Op : PlanePoint Geo rho := ⟨O, hOrho⟩
  let Cp : PlanePoint Geo rho := ⟨C, hCrho⟩
  let X0p : PlanePoint Geo rho := ⟨X0, hX0rho⟩
  let C0p : PlanePoint Geo rho := ⟨C0, hC0rho⟩

  have hXOCPlane :
      Not (PrimCollinear (PlaneGeo Geo rho) Xp Op Cp) := by
    intro h
    apply hXOC
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) rho Xp Op Cp h
    simpa [Xp, Op, Cp] using hAmb

  have hRayX0Plane :
      HilbertSameRay (PlaneGeo Geo rho) Op Xp X0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Op Xp X0p).mpr
    simpa [Op, Xp, X0p] using hRayX0

  have hRayC0Plane :
      HilbertSameRay (PlaneGeo Geo rho) Op Cp C0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Op Cp C0p).mpr
    simpa [Op, Cp, C0p] using hRayC0

  have hX0OC0Plane :
      Not (PrimCollinear (PlaneGeo Geo rho) X0p Op C0p) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      Xp Op Cp
      X0p C0p
      hXOCPlane
      hRayX0Plane
      hRayC0Plane

  have hX0OC0 :
      Not (PrimCollinear Geo X0 O C0) := by
    intro h
    apply hX0OC0Plane
    have hPlane :=
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho X0p Op C0p
        hRayX0.2.1
        h
    exact hPlane

  have hMoveWhole :
      Geo.AngleCongruent X O C X0 O C0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      X O C X0 C0
      hXrho hOrho hCrho hX0rho hC0rho
      hXOC
      hRayX0 hRayC0

  have hMoveWholeSymm :
      Geo.AngleCongruent X0 O C0 X O C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X O C
      X0 O C0
      hMoveWhole

  have hWhole0 :
      Geo.AngleCongruent X0 O C0 A' O' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X0 O C0
      X O C
      A' O' B'
      hMoveWholeSymm
      hWhole

  --------------------------------------------------------------------
  -- Big SAS: X0C0 ~= A'B' and the angle at X0 is transported.
  --------------------------------------------------------------------

  have hOX0C0 :
      Not (PrimCollinear Geo O X0 C0) := by
    intro h
    apply hX0OC0
    rcases h with ⟨l, hOl, hX0l, hC0l⟩
    exact ⟨l, hX0l, hOl, hC0l⟩

  let A'p : PlanePoint Geo sigma := ⟨A', hA'sigma⟩
  let O'p : PlanePoint Geo sigma := ⟨O', hO'sigma⟩
  let B'p : PlanePoint Geo sigma := ⟨B', hB'sigma⟩

  have hO'A'B'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p A'p B'p) := by
    intro h
    apply hAOB
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma O'p A'p B'p h
    rcases hAmb with ⟨l, hO'l, hA'l, hB'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hBig :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      O X0 C0
      O'p A'p B'p
      hOX0C0
      hO'A'B'Plane
      hOX0_O'A'
      hOC0_O'B'
      hWhole0

  have hX0C0_A'B' :
      Geo.Congruent X0 C0 A' B' := by
    simpa [A'p, B'p] using hBig.1

  have hBigAngleX0 :
      Geo.AngleCongruent O X0 C0 O' A' B' :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      O X0 C0
      O' A' B'
      hOX0C0
      (by
        intro h
        apply hAOB
        rcases h with ⟨l, hO'l, hA'l, hB'l⟩
        exact ⟨l, hA'l, hO'l, hB'l⟩)
      hOX0_O'A'
      hOC0_O'B'
      hWhole0

  --------------------------------------------------------------------
  -- Move the original interior ray to segment X0C0 in rho.
  --------------------------------------------------------------------

  have hInside0 :
      HilbertRayMeetsSegment Geo O D X0 C0 :=
    hilbert_space_ray_meets_segment_sameRays_in_plane
      (Geo := Geo)
      rho
      O D
      X C
      X0 C0
      hOrho hDrho
      hXrho hCrho
      hX0rho hC0rho
      ⟨H, hXHC, hRayODH⟩
      hRayX0
      hRayC0
      hXOC
      hX0OC0

  rcases hInside0 with
    ⟨H0, hX0H0C0, hRayODH0⟩

  have hX0H0C0data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X0 H0 C0 hX0H0C0

  have hX0C0 : Ne X0 C0 :=
    hX0H0C0data.2.2.1

  have hX0H0C0col :
      PrimCollinear Geo X0 H0 C0 :=
    hX0H0C0data.2.2.2.1

  have hX0C0H0col :
      PrimCollinear Geo X0 C0 H0 := by
    rcases hX0H0C0col with ⟨l, hX0l, hH0l, hC0l⟩
    exact ⟨l, hX0l, hC0l, hH0l⟩

  have hH0rho :
      S.OnPlane H0 rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho X0 C0 H0
      hX0C0
      hX0rho hC0rho
      hX0C0H0col

  let H0p : PlanePoint Geo rho := ⟨H0, hH0rho⟩

  have hX0H0C0Plane :
      (PlaneGeo Geo rho).Between X0p H0p C0p := by
    apply
      (planeGeo_between
        (Geo := Geo) rho X0p H0p C0p).mpr
    simpa [X0p, H0p, C0p] using hX0H0C0

  have hRayX0H0C0Plane :
      HilbertSameRay
        (PlaneGeo Geo rho) X0p H0p C0p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo rho)
      X0p H0p C0p
      hX0H0C0Plane

  have hRayX0C0H0Plane :
      HilbertSameRay
        (PlaneGeo Geo rho) X0p C0p H0p :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      X0p H0p C0p
      hRayX0H0C0Plane

  have hRayX0C0H0 :
      HilbertSameRay Geo X0 C0 H0 := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho X0p C0p H0p).mp
        hRayX0C0H0Plane
    simpa [X0p, C0p, H0p] using h

  --------------------------------------------------------------------
  -- Transport the split point to the target segment A'B'.
  --------------------------------------------------------------------

  rcases
      hilbert_space_between_point_transport_in_plane
        (Geo := Geo)
        sigma
        X0 H0 C0
        A' B'
        hA'sigma hB'sigma
        hX0H0C0
        hX0C0_A'B'
        hA'B'
    with
    ⟨H', hH'sigma, hA'H'B', hX0H0_A'H', hH0C0_H'B'⟩

  let H'p : PlanePoint Geo sigma := ⟨H', hH'sigma⟩

  have hA'H'B'Plane :
      (PlaneGeo Geo sigma).Between A'p H'p B'p := by
    apply
      (planeGeo_between
        (Geo := Geo) sigma A'p H'p B'p).mpr
    simpa [A'p, H'p, B'p] using hA'H'B'

  have hRayA'H'B'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p H'p B'p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      A'p H'p B'p
      hA'H'B'Plane

  have hRayA'B'H'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p B'p H'p :=
    hilbert_sameRay_symm
      (PlaneGeo Geo sigma)
      A'p H'p B'p
      hRayA'H'B'Plane

  have hRayA'B'H' :
      HilbertSameRay Geo A' B' H' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma A'p B'p H'p).mp
        hRayA'B'H'Plane
    simpa [A'p, B'p, H'p] using h

  --------------------------------------------------------------------
  -- Move the angle-at-X0 conclusion from C0/B' to H0/H'.
  --------------------------------------------------------------------

  have hX0O : Ne X0 O := hOX0.symm

  have hRayX0OOPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) X0p Op Op :=
    hilbert_sameRay_refl
      (PlaneGeo Geo rho)
      X0p Op
      (by
        intro h
        exact hX0O (congrArg Subtype.val h).symm)

  have hRayX0OO :
      HilbertSameRay Geo X0 O O := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho X0p Op Op).mp
        hRayX0OOPlane
    simpa [X0p, Op] using h

  have hOX0C0Proper :
      Not (PrimCollinear Geo O X0 C0) :=
    hOX0C0

  have hMoveSmallLeft :
      Geo.AngleCongruent O X0 C0 O X0 H0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      O X0 C0
      O H0
      hOrho hX0rho hC0rho
      hOrho hH0rho
      hOX0C0Proper
      hRayX0OO
      hRayX0C0H0

  have hA'O' : Ne A' O' := hA'O'

  have hRayA'O'O'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p O'p O'p :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      A'p O'p
      (by
        intro h
        exact hA'O' (congrArg Subtype.val h).symm)

  have hRayA'O'O' :
      HilbertSameRay Geo A' O' O' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma A'p O'p O'p).mp
        hRayA'O'O'Plane
    simpa [A'p, O'p] using h

  have hO'A'B' :
      Not (PrimCollinear Geo O' A' B') := by
    intro h
    apply hAOB
    rcases h with ⟨l, hO'l, hA'l, hB'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hMoveSmallRight :
      Geo.AngleCongruent O' A' B' O' A' H' :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma
      O' A' B'
      O' H'
      hO'sigma hA'sigma hB'sigma
      hO'sigma hH'sigma
      hO'A'B'
      hRayA'O'O'
      hRayA'B'H'

  have hMoveSmallLeftSymm :
      Geo.AngleCongruent O X0 H0 O X0 C0 :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O X0 C0
      O X0 H0
      hMoveSmallLeft

  have hTmpSmall :
      Geo.AngleCongruent O X0 H0 O' A' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O X0 H0
      O X0 C0
      O' A' B'
      hMoveSmallLeftSymm
      hBigAngleX0

  have hSmallAngle :
      Geo.AngleCongruent O X0 H0 O' A' H' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O X0 H0
      O' A' B'
      O' A' H'
      hTmpSmall
      hMoveSmallRight

  --------------------------------------------------------------------
  -- Noncollinearity for the small SAS triangles.
  --------------------------------------------------------------------

  have hOX0C0Plane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Op X0p C0p) := by
    intro h
    apply hOX0C0
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) rho Op X0p C0p h
    simpa [Op, X0p, C0p] using hAmb

  have hOX0H0Plane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Op X0p H0p) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      Op X0p C0p
      Op H0p
      hOX0C0Plane
      hRayX0OOPlane
      hRayX0C0H0Plane

  have hX0OH0 :
      Not (PrimCollinear Geo X0 O H0) := by
    intro h
    have hOX0H0 : PrimCollinear Geo O X0 H0 := by
      rcases h with ⟨l, hX0l, hOl, hH0l⟩
      exact ⟨l, hOl, hX0l, hH0l⟩
    apply hOX0H0Plane
    exact
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho Op X0p H0p
        hOX0
        hOX0H0

  have hO'A'H'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p A'p H'p) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      O'p A'p B'p
      O'p H'p
      hO'A'B'Plane
      hRayA'O'O'Plane
      hRayA'B'H'Plane

  --------------------------------------------------------------------
  -- Small SAS gives OH0 ~= O'H'.
  --------------------------------------------------------------------

  have hX0O_A'O' :
      Geo.Congruent X0 O A' O' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      X0 O
      O' A').mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        O X0
        O' A').mp
        hOX0_O'A')

  have hSmall :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      X0 O H0
      A'p O'p H'p
      hX0OH0
      (by
        intro h
        exact hO'A'H'Plane
          (by
            rcases h with ⟨l, hA'l, hO'l, hH'l⟩
            exact ⟨l, hO'l, hA'l, hH'l⟩))
      hX0O_A'O'
      hX0H0_A'H'
      hSmallAngle

  have hOH0_O'H' :
      Geo.Congruent O H0 O' H' := by
    simpa [O'p, H'p] using hSmall.1

  --------------------------------------------------------------------
  -- Final SSS for triangles O-C0-H0 and O'-B'-H'.
  --------------------------------------------------------------------

  have hC0H0_B'H' :
      Geo.Congruent C0 H0 B' H' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      C0 H0
      H' B').mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        H0 C0
        H' B').mp
        hH0C0_H'B')

  have hOC0H0 :
      Not (PrimCollinear Geo O C0 H0) := by
    intro hCol

    rcases hCol with ⟨l, hOl, hC0l, hH0l⟩
    rcases hX0H0C0col with ⟨m, hX0m, hH0m, hC0m⟩

    have hC0H0 : Ne C0 H0 :=
      hX0H0C0data.2.1.symm

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        C0 H0 hC0H0
        l m
        hC0l hH0l
        hC0m hH0m

    subst m

    exact hOX0C0
      ⟨l, hOl, hX0m, hC0l⟩

  have hO'B'H'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p B'p H'p) := by
    intro hCol

    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma O'p B'p H'p hCol

    rcases hAmb with ⟨l, hO'l, hB'l, hH'l⟩

    have hA'H'B'data :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A' H' B' hA'H'B'

    have hA'H' : Ne A' H' :=
      hA'H'B'data.1

    have hA'H'B'col :
      PrimCollinear Geo A' H' B' :=
      hA'H'B'data.2.2.2.1

    rcases hA'H'B'col with
      ⟨m, hA'm, hH'm, hB'm⟩

    have hH'B' : Ne H' B' :=
      hA'H'B'data.2.1

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        H' B' hH'B'
        l m
        hH'l hB'l
        hH'm hB'm

    subst m

    exact hAOB
      ⟨l, hA'm, hO'l, hB'l⟩

  have hSSS :=
    hilbert_space_sss_angleA_in_plane
      (Geo := Geo)
      sigma
      O C0 H0
      O'p B'p H'p
      hOC0H0
      hO'B'H'Plane
      hOC0_O'B'
      hC0H0_B'H'
      hOH0_O'H'

  have hC0OH0_B'O'H' :
      Geo.AngleCongruent C0 O H0 B' O' H' := by
    simpa [O'p, B'p, H'p] using hSSS

  --------------------------------------------------------------------
  -- Return from the normalized rays C0,H0 to the original rays C,D.
  --------------------------------------------------------------------

  have hC0OH0Plane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) C0p Op H0p) := by
    intro h
    apply hOC0H0
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) rho C0p Op H0p h
    simpa [C0p, Op, H0p] using
      (by
        rcases hAmb with ⟨l, hC0l, hOl, hH0l⟩
        exact (⟨l, hOl, hC0l, hH0l⟩ :
          PrimCollinear Geo O C0 H0))

  let Dp : PlanePoint Geo rho := ⟨D, hDrho⟩

  have hRayC0CPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op C0p Cp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      Op Cp C0p
      hRayC0Plane

  have hRayDH0Plane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op Dp H0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Op Dp H0p).mpr
    simpa [Op, Dp, H0p] using hRayODH0

  have hRayH0DPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op H0p Dp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      Op Dp H0p
      hRayDH0Plane

  have hCODPlane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Cp Op Dp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      C0p Op H0p
      Cp Dp
      hC0OH0Plane
      hRayC0CPlane
      hRayH0DPlane

  have hCOD :
      Not (PrimCollinear Geo C O D) := by
    intro h
    apply hCODPlane
    exact
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho Cp Op Dp
        hOC.symm
        h

  have hMoveFinal :
      Geo.AngleCongruent C O D C0 O H0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      C O D
      C0 H0
      hCrho hOrho hDrho
      hC0rho hH0rho
      hCOD
      hRayC0
      hRayODH0

  have hFinal :
      Geo.AngleCongruent C O D B' O' H' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C O D
      C0 O H0
      B' O' H'
      hMoveFinal
      hC0OH0_B'O'H'

  --------------------------------------------------------------------
  -- The other component angle.
  --
  -- The small SAS already compares triangles
  --
  --   X0-O-H0  and  A'-O'-H'.
  --
  -- Its angle at O gives X0-O-H0 ~= A'-O'-H'.  We then move
  -- X0 back to X and H0 back to D along the same two rays in rho.
  --------------------------------------------------------------------

  have hA'O'H' :
      Not (PrimCollinear Geo A' O' H') :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma A'p O'p H'p
      (by
        intro h
        exact hO'A'H'Plane
          (PrimCollinearSwap
            (PlaneGeo Geo sigma)
            A'p O'p H'p h))

  have hSmallAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      X0 O H0
      A' O' H'
      hX0OH0
      hA'O'H'
      hX0O_A'O'
      hX0H0_A'H'
      hSmallAngle

  have hX0OH0_A'O'H' :
      Geo.AngleCongruent X0 O H0 A' O' H' :=
    hSmallAngles.1

  have hX0OH0Plane' :
      Not (PrimCollinear
        (PlaneGeo Geo rho) X0p Op H0p) := by
    intro h
    exact hOX0H0Plane
      (PrimCollinearSwap
        (PlaneGeo Geo rho)
        X0p Op H0p h)

  have hRayX0XPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op X0p Xp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo rho)
      Op Xp X0p
      hRayX0Plane

  have hXODPlane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Xp Op Dp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      X0p Op H0p
      Xp Dp
      hX0OH0Plane'
      hRayX0XPlane
      hRayH0DPlane

  have hXOD :
      Not (PrimCollinear Geo X O D) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      rho Xp Op Dp hXODPlane

  have hMoveLeft :
      Geo.AngleCongruent X O D X0 O H0 :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      X O D
      X0 H0
      hXrho hOrho hDrho
      hX0rho hH0rho
      hXOD
      hRayX0
      hRayODH0

  have hLeftFinal :
      Geo.AngleCongruent X O D A' O' H' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X O D
      X0 O H0
      A' O' H'
      hMoveLeft
      hX0OH0_A'O'H'

  --------------------------------------------------------------------
  -- H' itself is a valid interior ray of A'O'B'.
  --------------------------------------------------------------------

  have hO'H' : Ne O' H' := by
    intro hEq
    subst H'
    have hCol :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A' O' B' hA'H'B').2.2.2.1
    exact hAOB hCol

  have hO'pH'p : Ne O'p H'p := by
    intro h
    exact hO'H' (congrArg Subtype.val h)

  have hRayO'H'H'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) O'p H'p H'p :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      O'p H'p hO'pH'p.symm

  have hRayO'H'H' :
      HilbertSameRay Geo O' H' H' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma O'p H'p H'p).mp
        hRayO'H'H'Plane
    simpa [O'p, H'p] using h

  exact
    ⟨H',
      hH'sigma,
      ⟨H', hA'H'B', hRayO'H'H'⟩,
      ⟨hFinal, hLeftFinal⟩⟩

/--
Transport strict angle comparison on the right to a congruent angle
contained in an explicit plane.

If

  angle AOB < angle CPD

and

  angle CPD ~= angle C'P'D',

with C',P',D' lying in `sigma`, then

  angle AOB < angle C'P'D'.

The proof is the old planar transport argument with its single
interior-subangle step replaced by the spatial theorem proved in
`Hilbert3DInteriorSubangleTransport_test02`.
-/
theorem hilbert_space_angleLess_transport_right_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D C' P' D' : Geo.Point)
    (hC'sigma : S.OnPlane C' sigma)
    (hP'sigma : S.OnPlane P' sigma)
    (hD'sigma : S.OnPlane D' sigma)
    (hLess :
      HilbertAngleLess Geo A O B C P D)
    (hTarget :
      Not (PrimCollinear Geo C' P' D'))
    (hWhole :
      Geo.AngleCongruent C P D C' P' D') :
    HilbertAngleLess Geo A O B C' P' D' := by

  rcases hLess with
    ⟨hAOB, hCPD, X, hInside, hAngle⟩

  --------------------------------------------------------------------
  -- Reverse the source and target whole angles.
  --------------------------------------------------------------------

  have hWholeRev :
      Geo.AngleCongruent D P C D' P' C' :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      D P C
      C' P' D').mp
      ((Geometry.Geo.angle_congruent_reverse_first
        Geo
        C P D
        C' P' D').mp
        hWhole)

  --------------------------------------------------------------------
  -- Reverse the open source segment CD.
  --------------------------------------------------------------------

  rcases hInside with
    ⟨H, hCHD, hRayPXH⟩

  have hDHC :
      Geo.Between D H C :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C H D hCHD).2.2.2.2

  have hInsideRev :
      HilbertRayMeetsSegment Geo P X D C :=
    ⟨H, hDHC, hRayPXH⟩

  --------------------------------------------------------------------
  -- Properness after reversing the two whole angles.
  --------------------------------------------------------------------

  have hDPC :
      Not (PrimCollinear Geo D P C) := by
    intro h
    exact hCPD
      (PrimCollinearSymm Geo D P C h)

  have hD'P'C' :
      Not (PrimCollinear Geo D' P' C') := by
    intro h
    exact hTarget
      (PrimCollinearSymm Geo D' P' C' h)

  --------------------------------------------------------------------
  -- Spatial transport of the interior ray into sigma.
  --------------------------------------------------------------------

  rcases
      hilbert_space_interior_subangle_transport_in_plane
        (Geo := Geo)
        sigma
        P D C X
        D' P' C'
        hD'sigma
        hP'sigma
        hC'sigma
        hDPC
        hD'P'C'
        hInsideRev
        hWholeRev
    with
    ⟨Y, hYsigma, hInsideTargetRev, hSubAngle⟩

  --------------------------------------------------------------------
  -- Reverse the target segment D'C' back to C'D'.
  --------------------------------------------------------------------

  rcases hInsideTargetRev with
    ⟨K, hD'KC', hRayP'YK⟩

  have hC'KD' :
      Geo.Between C' K D' :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      D' K C' hD'KC').2.2.2.2

  have hInsideTarget :
      HilbertRayMeetsSegment Geo P' Y C' D' :=
    ⟨K, hC'KD', hRayP'YK⟩

  --------------------------------------------------------------------
  -- Compose the old witness angle with the transported subangle.
  --------------------------------------------------------------------

  have hFinal :
      Geo.AngleCongruent A O B C' P' Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O B
      C P X
      C' P' Y
      hAngle
      hSubAngle

  exact
    ⟨hAOB,
      hTarget,
      Y,
      hInsideTarget,
      hFinal⟩

/--
Replace the target angle of `HilbertTwoAnglesGreaterThanAngle` by a
congruent proper angle contained in `sigma`.
-/
theorem hilbert_space_twoAnglesGreater_transport_target_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D E Q F E' Q' F' : Geo.Point)
    (hE'sigma : S.OnPlane E' sigma)
    (hQ'sigma : S.OnPlane Q' sigma)
    (hF'sigma : S.OnPlane F' sigma)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hTarget' :
      Not (PrimCollinear Geo E' Q' F'))
    (hTargetCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C P D
      E' Q' F' := by

  have hFirst :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hSecond :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  have hCore :=
    h.2.2.2

  refine
    And.intro hFirst
      (And.intro hSecond
        (And.intro hTarget' ?_))

  cases hCore with

  --------------------------------------------------------------------
  -- The old target was already smaller than the first summand.
  --------------------------------------------------------------------

  | inl hLess =>

      rcases hLess with
        ⟨hSmall, hWhole, W, hInsideW, hAngleW⟩

      have hTargetCongSymm :
          Geo.AngleCongruent
            E' Q' F'
            E Q F :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          E Q F
          E' Q' F'
          hTargetCong

      have hAngleW' :
          Geo.AngleCongruent
            E' Q' F'
            A O W :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          E' Q' F'
          E Q F
          A O W
          hTargetCongSymm
          hAngleW

      exact
        Or.inl
          ⟨hTarget',
           hWhole,
           W,
           hInsideW,
           hAngleW'⟩

  --------------------------------------------------------------------
  -- The old target was equal to the first summand.
  --------------------------------------------------------------------

  | inr hRest =>
      cases hRest with

      | inl hEq =>

          have hTargetCongSymm :
              Geo.AngleCongruent
                E' Q' F'
                E Q F :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              E Q F
              E' Q' F'
              hTargetCong

          have hEq' :
              Geo.AngleCongruent
                E' Q' F'
                A O B :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              E' Q' F'
              E Q F
              A O B
              hTargetCongSymm
              hEq

          exact
            Or.inr (Or.inl hEq')

      ----------------------------------------------------------------
      -- Decomposition of the old target:
      --
      --   AOB ~= EQX
      --   XQF < CPD.
      --
      -- Transport the split point X to Y inside E'Q'F'.
      ----------------------------------------------------------------

      | inr hDecomp =>

          rcases hDecomp with
            ⟨X, hInside, hFirstPart, hRemainder⟩

          rcases
              hilbert_space_interior_subangle_transport_both_in_plane
                (Geo := Geo)
                sigma
                Q E F X
                E' Q' F'
                hE'sigma
                hQ'sigma
                hF'sigma
                hTarget
                hTarget'
                hInside
                hTargetCong
            with
            ⟨Y, hYsigma, hInside', hBoth⟩

          have hRightPart :
              Geo.AngleCongruent
                F Q X
                F' Q' Y :=
            hBoth.1

          have hLeftPart :
              Geo.AngleCongruent
                E Q X
                E' Q' Y :=
            hBoth.2

          have hFirstPart' :
              Geo.AngleCongruent
                A O B
                E' Q' Y :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              A O B
              E Q X
              E' Q' Y
              hFirstPart
              hLeftPart

          ----------------------------------------------------------------
          -- The new remainder angle YQ'F' is proper.
          --
          -- Use the transported interior point locally in PlaneGeo sigma.
          ----------------------------------------------------------------

          rcases hInside' with
            ⟨K, hE'KF', hRayQ'YK⟩

          have hE'F'Q' :
              Not (PrimCollinear Geo E' F' Q') := by
            rintro ⟨l, hE'l, hF'l, hQ'l⟩
            exact hTarget'
              ⟨l, hE'l, hQ'l, hF'l⟩

          have hE'F' :
              Ne E' F' :=
            hilbert_noncollinear_ne_first
              Geo E' F' Q' hE'F'Q'

          have hE'KF'data :=
            HilbertSpaceOrder.between_incidence
              (Geo := Geo)
              E' K F' hE'KF'

          have hE'KF'col :
              PrimCollinear Geo E' K F' :=
            hE'KF'data.2.2.2.1

          have hE'F'Kcol :
              PrimCollinear Geo E' F' K := by
            rcases hE'KF'col with
              ⟨l, hE'l, hKl, hF'l⟩
            exact
              ⟨l, hE'l, hF'l, hKl⟩

          have hKsigma :
              S.OnPlane K sigma :=
            hilbert_onPlane_of_primCollinear_with_two_on_plane
              (Geo := Geo)
              sigma
              E' F' K
              hE'F'
              hE'sigma hF'sigma
              hE'F'Kcol

          let E'p : PlanePoint Geo sigma :=
            ⟨E', hE'sigma⟩

          let Q'p : PlanePoint Geo sigma :=
            ⟨Q', hQ'sigma⟩

          let F'p : PlanePoint Geo sigma :=
            ⟨F', hF'sigma⟩

          let Yp : PlanePoint Geo sigma :=
            ⟨Y, hYsigma⟩

          let Kp : PlanePoint Geo sigma :=
            ⟨K, hKsigma⟩

          have hF'KE' :
              Geo.Between F' K E' :=
            hE'KF'data.2.2.2.2

          have hF'KpE'Plane :
              (PlaneGeo Geo sigma).Between
                F'p Kp E'p := by
            apply
              (planeGeo_between
                (Geo := Geo)
                sigma F'p Kp E'p).mpr
            simpa [F'p, Kp, E'p] using hF'KE'

          have hRayQ'YKPlane :
              HilbertSameRay
                (PlaneGeo Geo sigma)
                Q'p Yp Kp := by
            apply
              (planeGeo_sameRay_iff_ambient
                (Geo := Geo)
                sigma Q'p Yp Kp).mpr
            simpa [Q'p, Yp, Kp] using hRayQ'YK

          have hInsideRevPlane :
              HilbertRayMeetsSegment
                (PlaneGeo Geo sigma)
                Q'p Yp F'p E'p :=
            ⟨Kp,
             hF'KpE'Plane,
             hRayQ'YKPlane⟩

          have hF'Q'E' :
              Not (PrimCollinear Geo F' Q' E') := by
            rintro ⟨l, hF'l, hQ'l, hE'l⟩
            exact hTarget'
              ⟨l, hE'l, hQ'l, hF'l⟩

          have hF'Q'E'Plane :
              Not (PrimCollinear
                (PlaneGeo Geo sigma)
                F'p Q'p E'p) := by
            intro hCol
            apply hF'Q'E'
            have hAmb :=
              planeGeo_primCollinear_to_ambient
                (Geo := Geo)
                sigma F'p Q'p E'p hCol
            simpa [F'p, Q'p, E'p] using hAmb

          have hLocalLess :
              HilbertAngleLess
                (PlaneGeo Geo sigma)
                F'p Q'p Yp
                F'p Q'p E'p :=
            hilbert_interior_angle_less
              (PlaneGeo Geo sigma)
              Q'p Yp F'p E'p
              hF'Q'E'Plane
              hInsideRevPlane

          have hF'Q'YPlane :
              Not (PrimCollinear
                (PlaneGeo Geo sigma)
                F'p Q'p Yp) :=
            hLocalLess.1

          have hF'Q'Y :
              Not (PrimCollinear Geo F' Q' Y) := by
            have h :=
              planeGeo_not_primCollinear_to_ambient
                (Geo := Geo)
                sigma F'p Q'p Yp
                hF'Q'YPlane
            simpa [F'p, Q'p, Yp] using h

          have hYQ'F' :
              Not (PrimCollinear Geo Y Q' F') := by
            rintro ⟨l, hYl, hQ'l, hF'l⟩
            exact hF'Q'Y
              ⟨l, hF'l, hQ'l, hYl⟩

          ----------------------------------------------------------------
          -- Reorient the second component:
          --
          --   FQX ~= F'Q'Y
          --
          -- to
          --
          --   YQ'F' ~= XQF.
          ----------------------------------------------------------------

          have hXQF_F'Q'Y :
              Geo.AngleCongruent
                X Q F
                F' Q' Y :=
            (Geometry.Geo.angle_congruent_reverse_first
              Geo
              F Q X
              F' Q' Y).mp
              hRightPart

          have hXQF_YQ'F' :
              Geo.AngleCongruent
                X Q F
                Y Q' F' :=
            (Geometry.Geo.angle_congruent_reverse_second
              Geo
              X Q F
              F' Q' Y).mp
              hXQF_F'Q'Y

          have hYQ'F'_XQF :
              Geo.AngleCongruent
                Y Q' F'
                X Q F :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              X Q F
              Y Q' F'
              hXQF_YQ'F'

          ----------------------------------------------------------------
          -- Transport only the SMALL angle of the old remainder.
          -- This is purely structural once the new small angle is proper.
          ----------------------------------------------------------------

          rcases hRemainder with
            ⟨hXQF, hCPD, Z, hInsideZ, hAngleZ⟩

          have hAngleZ' :
              Geo.AngleCongruent
                Y Q' F'
                C P Z :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              Y Q' F'
              X Q F
              C P Z
              hYQ'F'_XQF
              hAngleZ

          have hRemainder' :
              HilbertAngleLess
                Geo
                Y Q' F'
                C P D :=
            ⟨hYQ'F',
             hCPD,
             Z,
             hInsideZ,
             hAngleZ'⟩

          exact
            Or.inr
              (Or.inr
                ⟨Y,
                 ⟨K, hE'KF', hRayQ'YK⟩,
                 hFirstPart',
                 hRemainder'⟩)

/--
Replace the first summand by a congruent proper angle contained in `sigma`.
-/
theorem hilbert_space_twoAnglesGreater_transport_first_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B A' O' B' C P D E Q F : Geo.Point)
    (hA'sigma : S.OnPlane A' sigma)
    (hO'sigma : S.OnPlane O' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hFirst' :
      Not (PrimCollinear Geo A' O' B'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A' O' B'
      C P D
      E Q F := by

  have hSecond :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  have hCore :=
    h.2.2.2

  refine
    And.intro hFirst'
      (And.intro hSecond
        (And.intro hTarget ?_))

  cases hCore with

  | inl hLess =>

      have hLess' :
          HilbertAngleLess
            Geo
            E Q F
            A' O' B' :=
        hilbert_space_angleLess_transport_right_in_plane
          (Geo := Geo)
          sigma
          E Q F
          A O B
          A' O' B'
          hA'sigma
          hO'sigma
          hB'sigma
          hLess
          hFirst'
          hFirstCong

      exact Or.inl hLess'

  | inr hRest =>

      cases hRest with

      | inl hEq =>

          have hEq' :
              Geo.AngleCongruent
                E Q F
                A' O' B' :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              E Q F
              A O B
              A' O' B'
              hEq
              hFirstCong

          exact Or.inr (Or.inl hEq')

      | inr hDecomp =>

          rcases hDecomp with
            ⟨X, hInside, hFirstPart, hRemainder⟩

          have hFirstCongSymm :
              Geo.AngleCongruent
                A' O' B'
                A O B :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              A O B
              A' O' B'
              hFirstCong

          have hFirstPart' :
              Geo.AngleCongruent
                A' O' B'
                E Q X :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              A' O' B'
              A O B
              E Q X
              hFirstCongSymm
              hFirstPart

          exact
            Or.inr
              (Or.inr
                ⟨X,
                 hInside,
                 hFirstPart',
                 hRemainder⟩)


/--
Replace the second summand by a congruent proper angle contained in `sigma`.
-/


theorem hilbert_space_twoAnglesGreater_transport_second_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D C' P' D' E Q F : Geo.Point)
    (hC'sigma : S.OnPlane C' sigma)
    (hP'sigma : S.OnPlane P' sigma)
    (hD'sigma : S.OnPlane D' sigma)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hSecond' :
      Not (PrimCollinear Geo C' P' D'))
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C' P' D'
      E Q F := by

  have hFirst :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  have hCore :=
    h.2.2.2

  refine
    And.intro hFirst
      (And.intro hSecond'
        (And.intro hTarget ?_))

  cases hCore with

  | inl hLess =>
      exact Or.inl hLess

  | inr hRest =>

      cases hRest with

      | inl hEq =>
          exact Or.inr (Or.inl hEq)

      | inr hDecomp =>

          rcases hDecomp with
            ⟨X, hInside, hFirstPart, hRemainder⟩

          have hRemainder' :
              HilbertAngleLess
                Geo
                X Q F
                C' P' D' :=
            hilbert_space_angleLess_transport_right_in_plane
              (Geo := Geo)
              sigma
              X Q F
              C P D
              C' P' D'
              hC'sigma
              hP'sigma
              hD'sigma
              hRemainder
              hSecond'
              hSecondCong

          exact
            Or.inr
              (Or.inr
                ⟨X,
                 hInside,
                 hFirstPart,
                 hRemainder'⟩)

/--
Transport all three angles occurring in

  angle AOB + angle CPD > angle EQF

to congruent proper copies

  angle A'O'B', angle C'P'D', angle E'Q'F'

lying in one explicit plane `sigma`.
-/
theorem hilbert_space_twoAnglesGreater_transport_all_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D E Q F : Geo.Point)
    (A' O' B' C' P' D' E' Q' F' : Geo.Point)
    (hA'sigma : S.OnPlane A' sigma)
    (hO'sigma : S.OnPlane O' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (hC'sigma : S.OnPlane C' sigma)
    (hP'sigma : S.OnPlane P' sigma)
    (hD'sigma : S.OnPlane D' sigma)
    (hE'sigma : S.OnPlane E' sigma)
    (hQ'sigma : S.OnPlane Q' sigma)
    (hF'sigma : S.OnPlane F' sigma)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hFirst' :
      Not (PrimCollinear Geo A' O' B'))
    (hSecond' :
      Not (PrimCollinear Geo C' P' D'))
    (hTarget' :
      Not (PrimCollinear Geo E' Q' F'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B')
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D')
    (hTargetCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A' O' B'
      C' P' D'
      E' Q' F' := by

  have h1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' B'
        C P D
        E Q F :=
    hilbert_space_twoAnglesGreater_transport_first_in_plane
      (Geo := Geo)
      sigma
      A O B
      A' O' B'
      C P D
      E Q F
      hA'sigma
      hO'sigma
      hB'sigma
      h
      hFirst'
      hFirstCong

  have h2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' B'
        C' P' D'
        E Q F :=
    hilbert_space_twoAnglesGreater_transport_second_in_plane
      (Geo := Geo)
      sigma
      A' O' B'
      C P D
      C' P' D'
      E Q F
      hC'sigma
      hP'sigma
      hD'sigma
      h1
      hSecond'
      hSecondCong

  exact
    hilbert_space_twoAnglesGreater_transport_target_in_plane
      (Geo := Geo)
      sigma
      A' O' B'
      C' P' D'
      E Q F
      E' Q' F'
      hE'sigma
      hQ'sigma
      hF'sigma
      h2
      hTarget'
      hTargetCong

theorem hilbert_space_adjacent_angles_congruent_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C A' O' B' C' : Geo.Point)
    (hA'sigma : S.OnPlane A' sigma)
    (hO'sigma : S.OnPlane O' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (hC'sigma : S.OnPlane C' sigma)
    (hAOC : Geo.Between A O C)
    (hA'O'C' : Geo.Between A' O' C')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'O'B' : Not (PrimCollinear Geo A' O' B'))
    (hAngle : Geo.AngleCongruent A O B A' O' B') :
    Geo.AngleCongruent B O C B' O' C' := by

  --------------------------------------------------------------------
  -- Source plane rho.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A O B hAOB
    with
    ⟨rho, hArho, hOrho, hBrho⟩

  have hAOCData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O C hAOC

  have hA'O'C'Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A' O' C' hA'O'C'

  have hAO : Ne A O :=
    hAOCData.1

  have hOA : Ne O A :=
    hAO.symm

  have hOC : Ne O C :=
    hAOCData.2.1

  have hAC : Ne A C :=
    hAOCData.2.2.1

  have hAOCcol :
      PrimCollinear Geo A O C :=
    hAOCData.2.2.2.1

  have hCrho :
      S.OnPlane C rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      A O C
      hAO
      hArho hOrho
      hAOCcol

  have hOB : Ne O B := by
    intro h
    subst B
    apply hAOB
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) A O hAO with
      ⟨l, hAl, hOl⟩
    exact ⟨l, hAl, hOl, hOl⟩

  --------------------------------------------------------------------
  -- Copy O'A', O'B', O'C' onto the three source rays.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' A'
        O A
        hOA
    with
    ⟨X, hAX, hOX⟩

  have hOXne : Ne O X :=
    hAX.2.1.symm

  have hXrho :
      S.OnPlane X rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      O A X
      hOA
      hOrho hArho
      hAX.2.2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' B'
        O B
        hOB
    with
    ⟨Y, hBY, hOY⟩

  have hOYne : Ne O Y :=
    hBY.2.1.symm

  have hYrho :
      S.OnPlane Y rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      O B Y
      hOB
      hOrho hBrho
      hBY.2.2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' C'
        O C
        hOC
    with
    ⟨Z, hCZ, hOZ⟩

  have hOZne : Ne O Z :=
    hCZ.2.1.symm

  have hZrho :
      S.OnPlane Z rho :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      rho
      O C Z
      hOC
      hOrho hCrho
      hCZ.2.2.1

  --------------------------------------------------------------------
  -- First SAS: triangle OXY versus O'A'B'.
  --------------------------------------------------------------------

  let Ap : PlanePoint Geo rho := ⟨A, hArho⟩
  let Op : PlanePoint Geo rho := ⟨O, hOrho⟩
  let Bp : PlanePoint Geo rho := ⟨B, hBrho⟩
  let Cp : PlanePoint Geo rho := ⟨C, hCrho⟩
  let Xp : PlanePoint Geo rho := ⟨X, hXrho⟩
  let Yp : PlanePoint Geo rho := ⟨Y, hYrho⟩
  let Zp : PlanePoint Geo rho := ⟨Z, hZrho⟩

  have hAOBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Ap Op Bp) := by
    intro h
    apply hAOB
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        rho Ap Op Bp h
    simpa [Ap, Op, Bp] using hAmb

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

  have hXOYPlane :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Xp Op Yp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo rho)
      Ap Op Bp
      Xp Yp
      hAOBPlane
      hAXPlane
      hBYPlane

  have hXOY :
      Not (PrimCollinear Geo X O Y) := by
    have h :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        rho Xp Op Yp hXOYPlane
    simpa [Xp, Op, Yp] using h

  have hMoveFirst :
      Geo.AngleCongruent A O B X O Y :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      A O B
      X Y
      hArho hOrho hBrho
      hXrho hYrho
      hAOB
      hAX hBY

  have hMoveFirstSymm :
      Geo.AngleCongruent X O Y A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      X O Y
      hMoveFirst

  have hAngleXOY :
      Geo.AngleCongruent X O Y A' O' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X O Y
      A O B
      A' O' B'
      hMoveFirstSymm
      hAngle

  have hOXY :
      Not (PrimCollinear Geo O X Y) := by
    intro h
    exact hXOY
      (PrimCollinearSwap Geo O X Y h)

  let A'p : PlanePoint Geo sigma := ⟨A', hA'sigma⟩
  let O'p : PlanePoint Geo sigma := ⟨O', hO'sigma⟩
  let B'p : PlanePoint Geo sigma := ⟨B', hB'sigma⟩
  let C'p : PlanePoint Geo sigma := ⟨C', hC'sigma⟩

  have hO'A'B'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) O'p A'p B'p) := by
    intro h
    apply hA'O'B'
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma O'p A'p B'p h
    rcases hAmb with ⟨l, hO'l, hA'l, hB'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hFirstAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      O X Y
      O' A' B'
      hOXY
      (by
        intro h
        apply hA'O'B'
        rcases h with ⟨l, hO'l, hA'l, hB'l⟩
        exact ⟨l, hA'l, hO'l, hB'l⟩)
      hOX
      hOY
      hAngleXOY

  have hFirstSide :
      Geo.Congruent X Y A' B' := by
    have h :=
      hilbert_space_sas_third_side_and_angle
        (Geo := Geo)
        sigma
        O X Y
        O'p A'p B'p
        hOXY
        hO'A'B'Plane
        hOX
        hOY
        hAngleXOY
    simpa [A'p, B'p] using h.1

  --------------------------------------------------------------------
  -- Transport A-O-C to X-O-Z inside the source plane.
  --------------------------------------------------------------------

  have hAOCPlane :
      (PlaneGeo Geo rho).Between Ap Op Cp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        rho Ap Op Cp).mpr
    simpa [Ap, Op, Cp] using hAOC

  have hCZPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Op Cp Zp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Op Cp Zp).mpr
    simpa [Op, Cp, Zp] using hCZ

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
    have h :=
      (planeGeo_between
        (Geo := Geo)
        rho Xp Op Zp).mp
        hXOZPlane
    simpa [Xp, Op, Zp] using h

  have hXO :
      Geo.Congruent X O A' O' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      X O
      O' A').mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        O X
        O' A').mp
        hOX)

  have hXZ :
      Geo.Congruent X Z A' C' :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      X O Z
      A' O' C'
      hXOZ
      hA'O'C'
      hXO
      hOZ

  --------------------------------------------------------------------
  -- Convert the first-SAS angle at X into Y-X-Z ~= B'-A'-C'.
  --------------------------------------------------------------------

  have hRayXOZPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Xp Op Zp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo rho)
      Xp Op Zp
      hXOZPlane

  have hRayXOZ :
      HilbertSameRay Geo X O Z := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Xp Op Zp).mp
        hRayXOZPlane
    simpa [Xp, Op, Zp] using h

  have hC'O'A' :
      Geo.Between C' O' A' :=
    hA'O'C'Data.2.2.2.2

  have hC'O'A'Plane :
      (PlaneGeo Geo sigma).Between C'p O'p A'p := by
    apply
      (planeGeo_between
        (Geo := Geo)
        sigma C'p O'p A'p).mpr
    simpa [C'p, O'p, A'p] using hC'O'A'

  have hRayC'O'A'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) C'p O'p A'p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      C'p O'p A'p
      hC'O'A'Plane

  have hRayA'O'C'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p O'p C'p :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      A'p O'p C'p
      (by
        apply
          (planeGeo_between
            (Geo := Geo)
            sigma A'p O'p C'p).mpr
        simpa [A'p, O'p, C'p] using hA'O'C')

  have hA'O' : Ne A' O' :=
    hA'O'C'Data.1

  have hA'B' : Ne A' B' := by
    intro h
    subst B'
    apply hA'O'B'
    rcases HilbertPlaneIncidence.line_through
        (Geo := Geo) A' O' hA'O' with
      ⟨l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hA'l⟩

  have hRayA'B'B'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A'p B'p B'p :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      A'p B'p
      (by
        intro h
        exact hA'B'
          (congrArg Subtype.val h).symm)

  have hB'A'O' :
      Not (PrimCollinear Geo B' A' O') := by
    intro h
    apply hA'O'B'
    rcases h with ⟨l, hB'l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hMoveRightAtA :
      Geo.AngleCongruent B' A' O' B' A' C' :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma
      B' A' O'
      B' C'
      hB'sigma hA'sigma hO'sigma
      hB'sigma hC'sigma
      hB'A'O'
      (by
        have h :=
          (planeGeo_sameRay_iff_ambient
            (Geo := Geo)
            sigma A'p B'p B'p).mp
            hRayA'B'B'Plane
        simpa [A'p, B'p] using h)
      (by
        have h :=
          (planeGeo_sameRay_iff_ambient
            (Geo := Geo)
            sigma A'p O'p C'p).mp
            hRayA'O'C'Plane
        simpa [A'p, O'p, C'p] using h)

  have hYXO_B'A'O' :
      Geo.AngleCongruent Y X O B' A' O' :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      Y X O
      O' A' B').mp
      ((Geometry.Geo.angle_congruent_reverse_first
        Geo
        O X Y
        O' A' B').mp
        hFirstAngles.1)

  have hYXO :
      Not (PrimCollinear Geo Y X O) := by
    intro h
    apply hXOY
    rcases h with ⟨l, hYl, hXl, hOl⟩
    exact ⟨l, hXl, hOl, hYl⟩

  have hXrho_refl :
      HilbertSameRay Geo X Y Y := by
    let Xpp : PlanePoint Geo rho := ⟨X, hXrho⟩
    let Ypp : PlanePoint Geo rho := ⟨Y, hYrho⟩
    have hXY : Ne X Y :=
      hilbert_noncollinear_ne_first
        Geo X Y O
        (by
          intro h
          exact hXOY
            (PrimCollinearRotate Geo X Y O h))
    have hPlane :
        HilbertSameRay
          (PlaneGeo Geo rho) Xpp Ypp Ypp :=
      hilbert_sameRay_refl
        (PlaneGeo Geo rho)
        Xpp Ypp
        (by
          intro h
          exact hXY
            (congrArg Subtype.val h).symm)
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Xpp Ypp Ypp).mp
        hPlane
    simpa [Xpp, Ypp] using h

  have hMoveLeftAtX :
      Geo.AngleCongruent Y X O Y X Z :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      Y X O
      Y Z
      hYrho hXrho hOrho
      hYrho hZrho
      hYXO
      hXrho_refl
      hRayXOZ

  have hYXO_B'A'C' :
      Geo.AngleCongruent Y X O B' A' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      Y X O
      B' A' O'
      B' A' C'
      hYXO_B'A'O'
      hMoveRightAtA

  have hAngleXYZ :
      Geo.AngleCongruent Y X Z B' A' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      Y X Z
      Y X O
      B' A' C'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        Y X O
        Y X Z
        hMoveLeftAtX)
      hYXO_B'A'C'

  --------------------------------------------------------------------
  -- Second SAS: triangle XYZ versus A'B'C'.
  --------------------------------------------------------------------

  have hXYZ :
      Not (PrimCollinear Geo X Y Z) := by
    intro h
    have hXOZdata :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ
    have hOXZ :
        PrimCollinear Geo O X Z :=
      PrimCollinearSwap Geo X O Z
        hXOZdata.2.2.2.1
    have hXZY :
        PrimCollinear Geo X Z Y :=
      PrimCollinearRotate Geo X Y Z h
    have hOXY :
        PrimCollinear Geo O X Y :=
      hilbert_primCollinear_trans
        Geo
        O X Z Y
        hXOZdata.2.2.1
        hOXZ
        hXZY
    exact hXOY
      (PrimCollinearSwap Geo O X Y hOXY)

  have hA'B'C' :
      Not (PrimCollinear Geo A' B' C') := by
    intro h
    have hO'A'C' :
        PrimCollinear Geo O' A' C' :=
      PrimCollinearSwap Geo A' O' C'
        hA'O'C'Data.2.2.2.1
    have hA'C'B' :
        PrimCollinear Geo A' C' B' :=
      PrimCollinearRotate Geo A' B' C' h
    have hO'A'B' :
        PrimCollinear Geo O' A' B' :=
      hilbert_primCollinear_trans
        Geo
        O' A' C' B'
        hA'O'C'Data.2.2.1
        hO'A'C'
        hA'C'B'
    exact hA'O'B'
      (PrimCollinearSwap Geo O' A' B' hO'A'B')

  have hA'B'C'Plane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A'p B'p C'p) := by
    intro h
    apply hA'B'C'
    have hAmb :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma A'p B'p C'p h
    simpa [A'p, B'p, C'p] using hAmb

  have hSecond :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      X Y Z
      A'p B'p C'p
      hXYZ
      hA'B'C'Plane
      hFirstSide
      hXZ
      hAngleXYZ

  have hYZ_B'C' :
      Geo.Congruent Y Z B' C' := by
    simpa [B'p, C'p] using hSecond.1

  have hXZY_A'C'B' :
      Geo.AngleCongruent X Z Y A' C' B' := by
    simpa [A'p, B'p, C'p] using hSecond.2

  --------------------------------------------------------------------
  -- Convert the angle at Z to O-Z-Y ~= O'-C'-B'.
  --------------------------------------------------------------------

  have hZOX :
      Geo.Between Z O X :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X O Z hXOZ).2.2.2.2

  have hZOXPlane :
      (PlaneGeo Geo rho).Between Zp Op Xp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        rho Zp Op Xp).mpr
    simpa [Zp, Op, Xp] using hZOX

  have hRayZOXPlane :
      HilbertSameRay
        (PlaneGeo Geo rho) Zp Op Xp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo rho)
      Zp Op Xp
      hZOXPlane

  have hRayZOX :
      HilbertSameRay Geo Z O X := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Zp Op Xp).mp
        hRayZOXPlane
    simpa [Zp, Op, Xp] using h

  have hZYX :
      Not (PrimCollinear Geo Z Y X) := by
    intro h
    apply hXYZ
    rcases h with ⟨l, hZl, hYl, hXl⟩
    exact ⟨l, hXl, hYl, hZl⟩

  have hZY : Ne Z Y :=
    hilbert_noncollinear_ne_first
      Geo Z Y X hZYX

  have hRayZYY :
      HilbertSameRay Geo Z Y Y := by
    let Zpp : PlanePoint Geo rho := ⟨Z, hZrho⟩
    let Ypp : PlanePoint Geo rho := ⟨Y, hYrho⟩
    have hPlane :
        HilbertSameRay
          (PlaneGeo Geo rho) Zpp Ypp Ypp :=
      hilbert_sameRay_refl
        (PlaneGeo Geo rho)
        Zpp Ypp
        (by
          intro h
          exact hZY
            (congrArg Subtype.val h).symm)
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        rho Zpp Ypp Ypp).mp
        hPlane
    simpa [Zpp, Ypp] using h

  have hOZY :
      Not (PrimCollinear Geo O Z Y) := by
    intro h
    apply hXYZ
    rcases h with ⟨l, hOl, hZl, hYl⟩
    have hXOZcol :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ).2.2.2.1
    rcases hXOZcol with
      ⟨m, hXm, hOm, hZm⟩
    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O Z hOZne
        l m
        hOl hZl
        hOm hZm
    subst m
    exact ⟨l, hXm, hYl, hZl⟩

  have hMoveAtZ :
      Geo.AngleCongruent O Z Y X Z Y :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      O Z Y
      X Y
      hOrho hZrho hYrho
      hXrho hYrho
      hOZY
      hRayZOX
      hRayZYY

  have hC'O'A'PlaneRay :
      HilbertSameRay
        (PlaneGeo Geo sigma) C'p O'p A'p :=
    hRayC'O'A'Plane

  have hRayC'B'B' :
      HilbertSameRay Geo C' B' B' := by
    let Cpp : PlanePoint Geo sigma := ⟨C', hC'sigma⟩
    let Bpp : PlanePoint Geo sigma := ⟨B', hB'sigma⟩
    have hC'B'A' :
        Not (PrimCollinear Geo C' B' A') := by
      intro h
      apply hA'B'C'
      rcases h with ⟨l, hC'l, hB'l, hA'l⟩
      exact ⟨l, hA'l, hB'l, hC'l⟩

    have hC'B' : Ne C' B' :=
      hilbert_noncollinear_ne_first
        Geo C' B' A' hC'B'A'
    have hPlane :
        HilbertSameRay
          (PlaneGeo Geo sigma) Cpp Bpp Bpp :=
      hilbert_sameRay_refl
        (PlaneGeo Geo sigma)
        Cpp Bpp
        (by
          intro h
          exact hC'B'
            (congrArg Subtype.val h).symm)
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Cpp Bpp Bpp).mp
        hPlane
    simpa [Cpp, Bpp] using h

  have hRayC'O'A' :
      HilbertSameRay Geo C' O' A' := by
    have h :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma C'p O'p A'p).mp
        hC'O'A'PlaneRay
    simpa [C'p, O'p, A'p] using h

  have hO'C'B' :
      Not (PrimCollinear Geo O' C' B') := by
    intro h
    apply hA'B'C'
    rcases h with ⟨l, hO'l, hC'l, hB'l⟩
    rcases hA'O'C'Data.2.2.2.1 with
      ⟨m, hA'm, hO'm, hC'm⟩
    have hO'C' : Ne O' C' :=
      hA'O'C'Data.2.1
    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O' C' hO'C'
        l m
        hO'l hC'l
        hO'm hC'm
    subst m
    exact ⟨l, hA'm, hB'l, hC'l⟩

  have hMoveAtC' :
      Geo.AngleCongruent O' C' B' A' C' B' :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma
      O' C' B'
      A' B'
      hO'sigma hC'sigma hB'sigma
      hA'sigma hB'sigma
      hO'C'B'
      hRayC'O'A'
      hRayC'B'B'

  have hOZY_A'C'B' :
      Geo.AngleCongruent O Z Y A' C' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O Z Y
      X Z Y
      A' C' B'
      hMoveAtZ
      hXZY_A'C'B'

  have hOZY_O'C'B' :
      Geo.AngleCongruent O Z Y O' C' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O Z Y
      A' C' B'
      O' C' B'
      hOZY_A'C'B'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        O' C' B'
        A' C' B'
        hMoveAtC')

  --------------------------------------------------------------------
  -- Third SAS: triangle ZOY versus C'O'B'.
  --------------------------------------------------------------------

  have hZO :
      Geo.Congruent Z O C' O' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      Z O
      O' C').mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        O Z
        O' C').mp
        hOZ)

  have hZY_B'C' :
      Geo.Congruent Z Y B' C' :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      Y Z
      B' C').mp
      hYZ_B'C'

  have hZY_C'B' :
      Geo.Congruent Z Y C' B' :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      Z Y
      B' C').mp
      hZY_B'C'

  have hZOY :
      Not (PrimCollinear Geo Z O Y) := by
    intro h
    exact hOZY
      (PrimCollinearSwap Geo Z O Y h)

  have hC'O'B' :
      Not (PrimCollinear Geo C' O' B') := by
    intro h
    apply hA'O'B'
    have hO'C' : Ne O' C' :=
      hA'O'C'Data.2.1
    have hA'O'C'col :=
      hA'O'C'Data.2.2.2.1
    have hO'C'B' :=
      PrimCollinearSwap Geo C' O' B' h
    exact
      hilbert_primCollinear_trans
        Geo
        A' O' C' B'
        hO'C'
        hA'O'C'col
        hO'C'B'

  have hFinal :
      Geo.AngleCongruent Z O Y C' O' B' :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      Z O Y
      C' O' B'
      hZOY
      hC'O'B'
      hZO
      hZY_C'B'
      hOZY_O'C'B'

  --------------------------------------------------------------------
  -- Return from Z,Y to the original rays C,B.
  --------------------------------------------------------------------

  have hCOB :
      Not (PrimCollinear Geo C O B) := by
    intro h
    apply hAOB
    have hOC : Ne O C :=
      hAOCData.2.1
    have hAOCcol :=
      hAOCData.2.2.2.1
    have hOCB :=
      PrimCollinearSwap Geo C O B h
    exact
      hilbert_primCollinear_trans
        Geo
        A O C B
        hOC
        hAOCcol
        hOCB

  have hMoveFinal :
      Geo.AngleCongruent C O B Z O Y :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      rho
      C O B
      Z Y
      hCrho hOrho hBrho
      hZrho hYrho
      hCOB
      hCZ
      hBY

  have hBOC_ZOY :
      Geo.AngleCongruent B O C Z O Y :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      C O B
      Z O Y).mp
      hMoveFinal

  have hBOC_C'O'B' :
      Geo.AngleCongruent B O C C' O' B' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O C
      Z O Y
      C' O' B'
      hBOC_ZOY
      hFinal

  exact
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      B O C
      C' O' B').mp
      hBOC_C'O'B'

theorem hilbert_space_threeAnglesLessThanFourRight_transport_all_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D E Q F : Geo.Point)
    (A' O' B' C' P' D' E' Q' F' : Geo.Point)
    (hA'sigma : S.OnPlane A' sigma)
    (hO'sigma : S.OnPlane O' sigma)
    (hB'sigma : S.OnPlane B' sigma)
    (hC'sigma : S.OnPlane C' sigma)
    (hP'sigma : S.OnPlane P' sigma)
    (hD'sigma : S.OnPlane D' sigma)
    (hE'sigma : S.OnPlane E' sigma)
    (hQ'sigma : S.OnPlane Q' sigma)
    (hF'sigma : S.OnPlane F' sigma)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hFirst' :
      Not (PrimCollinear Geo A' O' B'))
    (hSecond' :
      Not (PrimCollinear Geo C' P' D'))
    (hThird' :
      Not (PrimCollinear Geo E' Q' F'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B')
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D')
    (hThirdCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertThreeAnglesLessThanFourRightAngles
      Geo
      A' O' B'
      C' P' D'
      E' Q' F' := by

  rcases h with
    ⟨hFirst, hSecond, hThird,
     X, Y,
     hBOX, hDPY,
     hCompare⟩

  --------------------------------------------------------------------
  -- Extend the copied first and second angles in sigma.
  --------------------------------------------------------------------

  have hA'O' : Ne A' O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hFirst'

  have hB'O' : Ne B' O' := by
    intro hEq
    subst B'
    apply hFirst'
    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          A' O' hA'O'
    with
    ⟨l, hA'l, hO'l⟩
    exact ⟨l, hA'l, hO'l, hO'l⟩

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo)
        B' O' hB'O'
    with
    ⟨X', hB'O'X'⟩

  have hB'O'X'data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      B' O' X' hB'O'X'

  have hB'O'X'col :
      PrimCollinear Geo B' O' X' :=
    hB'O'X'data.2.2.2.1

  have hX'sigma :
      S.OnPlane X' sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      B' O' X'
      hB'O'
      hB'sigma hO'sigma
      hB'O'X'col

  have hC'P' : Ne C' P' :=
    hilbert_noncollinear_ne_first
      Geo C' P' D' hSecond'

  have hD'P' : Ne D' P' := by
    intro hEq
    subst D'
    apply hSecond'
    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          C' P' hC'P'
    with
    ⟨l, hC'l, hP'l⟩
    exact ⟨l, hC'l, hP'l, hP'l⟩

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo)
        D' P' hD'P'
    with
    ⟨Y', hD'P'Y'⟩

  have hD'P'Y'data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      D' P' Y' hD'P'Y'

  have hD'P'Y'col :
      PrimCollinear Geo D' P' Y' :=
    hD'P'Y'data.2.2.2.1

  have hY'sigma :
      S.OnPlane Y' sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      D' P' Y'
      hD'P'
      hD'sigma hP'sigma
      hD'P'Y'col

  --------------------------------------------------------------------
  -- Reverse both rays of the original angle congruences so that
  -- Hilbert T14 sees the two linear pairs
  --
  --   B-O-X,   B'-O'-X'
  --
  -- and
  --
  --   D-P-Y,   D'-P'-Y'.
  --------------------------------------------------------------------

  have hBOA_B'O'A' :
      Geo.AngleCongruent
        B O A
        B' O' A' :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      B O A
      A' O' B').mp
      ((Geometry.Geo.angle_congruent_reverse_first
        Geo
        A O B
        A' O' B').mp
        hFirstCong)

  have hDPC_D'P'C' :
      Geo.AngleCongruent
        D P C
        D' P' C' :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      D P C
      C' P' D').mp
      ((Geometry.Geo.angle_congruent_reverse_first
        Geo
        C P D
        C' P' D').mp
        hSecondCong)

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro hCol
    apply hFirst
    rcases hCol with
      ⟨l, hBl, hOl, hAl⟩
    exact ⟨l, hAl, hOl, hBl⟩

  have hB'O'A' :
      Not (PrimCollinear Geo B' O' A') := by
    intro hCol
    apply hFirst'
    rcases hCol with
      ⟨l, hB'l, hO'l, hA'l⟩
    exact ⟨l, hA'l, hO'l, hB'l⟩

  have hDPC :
      Not (PrimCollinear Geo D P C) := by
    intro hCol
    apply hSecond
    rcases hCol with
      ⟨l, hDl, hPl, hCl⟩
    exact ⟨l, hCl, hPl, hDl⟩

  have hD'P'C' :
      Not (PrimCollinear Geo D' P' C') := by
    intro hCol
    apply hSecond'
    rcases hCol with
      ⟨l, hD'l, hP'l, hC'l⟩
    exact ⟨l, hC'l, hP'l, hD'l⟩

  --------------------------------------------------------------------
  -- Spatial T14 transports the two supplementary angles.
  --------------------------------------------------------------------

  have hSuppFirst :
      Geo.AngleCongruent
        A O X
        A' O' X' :=
    hilbert_space_adjacent_angles_congruent_in_plane
      (Geo := Geo)
      sigma
      B O A X
      B' O' A' X'
      hB'sigma
      hO'sigma
      hA'sigma
      hX'sigma
      hBOX
      hB'O'X'
      hBOA
      hB'O'A'
      hBOA_B'O'A'

  have hSuppSecond :
      Geo.AngleCongruent
        C P Y
        C' P' Y' :=
    hilbert_space_adjacent_angles_congruent_in_plane
      (Geo := Geo)
      sigma
      D P C Y
      D' P' C' Y'
      hD'sigma
      hP'sigma
      hC'sigma
      hY'sigma
      hDPY
      hD'P'Y'
      hDPC
      hD'P'C'
      hDPC_D'P'C'

  --------------------------------------------------------------------
  -- The two copied supplementary angles are proper.
  --------------------------------------------------------------------

  have hA'O'X' :
      Not (PrimCollinear Geo A' O' X') := by
    intro hCol

    rcases hCol with
      ⟨l, hA'l, hO'l, hX'l⟩

    rcases hB'O'X'col with
      ⟨m, hB'm, hO'm, hX'm⟩

    have hO'X' : Ne O' X' :=
      hB'O'X'data.2.1

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        O' X' hO'X'
        l m
        hO'l hX'l
        hO'm hX'm

    subst m

    exact hFirst'
      ⟨l, hA'l, hO'l, hB'm⟩

  have hC'P'Y' :
      Not (PrimCollinear Geo C' P' Y') := by
    intro hCol

    rcases hCol with
      ⟨l, hC'l, hP'l, hY'l⟩

    rcases hD'P'Y'col with
      ⟨m, hD'm, hP'm, hY'm⟩

    have hP'Y' : Ne P' Y' :=
      hD'P'Y'data.2.1

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        P' Y' hP'Y'
        l m
        hP'l hY'l
        hP'm hY'm

    subst m

    exact hSecond'
      ⟨l, hC'l, hP'l, hD'm⟩

  --------------------------------------------------------------------
  -- Transport the XI.20-style comparison to the copied supplements
  -- and copied third angle, all lying in sigma.
  --------------------------------------------------------------------

  have hCompare' :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' X'
        C' P' Y'
        E' Q' F' :=
    hilbert_space_twoAnglesGreater_transport_all_in_plane
      (Geo := Geo)
      sigma
      A O X
      C P Y
      E Q F
      A' O' X'
      C' P' Y'
      E' Q' F'
      hA'sigma
      hO'sigma
      hX'sigma
      hC'sigma
      hP'sigma
      hY'sigma
      hE'sigma
      hQ'sigma
      hF'sigma
      hCompare
      hA'O'X'
      hC'P'Y'
      hThird'
      hSuppFirst
      hSuppSecond
      hThirdCong

  exact
    ⟨hFirst',
      hSecond',
      hThird',
      X', Y',
      hB'O'X',
      hD'P'Y',
      hCompare'⟩

/--
If all six named points of an ambient `HilbertAngleLess` relation lie
in `sigma`, then the same strict angle comparison holds in
`PlaneGeo Geo sigma`.
-/
theorem hilbert_space_angleLess_to_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D : Geo.Point)
    (hAsigma : S.OnPlane A sigma)
    (hOsigma : S.OnPlane O sigma)
    (hBsigma : S.OnPlane B sigma)
    (hCsigma : S.OnPlane C sigma)
    (hPsigma : S.OnPlane P sigma)
    (hDsigma : S.OnPlane D sigma)
    (hLess : HilbertAngleLess Geo A O B C P D) :
    HilbertAngleLess
      (PlaneGeo Geo sigma)
      (⟨A, hAsigma⟩ : PlanePoint Geo sigma)
      (⟨O, hOsigma⟩ : PlanePoint Geo sigma)
      (⟨B, hBsigma⟩ : PlanePoint Geo sigma)
      (⟨C, hCsigma⟩ : PlanePoint Geo sigma)
      (⟨P, hPsigma⟩ : PlanePoint Geo sigma)
      (⟨D, hDsigma⟩ : PlanePoint Geo sigma) := by

  rcases hLess with
    ⟨hAOB, hCPD, X, hInside, hAngle⟩

  rcases hInside with
    ⟨H, hCHD, hRayPXH⟩

  have hCHDdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C H D hCHD

  have hCD : Ne C D :=
    hCHDdata.2.2.1

  have hCHDcol :
      PrimCollinear Geo C H D :=
    hCHDdata.2.2.2.1

  have hCDHcol :
      PrimCollinear Geo C D H := by
    rcases hCHDcol with
      ⟨l, hCl, hHl, hDl⟩
    exact ⟨l, hCl, hDl, hHl⟩

  have hHsigma :
      S.OnPlane H sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      C D H
      hCD
      hCsigma hDsigma
      hCDHcol

  have hPH : Ne P H :=
    hRayPXH.2.1.symm

  have hPXHcol :
      PrimCollinear Geo P X H :=
    hRayPXH.2.2.1

  have hPHXcol :
      PrimCollinear Geo P H X := by
    rcases hPXHcol with
      ⟨l, hPl, hXl, hHl⟩
    exact ⟨l, hPl, hHl, hXl⟩

  have hXsigma :
      S.OnPlane X sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      P H X
      hPH
      hPsigma hHsigma
      hPHXcol

  let Ap : PlanePoint Geo sigma := ⟨A, hAsigma⟩
  let Op : PlanePoint Geo sigma := ⟨O, hOsigma⟩
  let Bp : PlanePoint Geo sigma := ⟨B, hBsigma⟩
  let Cp : PlanePoint Geo sigma := ⟨C, hCsigma⟩
  let Pp : PlanePoint Geo sigma := ⟨P, hPsigma⟩
  let Dp : PlanePoint Geo sigma := ⟨D, hDsigma⟩
  let Xp : PlanePoint Geo sigma := ⟨X, hXsigma⟩
  let Hp : PlanePoint Geo sigma := ⟨H, hHsigma⟩

  have hAOBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ap Op Bp) := by
    intro hCol
    apply hAOB
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ap Op Bp hCol
    simpa [Ap, Op, Bp] using h

  have hCPDPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Cp Pp Dp) := by
    intro hCol
    apply hCPD
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Cp Pp Dp hCol
    simpa [Cp, Pp, Dp] using h

  have hCHDPlane :
      (PlaneGeo Geo sigma).Between Cp Hp Dp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        sigma Cp Hp Dp).mpr
    simpa [Cp, Hp, Dp] using hCHD

  have hRayPXHPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma)
        Pp Xp Hp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Pp Xp Hp).mpr
    simpa [Pp, Xp, Hp] using hRayPXH

  have hInsidePlane :
      HilbertRayMeetsSegment
        (PlaneGeo Geo sigma)
        Pp Xp Cp Dp :=
    ⟨Hp, hCHDPlane, hRayPXHPlane⟩

  have hAnglePlane :
      (PlaneGeo Geo sigma).AngleCongruent
        Ap Op Bp Cp Pp Xp := by
    apply
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        sigma
        Ap Op Bp
        Cp Pp Xp).mpr
    simpa [Ap, Op, Bp, Cp, Pp, Xp] using hAngle

  exact
    ⟨hAOBPlane,
      hCPDPlane,
      Xp,
      hInsidePlane,
      hAnglePlane⟩


/--
If all nine named points of an ambient
`HilbertTwoAnglesGreaterThanAngle` relation lie in `sigma`, then the
same comparison holds in `PlaneGeo Geo sigma`.
-/


theorem hilbert_space_twoAnglesGreater_to_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D E Q F : Geo.Point)
    (hAsigma : S.OnPlane A sigma)
    (hOsigma : S.OnPlane O sigma)
    (hBsigma : S.OnPlane B sigma)
    (hCsigma : S.OnPlane C sigma)
    (hPsigma : S.OnPlane P sigma)
    (hDsigma : S.OnPlane D sigma)
    (hEsigma : S.OnPlane E sigma)
    (hQsigma : S.OnPlane Q sigma)
    (hFsigma : S.OnPlane F sigma)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F) :
    HilbertTwoAnglesGreaterThanAngle
      (PlaneGeo Geo sigma)
      (⟨A, hAsigma⟩ : PlanePoint Geo sigma)
      (⟨O, hOsigma⟩ : PlanePoint Geo sigma)
      (⟨B, hBsigma⟩ : PlanePoint Geo sigma)
      (⟨C, hCsigma⟩ : PlanePoint Geo sigma)
      (⟨P, hPsigma⟩ : PlanePoint Geo sigma)
      (⟨D, hDsigma⟩ : PlanePoint Geo sigma)
      (⟨E, hEsigma⟩ : PlanePoint Geo sigma)
      (⟨Q, hQsigma⟩ : PlanePoint Geo sigma)
      (⟨F, hFsigma⟩ : PlanePoint Geo sigma) := by

  rcases h with
    ⟨hFirst, hSecond, hTarget, hCore⟩

  let Ap : PlanePoint Geo sigma := ⟨A, hAsigma⟩
  let Op : PlanePoint Geo sigma := ⟨O, hOsigma⟩
  let Bp : PlanePoint Geo sigma := ⟨B, hBsigma⟩
  let Cp : PlanePoint Geo sigma := ⟨C, hCsigma⟩
  let Pp : PlanePoint Geo sigma := ⟨P, hPsigma⟩
  let Dp : PlanePoint Geo sigma := ⟨D, hDsigma⟩
  let Ep : PlanePoint Geo sigma := ⟨E, hEsigma⟩
  let Qp : PlanePoint Geo sigma := ⟨Q, hQsigma⟩
  let Fp : PlanePoint Geo sigma := ⟨F, hFsigma⟩

  have hFirstPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ap Op Bp) := by
    intro hCol
    apply hFirst
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ap Op Bp hCol
    simpa [Ap, Op, Bp] using h

  have hSecondPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Cp Pp Dp) := by
    intro hCol
    apply hSecond
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Cp Pp Dp hCol
    simpa [Cp, Pp, Dp] using h

  have hTargetPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ep Qp Fp) := by
    intro hCol
    apply hTarget
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ep Qp Fp hCol
    simpa [Ep, Qp, Fp] using h

  refine
    ⟨hFirstPlane,
      hSecondPlane,
      hTargetPlane,
      ?_⟩

  cases hCore with

  | inl hLess =>

      have hLessPlane :
          HilbertAngleLess
            (PlaneGeo Geo sigma)
            Ep Qp Fp
            Ap Op Bp :=
        hilbert_space_angleLess_to_plane
          (Geo := Geo)
          sigma
          E Q F
          A O B
          hEsigma hQsigma hFsigma
          hAsigma hOsigma hBsigma
          hLess

      exact Or.inl hLessPlane

  | inr hRest =>

      cases hRest with

      | inl hEq =>

          have hEqPlane :
              (PlaneGeo Geo sigma).AngleCongruent
                Ep Qp Fp
                Ap Op Bp := by
            apply
              (planeGeo_angleCongruent_iff_ambient
                (Geo := Geo)
                sigma
                Ep Qp Fp
                Ap Op Bp).mpr
            simpa [Ep, Qp, Fp, Ap, Op, Bp] using hEq

          exact Or.inr (Or.inl hEqPlane)

      | inr hDecomp =>

          rcases hDecomp with
            ⟨X, hInside, hFirstPart, hRemainder⟩

          rcases hInside with
            ⟨H, hEHF, hRayQXH⟩

          have hEHFdata :=
            HilbertSpaceOrder.between_incidence
              (Geo := Geo)
              E H F hEHF

          have hEF : Ne E F :=
            hEHFdata.2.2.1

          have hEHFcol :
              PrimCollinear Geo E H F :=
            hEHFdata.2.2.2.1

          have hEFHcol :
              PrimCollinear Geo E F H := by
            rcases hEHFcol with
              ⟨l, hEl, hHl, hFl⟩
            exact ⟨l, hEl, hFl, hHl⟩

          have hHsigma :
              S.OnPlane H sigma :=
            hilbert_onPlane_of_primCollinear_with_two_on_plane
              (Geo := Geo)
              sigma
              E F H
              hEF
              hEsigma hFsigma
              hEFHcol

          have hQH : Ne Q H :=
            hRayQXH.2.1.symm

          have hQXHcol :
              PrimCollinear Geo Q X H :=
            hRayQXH.2.2.1

          have hQHXcol :
              PrimCollinear Geo Q H X := by
            rcases hQXHcol with
              ⟨l, hQl, hXl, hHl⟩
            exact ⟨l, hQl, hHl, hXl⟩

          have hXsigma :
              S.OnPlane X sigma :=
            hilbert_onPlane_of_primCollinear_with_two_on_plane
              (Geo := Geo)
              sigma
              Q H X
              hQH
              hQsigma hHsigma
              hQHXcol

          let Xp : PlanePoint Geo sigma :=
            ⟨X, hXsigma⟩

          let Hp : PlanePoint Geo sigma :=
            ⟨H, hHsigma⟩

          have hEHFPlane :
              (PlaneGeo Geo sigma).Between
                Ep Hp Fp := by
            apply
              (planeGeo_between
                (Geo := Geo)
                sigma Ep Hp Fp).mpr
            simpa [Ep, Hp, Fp] using hEHF

          have hRayQXHPlane :
              HilbertSameRay
                (PlaneGeo Geo sigma)
                Qp Xp Hp := by
            apply
              (planeGeo_sameRay_iff_ambient
                (Geo := Geo)
                sigma Qp Xp Hp).mpr
            simpa [Qp, Xp, Hp] using hRayQXH

          have hInsidePlane :
              HilbertRayMeetsSegment
                (PlaneGeo Geo sigma)
                Qp Xp Ep Fp :=
            ⟨Hp, hEHFPlane, hRayQXHPlane⟩

          have hFirstPartPlane :
              (PlaneGeo Geo sigma).AngleCongruent
                Ap Op Bp
                Ep Qp Xp := by
            apply
              (planeGeo_angleCongruent_iff_ambient
                (Geo := Geo)
                sigma
                Ap Op Bp
                Ep Qp Xp).mpr
            simpa [Ap, Op, Bp, Ep, Qp, Xp] using hFirstPart

          have hRemainderPlane :
              HilbertAngleLess
                (PlaneGeo Geo sigma)
                Xp Qp Fp
                Cp Pp Dp :=
            hilbert_space_angleLess_to_plane
              (Geo := Geo)
              sigma
              X Q F
              C P D
              hXsigma hQsigma hFsigma
              hCsigma hPsigma hDsigma
              hRemainder

          exact
            Or.inr
              (Or.inr
                ⟨Xp,
                 hInsidePlane,
                 hFirstPartPlane,
                 hRemainderPlane⟩)


/--
If all nine named points of an ambient
`HilbertThreeAnglesLessThanFourRightAngles` relation lie in `sigma`,
then the same four-right-angle bound holds in `PlaneGeo Geo sigma`.
-/


theorem hilbert_space_threeAnglesFourRight_to_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (A O B C P D E Q F : Geo.Point)
    (hAsigma : S.OnPlane A sigma)
    (hOsigma : S.OnPlane O sigma)
    (hBsigma : S.OnPlane B sigma)
    (hCsigma : S.OnPlane C sigma)
    (hPsigma : S.OnPlane P sigma)
    (hDsigma : S.OnPlane D sigma)
    (hEsigma : S.OnPlane E sigma)
    (hQsigma : S.OnPlane Q sigma)
    (hFsigma : S.OnPlane F sigma)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    HilbertThreeAnglesLessThanFourRightAngles
      (PlaneGeo Geo sigma)
      (⟨A, hAsigma⟩ : PlanePoint Geo sigma)
      (⟨O, hOsigma⟩ : PlanePoint Geo sigma)
      (⟨B, hBsigma⟩ : PlanePoint Geo sigma)
      (⟨C, hCsigma⟩ : PlanePoint Geo sigma)
      (⟨P, hPsigma⟩ : PlanePoint Geo sigma)
      (⟨D, hDsigma⟩ : PlanePoint Geo sigma)
      (⟨E, hEsigma⟩ : PlanePoint Geo sigma)
      (⟨Q, hQsigma⟩ : PlanePoint Geo sigma)
      (⟨F, hFsigma⟩ : PlanePoint Geo sigma) := by

  rcases h with
    ⟨hFirst, hSecond, hThird,
     X, Y,
     hBOX, hDPY,
     hCompare⟩

  let Ap : PlanePoint Geo sigma := ⟨A, hAsigma⟩
  let Op : PlanePoint Geo sigma := ⟨O, hOsigma⟩
  let Bp : PlanePoint Geo sigma := ⟨B, hBsigma⟩
  let Cp : PlanePoint Geo sigma := ⟨C, hCsigma⟩
  let Pp : PlanePoint Geo sigma := ⟨P, hPsigma⟩
  let Dp : PlanePoint Geo sigma := ⟨D, hDsigma⟩
  let Ep : PlanePoint Geo sigma := ⟨E, hEsigma⟩
  let Qp : PlanePoint Geo sigma := ⟨Q, hQsigma⟩
  let Fp : PlanePoint Geo sigma := ⟨F, hFsigma⟩

  have hFirstPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ap Op Bp) := by
    intro hCol
    apply hFirst
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ap Op Bp hCol
    simpa [Ap, Op, Bp] using h

  have hSecondPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Cp Pp Dp) := by
    intro hCol
    apply hSecond
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Cp Pp Dp hCol
    simpa [Cp, Pp, Dp] using h

  have hThirdPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ep Qp Fp) := by
    intro hCol
    apply hThird
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ep Qp Fp hCol
    simpa [Ep, Qp, Fp] using h

  have hBOXdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      B O X hBOX

  have hBO : Ne B O :=
    hBOXdata.1

  have hBOXcol :
      PrimCollinear Geo B O X :=
    hBOXdata.2.2.2.1

  have hXsigma :
      S.OnPlane X sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      B O X
      hBO
      hBsigma hOsigma
      hBOXcol

  have hDPYdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      D P Y hDPY

  have hDP : Ne D P :=
    hDPYdata.1

  have hDPYcol :
      PrimCollinear Geo D P Y :=
    hDPYdata.2.2.2.1

  have hYsigma :
      S.OnPlane Y sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      D P Y
      hDP
      hDsigma hPsigma
      hDPYcol

  let Xp : PlanePoint Geo sigma := ⟨X, hXsigma⟩
  let Yp : PlanePoint Geo sigma := ⟨Y, hYsigma⟩

  have hBOXPlane :
      (PlaneGeo Geo sigma).Between Bp Op Xp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        sigma Bp Op Xp).mpr
    simpa [Bp, Op, Xp] using hBOX

  have hDPYPlane :
      (PlaneGeo Geo sigma).Between Dp Pp Yp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        sigma Dp Pp Yp).mpr
    simpa [Dp, Pp, Yp] using hDPY

  have hComparePlane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo sigma)
        Ap Op Xp
        Cp Pp Yp
        Ep Qp Fp :=
    hilbert_space_twoAnglesGreater_to_plane
      (Geo := Geo)
      sigma
      A O X
      C P Y
      E Q F
      hAsigma hOsigma hXsigma
      hCsigma hPsigma hYsigma
      hEsigma hQsigma hFsigma
      hCompare

  exact
    ⟨hFirstPlane,
      hSecondPlane,
      hThirdPlane,
      Xp, Yp,
      hBOXPlane,
      hDPYPlane,
      hComparePlane⟩

end Geometry

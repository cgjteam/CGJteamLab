import CGJteamLab.Coxeter.E4AmbientTriangleSAS

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 ambient triangle congruence: SSS layer

This module is the corrected-E4 analogue of the old spatial SSS theorem

  hilbert_space_sss_angleA_in_plane.

The source triangle is ambient.  The target triangle is carried by one
explicit ambient 2-plane.  No global `HilbertCongruence Geo` instance is
introduced.

The proof reconstructs the source angle inside the target plane using
corrected ambient III.4, lays off the second source side on that ray,
uses the corrected ambient SAS theorem from `E4AmbientTriangleSAS`, and
finally closes the comparison inside the target `PlaneGeo` by ordinary
planar SSS.
-/

/--
Corrected ambient E4 SSS, angle-at-the-first-vertex form.

The source triangle `ABC` is ambient.  The target triangle `A'B'C'`
lies in the explicit plane `sigma`.
-/
theorem hilbert4D_ambient_sss_angleA_in_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (sigma : Q.toHilbertSpacePrimitive.Plane)
    (A B C : Geo.Point)
    (A' B' C' : PlanePoint Geo sigma)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not
        (PrimCollinear
          Geo A'.1 B'.1 C'.1))
    (hAB :
      Geo.Congruent A B A'.1 B'.1)
    (hBC :
      Geo.Congruent B C B'.1 C'.1)
    (hAC :
      Geo.Congruent A C A'.1 C'.1) :
    Geo.AngleCongruent
      B A C
      B'.1 A'.1 C'.1 := by

  have hBAC :
      Not (PrimCollinear Geo B A C) := by

    intro h

    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  have hA'B' :
      Ne A'.1 B'.1 :=
    hilbert_noncollinear_ne_first
      Geo
      A'.1 B'.1 C'.1
      hA'B'C'

  have hA'B'Plane :
      Ne A' B' := by

    intro h
    apply hA'B'
    exact congrArg Subtype.val h

  let : HilbertPlaneIncidence (PlaneGeo Geo sigma) :=
    planeGeoHilbertPlaneIncidence4_corrected
      (Geo := Geo)
      sigma
      A'.1 B'.1 C'.1
      A'.2 B'.2 C'.2
      hA'B'C'

  have hA'B'C'Plane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          A' B' C') := by

    intro hPlane

    exact
      hA'B'C'
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma
          A' B' C'
          hPlane)

  let : HilbertCongruence (PlaneGeo Geo sigma) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      sigma
      A'.1 B'.1 C'.1
      A'.2 B'.2 C'.2
      hA'B'C'

  have hBaseExists :=
    HilbertPlaneIncidence.line_through
      (Geo := PlaneGeo Geo sigma)
      A' B'
      hA'B'Plane

  let base : PlaneLine Geo sigma :=
    Classical.choose hBaseExists

  have hBaseData :=
    Classical.choose_spec hBaseExists

  have hA'base :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        A' base :=
    hBaseData.1

  have hB'base :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        B' base :=
    hBaseData.2

  have hC'offBase :
      Not
        (HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo sigma)
          C' base) := by

    intro hC'base

    exact
      hA'B'C'Plane
        (Exists.intro base
          (And.intro hA'base
            (And.intro hB'base hC'base)))

  have hA'baseAmbient :
      H.OnLine A'.1 base.1 := by

    change PlaneOnLine Geo A' base at hA'base
    exact hA'base

  have hB'baseAmbient :
      H.OnLine B'.1 base.1 := by

    change PlaneOnLine Geo B' base at hB'base
    exact hB'base

  have hC'offBaseAmbient :
      Not (H.OnLine C'.1 base.1) := by

    change Not (PlaneOnLine Geo C' base) at hC'offBase
    exact hC'offBase

  have hXExists :=
    H4C.angle_construction_in_plane
      B A C
      B'.1 A'.1 C'.1
      hBAC
      hA'B'.symm
      sigma
      base.1
      base.2
      hB'baseAmbient
      hA'baseAmbient
      C'.2
      hC'offBaseAmbient

  let X : Geo.Point :=
    Classical.choose hXExists

  have hXData :=
    Classical.choose_spec hXExists

  have hXC'space :
      HilbertSameSideInPlane
        Geo X C'.1 base.1 sigma :=
    hXData.1

  have hAngleX :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 X :=
    hXData.2.1

  have hXsigma :
      Q.toHilbertSpacePrimitive.OnPlane X sigma :=
    hXC'space.1

  have hXoffBase :
      Not (H.OnLine X base.1) :=
    hXC'space.2.2.1

  have hA'X :
      Ne A'.1 X := by

    intro h

    apply hXoffBase

    rw [<- h]

    exact hA'baseAmbient

  have hYExists :=
    H4C.segment_construction
      A C
      A'.1 X
      hA'X

  let Y : Geo.Point :=
    Classical.choose hYExists

  have hYData :=
    Classical.choose_spec hYExists

  have hRayXY :
      HilbertSameRay
        Geo A'.1 X Y :=
    hYData.1

  have hA'Y_AC :
      Geo.Congruent
        A'.1 Y A C :=
    hYData.2

  have hA'Y :
      Ne A'.1 Y :=
    hRayXY.2.1.symm

  have hYsigma :
      Q.toHilbertSpacePrimitive.OnPlane
        Y sigma :=
    hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
      (Geo := Geo)
      sigma
      A'.1 X Y
      hA'X
      A'.2 hXsigma
      hRayXY.2.2.1

  let Xp : PlanePoint Geo sigma :=
    Subtype.mk X hXsigma

  let Yp : PlanePoint Geo sigma :=
    Subtype.mk Y hYsigma

  have hRayXYPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma)
        A' Xp Yp := by

    apply
      (planeGeo_sameRay_iff_ambient4_corrected
        (Geo := Geo)
        sigma
        A' Xp Yp).mpr

    simpa [Xp, Yp] using hRayXY

  have hXoffBasePlane :
      Not
        (HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo sigma)
          Xp base) := by

    intro h

    apply hXoffBase

    change H.OnLine X base.1 at h

    exact h

  have hB'A'XPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          B' A' Xp) :=
    hilbert_not_collinear_of_off_line
      (PlaneGeo Geo sigma)
      B' A' Xp
      base
      hA'B'Plane.symm
      hB'base hA'base
      hXoffBasePlane

  have hRayB'B'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma)
        A' B' B' :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      A' B'
      hA'B'Plane.symm

  have hB'A'YPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          B' A' Yp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      B' A' Xp
      B' Yp
      hB'A'XPlane
      hRayB'B'Plane
      hRayXYPlane

  have hA'B'YPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          A' B' Yp) := by

    intro h

    exact
      hB'A'YPlane
        (PrimCollinearSwap
          (PlaneGeo Geo sigma)
          A' B' Yp h)

  have hA'B'YAmbient :
      Not
        (PrimCollinear
          Geo A'.1 B'.1 Y) := by

    have h :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        sigma
        A' B' Yp
        hA'B'
        hA'B'YPlane

    simpa [Yp] using h

  have hTargetAngleXYPlane :
      (PlaneGeo Geo sigma).Angle
          B' A' Xp =
        (PlaneGeo Geo sigma).Angle
          B' A' Yp :=
    hilbert_angle_eq_of_sameRay_second
      (PlaneGeo Geo sigma)
      A' B' Xp Yp
      hRayXYPlane

  have hPlaneAngleXX :
      (PlaneGeo Geo sigma).AngleCongruent
        B' A' Xp
        B' A' Xp :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo sigma)
      B' A' Xp
      hB'A'XPlane

  have hPlaneAngleXY :
      (PlaneGeo Geo sigma).AngleCongruent
        B' A' Xp
        B' A' Yp := by

    unfold Geometry.Geo.AngleCongruent
      at hPlaneAngleXX

    unfold Geometry.Geo.AngleCongruent

    rw [<- hTargetAngleXYPlane]

    exact hPlaneAngleXX

  have hAmbientAngleXY :
      Geo.AngleCongruent
        B'.1 A'.1 X
        B'.1 A'.1 Y := by

    have h :=
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        sigma
        B' A' Xp
        B' A' Yp).mp
        hPlaneAngleXY

    simpa [Xp, Yp] using h

  have hAngleY :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A C
      B'.1 A'.1 X
      B'.1 A'.1 Y
      hAngleX
      hAmbientAngleXY

  have hAC_A'Y :
      Geo.Congruent
        A C
        A'.1 Y :=
    hilbert4D_ambient_congruent_symm_corrected
      (Geo := Geo)
      A'.1 Y
      A C
      hA'Y_AC

  have hSAS :=
    hilbert4D_ambient_sas_third_side_and_angle_corrected
      (Geo := Geo)
      sigma
      A B C
      A' B' Yp
      hABC
      hA'B'YAmbient
      hAB
      hAC_A'Y
      hAngleY

  have hBC_B'Y :
      Geo.Congruent
        B C
        B'.1 Y := by

    simpa [Yp] using hSAS.1

  have hB'Y_B'C' :
      Geo.Congruent
        B'.1 Y
        B'.1 C'.1 :=
    H4C.segment_congruence_common
      B C
      B'.1 Y
      B'.1 C'.1
      hBC_B'Y
      hBC

  have hA'Y_A'C' :
      Geo.Congruent
        A'.1 Y
        A'.1 C'.1 :=
    H4C.segment_congruence_common
      A C
      A'.1 Y
      A'.1 C'.1
      hAC_A'Y
      hAC

  have hA'B'ReflAmbient :
      Geo.Congruent
        A'.1 B'.1
        A'.1 B'.1 :=
    hilbert4D_ambient_congruent_reflexive_corrected
      (Geo := Geo)
      A'.1 B'.1

  have hA'B'ReflPlane :
      (PlaneGeo Geo sigma).Congruent
        A' B'
        A' B' :=
    (planeGeo_congruent
      (Geo := Geo)
      sigma
      A' B' A' B').mpr
      hA'B'ReflAmbient

  have hB'Y_B'C'Plane :
      (PlaneGeo Geo sigma).Congruent
        B' Yp
        B' C' := by

    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma
        B' Yp B' C').mpr

    simpa [Yp] using hB'Y_B'C'

  have hA'Y_A'C'Plane :
      (PlaneGeo Geo sigma).Congruent
        A' Yp
        A' C' := by

    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma
        A' Yp A' C').mpr

    simpa [Yp] using hA'Y_A'C'

  have hPlanarSSS :=
    HilbertSSS
      (PlaneGeo Geo sigma)
      A' B' Yp
      A' B' C'
      hA'B'YPlane
      hA'B'ReflPlane
      hB'Y_B'C'Plane
      hA'Y_A'C'Plane

  have hPlaneAngle :
      (PlaneGeo Geo sigma).AngleCongruent
        B' A' Yp
        B' A' C' :=
    hPlanarSSS.2.angleA

  have hAmbientAngle :
      Geo.AngleCongruent
        B'.1 A'.1 Y
        B'.1 A'.1 C'.1 := by

    have h :=
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        sigma
        B' A' Yp
        B' A' C').mp
        hPlaneAngle

    simpa [Yp] using h

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A C
      B'.1 A'.1 Y
      B'.1 A'.1 C'.1
      hAngleY
      hAmbientAngle

end Geometry

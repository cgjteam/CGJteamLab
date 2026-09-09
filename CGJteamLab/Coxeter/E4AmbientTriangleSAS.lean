import CGJteamLab.Coxeter.E4HyperplaneReflectionOrderTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 ambient triangle congruence: SAS layer

This module reconstructs the dimension-safe E4 analogue of the old
spatial SAS infrastructure from `Hilbert3DInterface`.

No ambient `HilbertCongruence Geo` instance is installed.

The corrected ambient Group III interface already contains the spatial
SAS axiom itself.  The only additional work needed here is:

* expose both remaining angle conclusions;
* recover the third corresponding side when the target triangle is
  carried by one explicit ambient plane.

The second step uses the target `PlaneGeo` only for the III.4 uniqueness
argument.  This is the same architecture as the old Book XI proof, but
with the corrected genuine-E4 hierarchy.
-/

/--
The two remaining angle conclusions of corrected ambient E4 SAS.

The two triangles may lie in different ambient planes.
-/
theorem hilbert4D_ambient_sas_remaining_angles_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (A B C A' B' C' : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear Geo A' B' C'))
    (hAB :
      Geo.Congruent A B A' B')
    (hAC :
      Geo.Congruent A C A' C')
    (hAngleA :
      Geo.AngleCongruent B A C B' A' C') :
    Geo.AngleCongruent A B C A' B' C' /\
    Geo.AngleCongruent A C B A' C' B' := by

  constructor

  next =>
    exact
      H4C.sas
        A B C
        A' B' C'
        hABC hA'B'C'
        hAB hAC hAngleA

  next =>
    have hACB :
        Not (PrimCollinear Geo A C B) := by

      intro h
      exact
        hABC
          (PrimCollinearRotate
            Geo A C B h)

    have hA'C'B' :
        Not (PrimCollinear Geo A' C' B') := by

      intro h
      exact
        hA'B'C'
          (PrimCollinearRotate
            Geo A' C' B' h)

    have hAngleARev :
        Geo.AngleCongruent
          C A B
          C' A' B' :=
      (Geometry.Geo.angle_congruent_reverse_second
        Geo
        C A B
        B' A' C').mp
        ((Geometry.Geo.angle_congruent_reverse_first
          Geo
          B A C
          B' A' C').mp
          hAngleA)

    exact
      H4C.sas
        A C B
        A' C' B'
        hACB hA'C'B'
        hAC hAB hAngleARev


/--
Corrected ambient E4 SAS, third-side-and-angle form.

The source triangle `ABC` is ambient.  The target triangle is supplied
as three points of one explicit ambient plane `sigma`.

The theorem returns

    BC ~= B'C'

and the angle at `C`.

The proof uses the ambient corrected SAS axiom for angle information,
then performs only the III.4 uniqueness step in `PlaneGeo Geo sigma`.
-/
theorem hilbert4D_ambient_sas_third_side_and_angle_corrected
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
    (hAC :
      Geo.Congruent A C A'.1 C'.1)
    (hAngleA :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 C'.1) :
    Geo.Congruent B C B'.1 C'.1 /\
    Geo.AngleCongruent
      A C B
      A'.1 C'.1 B'.1 := by

  have hA'B' :
      Ne A'.1 B'.1 :=
    hilbert_noncollinear_ne_first
      Geo
      A'.1 B'.1 C'.1
      hA'B'C'

  have hA'B'Plane :
      Ne A' B' := by

    intro hEq
    apply hA'B'
    exact congrArg Subtype.val hEq

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

  have hAngles :
      Geo.AngleCongruent
          A B C
          A'.1 B'.1 C'.1 /\
      Geo.AngleCongruent
          A C B
          A'.1 C'.1 B'.1 :=
    hilbert4D_ambient_sas_remaining_angles_corrected
      (Geo := Geo)
      A B C
      A'.1 B'.1 C'.1
      hABC hA'B'C'
      hAB hAC hAngleA

  have hB'C'A' :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          B' C' A') := by

    intro h

    exact
      hA'B'C'Plane
        (PrimCollinearCycle
          (PlaneGeo Geo sigma)
          C' A' B'
          (PrimCollinearCycle
            (PlaneGeo Geo sigma)
            B' C' A' h))

  have hB'C'Plane :
      Ne B' C' :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo sigma)
      B' C' A'
      hB'C'A'

  have hB'C' :
      Ne B'.1 C'.1 := by

    intro h
    apply hB'C'Plane
    exact Subtype.ext h

  have hXExists :=
    H4C.segment_construction
      B C
      B'.1 C'.1
      hB'C'

  let X : Geo.Point :=
    Classical.choose hXExists

  have hData :=
    Classical.choose_spec hXExists

  have hRayAmbient :
      HilbertSameRay
        Geo B'.1 C'.1 X :=
    hData.1

  have hB'X_BC :
      Geo.Congruent
        B'.1 X B C :=
    hData.2

  have hB'X :
      Ne B'.1 X :=
    hRayAmbient.2.1.symm

  have hXsigma :
      Q.toHilbertSpacePrimitive.OnPlane
        X sigma :=
    hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
      (Geo := Geo)
      sigma
      B'.1 C'.1 X
      hB'C'
      B'.2 C'.2
      hRayAmbient.2.2.1

  let Xp : PlanePoint Geo sigma :=
    Subtype.mk X hXsigma

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma)
        B' C' Xp := by

    apply
      (planeGeo_sameRay_iff_ambient4_corrected
        (Geo := Geo)
        sigma
        B' C' Xp).mpr

    simpa [Xp] using hRayAmbient

  have hBaseExists :=
    HilbertPlaneIncidence.line_through
      (Geo := PlaneGeo Geo sigma)
      B' C'
      hB'C'Plane

  let base : PlaneLine Geo sigma :=
    Classical.choose hBaseExists

  have hBaseData :=
    Classical.choose_spec hBaseExists

  have hB'base :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        B' base :=
    hBaseData.1

  have hC'base :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        C' base :=
    hBaseData.2

  have hXbase :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        Xp base :=
    hilbert_collinear_on_line
      (PlaneGeo Geo sigma)
      B' C' Xp
      base
      hB'C'Plane
      hB'base hC'base
      hRayPlane.2.2.1

  have hA'base :
      Not
        (HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo sigma)
          A' base) := by

    intro h

    exact
      hA'B'C'Plane
        (Exists.intro base
          (And.intro h
            (And.intro hB'base hC'base)))

  have hCrossExists :=
    HilbertPlaneIncidence.line_through
      (Geo := PlaneGeo Geo sigma)
      A' B'
      hA'B'Plane

  let cross : PlaneLine Geo sigma :=
    Classical.choose hCrossExists

  have hCrossData :=
    Classical.choose_spec hCrossExists

  have hA'cross :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        A' cross :=
    hCrossData.1

  have hB'cross :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sigma)
        B' cross :=
    hCrossData.2

  have hSideXC' :
      HilbertSameSide
        (PlaneGeo Geo sigma)
        Xp C' cross :=
    hilbert_sameRay_points_sameSide
      (PlaneGeo Geo sigma)
      B' C' Xp C' A'
      base cross
      hB'base hC'base
      hB'cross hA'cross
      hA'base
      hRayPlane
      (hilbert_sameRay_refl
        (PlaneGeo Geo sigma)
        B' C'
        hB'C'Plane.symm)

  have hA'B'XPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          A' B' Xp) := by

    intro h

    exact
      (hilbert_not_collinear_of_off_line
        (PlaneGeo Geo sigma)
        B' Xp A'
        base
        (by
          intro hEq
          apply hB'X
          exact
            congrArg
              Subtype.val hEq)
        hB'base hXbase
        hA'base)
        (PrimCollinearCycle
          (PlaneGeo Geo sigma)
          A' B' Xp h)

  have hTargetAngleEq :
      (PlaneGeo Geo sigma).Angle
          A' B' C' =
        (PlaneGeo Geo sigma).Angle
          A' B' Xp :=
    hilbert_angle_eq_of_sameRay_second
      (PlaneGeo Geo sigma)
      B' A' C' Xp
      hRayPlane

  have hTargetRefl :
      (PlaneGeo Geo sigma).AngleCongruent
        A' B' C'
        A' B' C' :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo sigma)
      A' B' C'
      hA'B'C'Plane

  have hTargetCongPlane :
      (PlaneGeo Geo sigma).AngleCongruent
        A' B' C'
        A' B' Xp := by

    unfold Geometry.Geo.AngleCongruent
      at hTargetRefl
    unfold Geometry.Geo.AngleCongruent

    rw [hTargetAngleEq.symm]

    exact hTargetRefl

  have hTargetCongAmbient :
      Geo.AngleCongruent
        A'.1 B'.1 C'.1
        A'.1 B'.1 X := by

    have h :=
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        sigma
        A' B' C'
        A' B' Xp).mp
        hTargetCongPlane

    simpa [Xp] using h

  have hAngleB_X :
      Geo.AngleCongruent
        A B C
        A'.1 B'.1 X :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A B C
      A'.1 B'.1 C'.1
      A'.1 B'.1 X
      hAngles.1
      hTargetCongAmbient

  have hB'A'XPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          B' A' Xp) := by

    intro h

    exact
      hA'B'XPlane
        (PrimCollinearSwap
          (PlaneGeo Geo sigma)
          B' A' Xp h)

  have hB'A'XAmbient :
      Not
        (PrimCollinear
          Geo B'.1 A'.1 X) := by

    have h :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        sigma
        B' A' Xp
        hA'B'.symm
        hB'A'XPlane

    simpa [Xp] using h

  have hBAC :
      Not (PrimCollinear Geo B A C) := by

    intro h

    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  have hBA_B'A' :
      Geo.Congruent
        B A B'.1 A'.1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B A
      A'.1 B'.1).mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        A B
        A'.1 B'.1).mp
        hAB)

  have hBC_B'X :
      Geo.Congruent
        B C B'.1 X :=
    hilbert4D_ambient_congruent_symm_corrected
      (Geo := Geo)
      B'.1 X
      B C
      hB'X_BC

  have hAngleAX :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 X :=
    H4C.sas
      B A C
      B'.1 A'.1 X
      hBAC hB'A'XAmbient
      hBA_B'A'
      hBC_B'X
      hAngleB_X

  have hC'crossOff :
      Not
        (H.OnLine
          C'.1 cross.1) :=
    hSideXC'.2.1

  have hZExists :=
    H4C.angle_construction_in_plane
      B A C
      B'.1 A'.1 C'.1
      hBAC
      hA'B'.symm
      sigma
      cross.1
      cross.2
      hB'cross
      hA'cross
      C'.2
      hC'crossOff

  let Z : Geo.Point :=
    Classical.choose hZExists

  have hZData :=
    Classical.choose_spec hZExists

  have hZC'space :
      HilbertSameSideInPlane
        Geo Z C'.1
        cross.1 sigma :=
    hZData.1

  have hAngleZ :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 Z :=
    hZData.2.1

  have hUnique :=
    hZData.2.2

  have hC'C'Plane :
      HilbertSameSide
        (PlaneGeo Geo sigma)
        C' C' cross :=
    hilbert_sameSide_refl
      (PlaneGeo Geo sigma)
      C' cross
      hSideXC'.2.1

  have hC'C'space :
      HilbertSameSideInPlane
        Geo C'.1 C'.1
        cross.1 sigma :=
    (planeGeo_sameSide_iff_space
      (Geo := Geo)
      sigma
      C' C' cross).mp
      hC'C'Plane

  have hZC'Ray :
      HilbertSameRay
        Geo A'.1 Z C'.1 :=
    hUnique
      C'.1
      hC'C'space
      hAngleA

  have hXC'space :
      HilbertSameSideInPlane
        Geo X C'.1
        cross.1 sigma := by

    have h :=
      (planeGeo_sameSide_iff_space
        (Geo := Geo)
        sigma
        Xp C' cross).mp
        hSideXC'

    simpa [Xp] using h

  have hZXRay :
      HilbertSameRay
        Geo A'.1 Z X :=
    hUnique
      X
      hXC'space
      hAngleAX

  have hXbaseAmbient :
      H.OnLine X base.1 := by

    change
      PlaneOnLine Geo Xp base
        at hXbase

    exact hXbase

  have hC'baseAmbient :
      H.OnLine C'.1 base.1 := by

    change
      PlaneOnLine Geo C' base
        at hC'base

    exact hC'base

  have hA'baseAmbient :
      Not
        (H.OnLine
          A'.1 base.1) := by

    change
      Not
        (PlaneOnLine
          Geo A' base)
        at hA'base

    exact hA'base

  have hXC' :
      X = C'.1 := by

    by_contra hNe

    have hL1Exists :=
      hZXRay.2.2.1

    let l1 : Geo.Line :=
      Classical.choose hL1Exists

    have hL1Data :=
      Classical.choose_spec hL1Exists

    have hA'l1 := hL1Data.1
    have hZl1 := hL1Data.2.1
    have hXl1 := hL1Data.2.2

    have hL2Exists :=
      hZC'Ray.2.2.1

    let l2 : Geo.Line :=
      Classical.choose hL2Exists

    have hL2Data :=
      Classical.choose_spec hL2Exists

    have hA'l2 := hL2Data.1
    have hZl2 := hL2Data.2.1
    have hC'l2 := hL2Data.2.2

    change H.OnLine A'.1 l1 at hA'l1
    change H.OnLine Z l1 at hZl1
    change H.OnLine X l1 at hXl1
    change H.OnLine A'.1 l2 at hA'l2
    change H.OnLine Z l2 at hZl2
    change H.OnLine C'.1 l2 at hC'l2

    have hl1l2 :
        l1 = l2 :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        A'.1 Z
        hZXRay.1.symm
        l1 l2
        hA'l1 hZl1
        hA'l2 hZl2

    have hC'l1 :
        H.OnLine C'.1 l1 := by
      rw [hl1l2]
      exact hC'l2

    have hBaseL1 :
        base.1 = l1 :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        X C'.1
        hNe
        base.1 l1
        hXbaseAmbient
        hC'baseAmbient
        hXl1 hC'l1

    have hA'baseFromL1 :
        H.OnLine A'.1 base.1 := by
      rw [hBaseL1]
      exact hA'l1

    exact
      hA'baseAmbient hA'baseFromL1

  have hB'C'_BC :
      Geo.Congruent
        B'.1 C'.1
        B C := by
    simpa only [hXC'] using hB'X_BC

  have hThird :
      Geo.Congruent
        B C
        B'.1 C'.1 :=
    hilbert4D_ambient_congruent_symm_corrected
      (Geo := Geo)
      B'.1 C'.1
      B C
      hB'C'_BC

  exact
    And.intro
      hThird hAngles.2

end Geometry

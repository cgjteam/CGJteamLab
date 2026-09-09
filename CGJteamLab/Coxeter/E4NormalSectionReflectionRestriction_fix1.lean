import CGJteamLab.Coxeter.E4NormalSectionPlanarSetup_fix1

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal section: restriction of hyperplane reflection to line reflection

This file is the bridge from the corrected E4 normal-section geometry
to the already developed planar Coxeter reflection theory.

There are two conceptual steps.

1. Normal-carrier absorption.

   If a plane N contains one normal r to a hyperplane Sigma, then every
   other Sigma-normal l which passes through a point P of N is contained
   in N.

   * same foot: uniqueness of the normal;
   * different feet: corrected XI.6 gives l parallel to r, and the
     Smith/Wyler carrier theorem absorbs l into N.

2. Reflection restriction.

   Once the reflection carrier l lies in N, the ambient hyperplane
   reflection relation becomes exactly the ordinary IsLineReflection
   relation in PlaneGeo Geo N, with axis N cap Sigma.

No ambient HilbertSpaceIncidence instance is installed.
-/

/--
A Sigma-normal through a point of N is absorbed by N as soon as N
contains one Sigma-normal.
-/
theorem hilbert4D_normal_carrier_absorbed_by_plane_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (N : Q.toHilbertSpacePrimitive.Plane)
    (O F P : Geo.Point)
    (r l : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hPl :
      H.OnLine P l)
    (hPN :
      Q.toHilbertSpacePrimitive.OnPlane P N) :
    HilbertLineInPlane Geo l N := by

  by_cases hFO :
      F = O

  case pos =>
    have hLNormalO :
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo l Sigma O :=
      Eq.mp
        (congrArg
          (fun X : Geo.Point =>
            HilbertLinePerpendicularHyperplaneAt4_corrected
              Geo l Sigma X)
          hFO)
        hLNormal

    have hlr :
        l = r :=
      hilbert4D_normal_same_foot_unique_corrected
        (Geo := Geo)
        Sigma
        l r
        O
        hLNormalO
        hRNormal

    rw [hlr]
    exact hrN

  case neg =>
    have hPar :
        Hilbert4DLinesParallel_corrected
          Geo l r :=
      hilbert4D_normals_to_same_hyperplane_parallel_corrected
        (Geo := Geo)
        Sigma
        l r
        F O
        hFO
        hLNormal
        hRNormal

    let pi : Q.toHilbertSpacePrimitive.Plane :=
      Classical.choose hPar

    have hParData :=
      Classical.choose_spec hPar

    have hlPi :
        HilbertLineInPlane Geo l pi :=
      hParData.1

    have hrPi :
        HilbertLineInPlane Geo r pi :=
      hParData.2.1

    have hDisjoint :
        HilbertLinesDisjoint Geo l r :=
      hParData.2.2

    exact
      hilbert_dimension_free_disjoint_coplanar_line_absorbed_by_plane
        (Geo := Geo)
        N pi
        r l
        P
        hrN
        hrPi
        hlPi
        hPl
        hPN
        hDisjoint


/--
Generic restriction theorem.

The ambient hyperplane-reflection relation becomes the planar
line-reflection relation on N when:

* N contains a Sigma-normal r at O;
* s is the exact trace N cap Sigma;
* axis is the local copy of s in PlaneGeo Geo N.
-/
theorem hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (N : Q.toHilbertSpacePrimitive.Plane)
    [HilbertCongruence (PlaneGeo Geo N)]
    (O : Geo.Point)
    (r s : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (hsN :
      HilbertLineInPlane Geo s N)
    (hTrace :
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X N /\
         Q.OnHyperplane X Sigma) <->
          H.OnLine X s)
    (axis :
      ReflectionAxis (PlaneGeo Geo N))
    (hAxisCarrier :
      axis.carrier =
        (Subtype.mk s hsN : PlaneLine Geo N))
    (Pp Pp' : PlanePoint Geo N)
    (hRefl :
      IsHyperplaneReflection4_corrected
        Geo Sigma Pp.1 Pp'.1) :
    IsLineReflection
      (PlaneGeo Geo N)
      axis Pp Pp' := by

  have hCarrierAmbient :
      axis.carrier.1 = s :=
    congrArg Subtype.val hAxisCarrier

  rcases hRefl with hFixed | hOff

  case inl =>
    apply Or.inl

    have hPs :
        H.OnLine Pp.1 s :=
      (hTrace Pp.1).mp
        (And.intro Pp.2 hFixed.1)

    have hPaxis :
        HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo N)
          Pp axis.carrier := by
      change H.OnLine Pp.1 axis.carrier.1
      rw [hCarrierAmbient]
      exact hPs

    exact
      And.intro
        hPaxis
        (Subtype.ext hFixed.2)

  case inr =>
    apply Or.inr

    have hPoffSigma :
        Not (Q.OnHyperplane Pp.1 Sigma) :=
      hOff.1

    have hPoffAxis :
        Not
          (HilbertIncidence.OnLine
            (Geo := PlaneGeo Geo N)
            Pp axis.carrier) := by

      intro hPaxis

      have hPs :
          H.OnLine Pp.1 s := by
        change H.OnLine Pp.1 axis.carrier.1 at hPaxis
        rw [hCarrierAmbient] at hPaxis
        exact hPaxis

      have hPSigma :
          Q.OnHyperplane Pp.1 Sigma :=
        ((hTrace Pp.1).mpr hPs).2

      exact
        hPoffSigma hPSigma

    have hFootExists :=
      hOff.2

    let F : Geo.Point :=
      Classical.choose hFootExists

    have hFootData :=
      Classical.choose_spec hFootExists

    have hPerpThrough :
        PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F Pp.1 :=
      hFootData.1

    have hMid :
        HilbertIsMidpoint Geo F Pp.1 Pp'.1 :=
      hFootData.2

    have hCarrierExists :=
      hPerpThrough

    let l : Geo.Line :=
      Classical.choose hCarrierExists

    have hCarrierData :=
      Classical.choose_spec hCarrierExists

    have hPl :
        H.OnLine Pp.1 l :=
      hCarrierData.1

    have hLNormal :
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo l Sigma F :=
      hCarrierData.2

    have hFl :
        H.OnLine F l :=
      hLNormal.1

    have hFSigma :
        Q.OnHyperplane F Sigma :=
      hLNormal.2.1

    have hlN :
        HilbertLineInPlane Geo l N :=
      hilbert4D_normal_carrier_absorbed_by_plane_smith
        (Geo := Geo)
        Sigma N
        O F Pp.1
        r l
        hrN
        hRNormal
        hLNormal
        hPl
        Pp.2

    have hFN :
        Q.toHilbertSpacePrimitive.OnPlane F N :=
      hlN F hFl

    have hFs :
        H.OnLine F s :=
      (hTrace F).mp
        (And.intro hFN hFSigma)

    let Fp : PlanePoint Geo N :=
      Subtype.mk F hFN

    let lN : PlaneLine Geo N :=
      Subtype.mk l hlN

    have hFaxis :
        HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo N)
          Fp axis.carrier := by
      change H.OnLine F axis.carrier.1
      rw [hCarrierAmbient]
      exact hFs

    have hAxisInSigma :
        HilbertLineInHyperplane4
          Geo axis.carrier.1 Sigma := by

      intro X hXaxis

      have hXs :
          H.OnLine X s := by
        rw [<- hCarrierAmbient]
        exact hXaxis

      exact
        ((hTrace X).mpr hXs).2

    have hFaxisAmbient :
        H.OnLine F axis.carrier.1 := by
      change H.OnLine F axis.carrier.1 at hFaxis
      exact hFaxis

    have hLperpAxisAmbient :
        HilbertLinesPerpendicularAt
          Geo l axis.carrier.1 F :=
      hLNormal.2.2
        axis.carrier.1
        hAxisInSigma
        hFaxisAmbient

    have hLperpAxisLocal :
        HilbertLinesPerpendicularAt
          (PlaneGeo Geo N)
          lN axis.carrier Fp :=
      (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
        (Geo := Geo)
        N lN axis.carrier Fp).mpr
        hLperpAxisAmbient

    have hMidData :=
      H4O.between_incidence
        Pp.1 F Pp'.1
        hMid.1

    have hPF :
        Ne Pp.1 F :=
      hMidData.1

    have hPFp :
        Ne Pp Fp := by
      intro hEq
      apply hPF
      exact
        congrArg Subtype.val hEq

    have hPplN :
        HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo N)
          Pp lN :=
      hPl

    have hRExists :=
      hilbert_other_point_on_line
        (Geo := PlaneGeo Geo N)
        axis.carrier Fp

    let Rp : PlanePoint Geo N :=
      Classical.choose hRExists

    have hRData :=
      Classical.choose_spec hRExists

    have hRFp :
        Ne Rp Fp :=
      hRData.1

    have hRaxis :
        HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo N)
          Rp axis.carrier :=
      hRData.2

    have hNorm :=
      hilbert_XI4_linesPerpendicularAt_right_angle_of_points
        (PlaneGeo Geo N)
        lN axis.carrier
        Fp
        Pp Rp
        (hilbert_linesPerpendicularAt_ne
          (PlaneGeo Geo N)
          lN axis.carrier Fp
          hLperpAxisLocal)
        hLperpAxisLocal
        hPFp
        hRFp
        hPplN
        hRaxis

    have hRightRFP :
        HilbertRightAngle
          (PlaneGeo Geo N)
          Rp Fp Pp :=
      hilbert_XI4_right_angle_swap
        (PlaneGeo Geo N)
        Pp Fp Rp
        hNorm.1
        hNorm.2

    have hPerpAxis :
        PerpendicularToAxis
          (PlaneGeo Geo N)
          axis Fp Pp := by

      exact
        And.intro hFaxis
          (And.intro hPoffAxis
            (Exists.intro Rp
              (And.intro hRaxis
                (And.intro hRFp hRightRFP))))

    have hMidLocal :
        HilbertIsMidpoint
          (PlaneGeo Geo N)
          Fp Pp Pp' := by

      apply And.intro

      exact
        (planeGeo_between
          (Geo := Geo)
          N Pp Fp Pp').mpr
          hMid.1

      exact
        (planeGeo_congruent
          (Geo := Geo)
          N Fp Pp Fp Pp').mpr
          hMid.2

    exact
      And.intro hPoffAxis
        (Exists.intro Fp
          (And.intro hPerpAxis hMidLocal))


/--
The planar Sigma reflection selected from the packaged normal section.
-/
noncomputable def hilbert4D_normalSectionSigmaLineReflect
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (sec :
      Hilbert4DNormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      Hilbert4DNormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    PlanePoint Geo sec.N := by

  letI : HilbertCongruence (PlaneGeo Geo sec.N) :=
    planar.plane_congruence

  exact
    lineReflect
      (PlaneGeo Geo sec.N)
      planar.sigma_axis P


/--
The planar Tau reflection selected from the packaged normal section.
-/
noncomputable def hilbert4D_normalSectionTauLineReflect
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (sec :
      Hilbert4DNormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      Hilbert4DNormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    PlanePoint Geo sec.N := by

  letI : HilbertCongruence (PlaneGeo Geo sec.N) :=
    planar.plane_congruence

  exact
    lineReflect
      (PlaneGeo Geo sec.N)
      planar.tau_axis P


/--
On the normal section, the corrected E4 Sigma-reflection is exactly the
ordinary planar line reflection in the Sigma trace.
-/
theorem hilbert4D_normalSectionSigmaLineReflect_eq_hyperplaneReflect
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (sec :
      Hilbert4DNormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      Hilbert4DNormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    hilbert4D_normalSectionSigmaLineReflect
        (Geo := Geo)
        Sigma Tau Delta hMeet O hODelta
        sec planar P =
      (Subtype.mk
        (hyperplaneReflect4_corrected Geo Sigma P.1)
        (sec.sigma_reflection_invariant P.1 P.2) :
          PlanePoint Geo sec.N) := by

  letI : HilbertCongruence (PlaneGeo Geo sec.N) :=
    planar.plane_congruence

  let P' : PlanePoint Geo sec.N :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma P.1)
      (sec.sigma_reflection_invariant P.1 P.2)

  have hRestricted :
      IsLineReflection
        (PlaneGeo Geo sec.N)
        planar.sigma_axis
        P P' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := sec.N)
      Sigma O
      sec.sigma_normal sec.s.1
      sec.sigma_normal_in_N
      sec.sigma_normal_at_O
      sec.s_in_N
      sec.sigma_trace_exact
      planar.sigma_axis
      planar.sigma_axis_carrier
      P P'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P.1)

  have hCanonical :
      IsLineReflection
        (PlaneGeo Geo sec.N)
        planar.sigma_axis
        P
        (lineReflect
          (PlaneGeo Geo sec.N)
          planar.sigma_axis P) :=
    lineReflect_spec
      (PlaneGeo Geo sec.N)
      planar.sigma_axis P

  have hEq :
      lineReflect
          (PlaneGeo Geo sec.N)
          planar.sigma_axis P =
        P' :=
    line_reflection_unique
      (PlaneGeo Geo sec.N)
      planar.sigma_axis
      P
      (lineReflect
        (PlaneGeo Geo sec.N)
        planar.sigma_axis P)
      P'
      hCanonical
      hRestricted

  simpa
    [hilbert4D_normalSectionSigmaLineReflect, P']
    using hEq


/--
On the normal section, the corrected E4 Tau-reflection is exactly the
ordinary planar line reflection in the Tau trace.
-/
theorem hilbert4D_normalSectionTauLineReflect_eq_hyperplaneReflect
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (sec :
      Hilbert4DNormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      Hilbert4DNormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    hilbert4D_normalSectionTauLineReflect
        (Geo := Geo)
        Sigma Tau Delta hMeet O hODelta
        sec planar P =
      (Subtype.mk
        (hyperplaneReflect4_corrected Geo Tau P.1)
        (sec.tau_reflection_invariant P.1 P.2) :
          PlanePoint Geo sec.N) := by

  letI : HilbertCongruence (PlaneGeo Geo sec.N) :=
    planar.plane_congruence

  let P' : PlanePoint Geo sec.N :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Tau P.1)
      (sec.tau_reflection_invariant P.1 P.2)

  have hRestricted :
      IsLineReflection
        (PlaneGeo Geo sec.N)
        planar.tau_axis
        P P' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := sec.N)
      Tau O
      sec.tau_normal sec.t.1
      sec.tau_normal_in_N
      sec.tau_normal_at_O
      sec.t_in_N
      sec.tau_trace_exact
      planar.tau_axis
      planar.tau_axis_carrier
      P P'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Tau P.1)

  have hCanonical :
      IsLineReflection
        (PlaneGeo Geo sec.N)
        planar.tau_axis
        P
        (lineReflect
          (PlaneGeo Geo sec.N)
          planar.tau_axis P) :=
    lineReflect_spec
      (PlaneGeo Geo sec.N)
      planar.tau_axis P

  have hEq :
      lineReflect
          (PlaneGeo Geo sec.N)
          planar.tau_axis P =
        P' :=
    line_reflection_unique
      (PlaneGeo Geo sec.N)
      planar.tau_axis
      P
      (lineReflect
        (PlaneGeo Geo sec.N)
        planar.tau_axis P)
      P'
      hCanonical
      hRestricted

  simpa
    [hilbert4D_normalSectionTauLineReflect, P']
    using hEq

end Geometry

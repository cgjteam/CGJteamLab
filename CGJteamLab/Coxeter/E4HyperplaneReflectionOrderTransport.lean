import CGJteamLab.Coxeter.E4HyperplaneReflectionHyperplaneTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 reflection: planar slice and order transport

A plane containing one normal to the reflecting hyperplane is invariant
under the reflection.  This file packages the corresponding planar
reflection data once and uses it to transport strict betweenness.

The package is deliberately more general than the earlier normal-section
construction: the plane need not be the common normal section of two
hyperplanes.  It may be any ambient 2-plane containing a normal to the
single mirror Sigma.

This gives a reusable bridge

    corrected E4 hyperplane reflection on pi
      =
    ordinary line reflection in PlaneGeo Geo pi.

The first applications are:

* preservation of strict betweenness;
* preservation of midpoint configurations.
-/

/--
Planar reflection data associated with an invariant plane containing a
normal to Sigma.
-/
structure Hilbert4DReflectionPlanarSliceData
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (F : Geo.Point)
    (l : Geo.Line)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F) where

  s : Geo.Line

  s_in_pi :
    HilbertLineInPlane Geo s pi

  trace_exact :
    forall X : Geo.Point,
      (Q.toHilbertSpacePrimitive.OnPlane X pi /\
       Q.OnHyperplane X Sigma) <->
        H.OnLine X s

  plane_congruence :
    HilbertCongruence (PlaneGeo Geo pi)

  axis :
    ReflectionAxis (PlaneGeo Geo pi)

  axis_carrier :
    axis.carrier =
      (Subtype.mk s s_in_pi : PlaneLine Geo pi)


/--
Construct the planar slice package.
-/
noncomputable def hilbert4D_reflectionPlanarSliceData
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (F : Geo.Point)
    (l : Geo.Line)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F) :
    Hilbert4DReflectionPlanarSliceData
      Geo Sigma pi F l hlpi hNormal := by

  have hMarkedExists :=
    D.three_noncollinear_on_plane pi

  let U : Geo.Point :=
    Classical.choose hMarkedExists

  have hVExists :=
    Classical.choose_spec hMarkedExists

  let V : Geo.Point :=
    Classical.choose hVExists

  have hWExists :=
    Classical.choose_spec hVExists

  let W : Geo.Point :=
    Classical.choose hWExists

  have hMarkedData :=
    Classical.choose_spec hWExists

  have hUpi :
      Q.toHilbertSpacePrimitive.OnPlane U pi :=
    hMarkedData.1

  have hVpi :
      Q.toHilbertSpacePrimitive.OnPlane V pi :=
    hMarkedData.2.1

  have hWpi :
      Q.toHilbertSpacePrimitive.OnPlane W pi :=
    hMarkedData.2.2.1

  have hUVW :
      Not (PrimCollinear Geo U V W) :=
    hMarkedData.2.2.2

  let planeCong :
      HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi
      U V W
      hUpi hVpi hWpi
      hUVW

  have hTraceExists :=
    hilbert4D_normal_plane_intersection_line
      (Geo := Geo)
      hNormal pi hlpi

  let s : Geo.Line :=
    Classical.choose hTraceExists

  have hTraceData :=
    Classical.choose_spec hTraceExists

  have hspi :
      HilbertLineInPlane Geo s pi :=
    hTraceData.2.1

  have hTrace :
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X pi /\
         Q.OnHyperplane X Sigma) <->
          H.OnLine X s :=
    hTraceData.2.2.2

  have hSTExists :=
    D.two_points_on_each_line s

  let S0 : Geo.Point :=
    Classical.choose hSTExists

  have hTExists :=
    Classical.choose_spec hSTExists

  let T0 : Geo.Point :=
    Classical.choose hTExists

  have hSTData :=
    Classical.choose_spec hTExists

  have hST :
      Ne S0 T0 :=
    hSTData.1

  have hS0s :
      H.OnLine S0 s :=
    hSTData.2.1

  have hT0s :
      H.OnLine T0 s :=
    hSTData.2.2

  have hS0pi :
      Q.toHilbertSpacePrimitive.OnPlane S0 pi :=
    hspi S0 hS0s

  have hT0pi :
      Q.toHilbertSpacePrimitive.OnPlane T0 pi :=
    hspi T0 hT0s

  let Sp : PlanePoint Geo pi :=
    Subtype.mk S0 hS0pi

  let Tp : PlanePoint Geo pi :=
    Subtype.mk T0 hT0pi

  have hSTp :
      Ne Sp Tp := by

    intro hEq
    apply hST

    exact
      congrArg Subtype.val hEq

  let sp : PlaneLine Geo pi :=
    Subtype.mk s hspi

  let axis :
      ReflectionAxis (PlaneGeo Geo pi) :=
    {
      carrier := sp
      A := Sp
      B := Tp
      hAB := hSTp
      hA := hS0s
      hB := hT0s
    }

  exact
    {
      s := s
      s_in_pi := hspi
      trace_exact := hTrace
      plane_congruence := planeCong
      axis := axis
      axis_carrier := rfl
    }


/--
On an invariant plane containing a Sigma-normal, the corrected ambient
reflection is exactly the local line reflection from the packaged slice.
-/
theorem hilbert4D_reflectionPlanarSlice_lineReflect_eq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (F : Geo.Point)
    (l : Geo.Line)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (data :
      Hilbert4DReflectionPlanarSliceData
        Geo Sigma pi F l hlpi hNormal)
    (P : Geo.Point)
    (hPpi :
      Q.toHilbertSpacePrimitive.OnPlane P pi) :
    letI : HilbertCongruence (PlaneGeo Geo pi) :=
      data.plane_congruence
    lineReflect
        (PlaneGeo Geo pi)
        data.axis
        (Subtype.mk P hPpi) =
      (Subtype.mk
        (hyperplaneReflect4_corrected Geo Sigma P)
        (hyperplaneReflect4_preserves_plane_of_normal_smith
          (Geo := Geo)
          Sigma pi F l
          hlpi hNormal
          P hPpi) :
        PlanePoint Geo pi) := by

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    data.plane_congruence

  let Pp : PlanePoint Geo pi :=
    Subtype.mk P hPpi

  have hPPrimePi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma P)
        pi :=
    hyperplaneReflect4_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      P hPpi

  let Pp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma P)
      hPPrimePi

  have hRestricted :
      IsLineReflection
        (PlaneGeo Geo pi)
        data.axis
        Pp Pp' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := pi)
      Sigma F
      l data.s
      hlpi
      hNormal
      data.s_in_pi
      data.trace_exact
      data.axis
      data.axis_carrier
      Pp Pp'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P)

  have hCanonical :
      IsLineReflection
        (PlaneGeo Geo pi)
        data.axis
        Pp
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Pp) :=
    lineReflect_spec
      (PlaneGeo Geo pi)
      data.axis Pp

  exact
    line_reflection_unique
      (PlaneGeo Geo pi)
      data.axis
      Pp
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Pp)
      Pp'
      hCanonical
      hRestricted


/-!
## Strict betweenness
-/

/--
If a carrier line q contains one point P outside Sigma, then reflection
preserves betweenness of every ordered triple on q.
-/
theorem hyperplaneReflect4_corrected_preserves_between_of_off_point_on_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (q : Geo.Line)
    (A B C P : Geo.Point)
    (hABC : Geo.Between A B C)
    (hAq : H.OnLine A q)
    (hBq : H.OnLine B q)
    (hCq : H.OnLine C q)
    (hPq : H.OnLine P q)
    (hPoff :
      Not (Q.OnHyperplane P Sigma)) :
    Geo.Between
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C) := by

  have hFootExists :=
    hyperplaneReflect4_corrected_off_hyperplane_data
      (Geo := Geo)
      Sigma P hPoff

  let F : Geo.Point :=
    Classical.choose hFootExists

  have hFootData :=
    Classical.choose_spec hFootExists

  have hPerp :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P :=
    hFootData.1

  let l : Geo.Line :=
    Classical.choose hPerp

  have hLData :=
    Classical.choose_spec hPerp

  have hPl :
      H.OnLine P l :=
    hLData.1

  have hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F :=
    hLData.2

  have hPiExists :=
    hilbert_dimension_free_plane_through_intersecting_lines
      (Geo := Geo)
      q l P
      hPq hPl

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hPiExists

  have hPiData :=
    Classical.choose_spec hPiExists

  have hqpi :
      HilbertLineInPlane Geo q pi :=
    hPiData.1

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    hPiData.2

  have hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi :=
    hqpi A hAq

  have hBpi :
      Q.toHilbertSpacePrimitive.OnPlane B pi :=
    hqpi B hBq

  have hCpi :
      Q.toHilbertSpacePrimitive.OnPlane C pi :=
    hqpi C hCq

  let data :=
    hilbert4D_reflectionPlanarSliceData
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    data.plane_congruence

  let Ap : PlanePoint Geo pi :=
    Subtype.mk A hApi

  let Bp : PlanePoint Geo pi :=
    Subtype.mk B hBpi

  let Cp : PlanePoint Geo pi :=
    Subtype.mk C hCpi

  have hBetweenPlane :
      (PlaneGeo Geo pi).Between Ap Bp Cp :=
    (planeGeo_between
      (Geo := Geo)
      pi Ap Bp Cp).mpr
      hABC

  have hImagePlane :
      (PlaneGeo Geo pi).Between
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Ap)
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Bp)
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Cp) :=
    lineReflect_preserves_between
      (PlaneGeo Geo pi)
      data.axis
      Ap Bp Cp
      hBetweenPlane

  have hEqA :=
    hilbert4D_reflectionPlanarSlice_lineReflect_eq
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      data
      A hApi

  have hEqB :=
    hilbert4D_reflectionPlanarSlice_lineReflect_eq
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      data
      B hBpi

  have hEqC :=
    hilbert4D_reflectionPlanarSlice_lineReflect_eq
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      data
      C hCpi

  have hAmbient :
      Geo.Between
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Ap).1
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Bp).1
        (lineReflect
          (PlaneGeo Geo pi)
          data.axis Cp).1 :=
    (planeGeo_between
      (Geo := Geo)
      pi
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Ap)
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Bp)
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Cp)).mp
      hImagePlane

  have hEqAval :
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Ap).1 =
        hyperplaneReflect4_corrected Geo Sigma A :=
    congrArg Subtype.val hEqA

  have hEqBval :
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Bp).1 =
        hyperplaneReflect4_corrected Geo Sigma B :=
    congrArg Subtype.val hEqB

  have hEqCval :
      (lineReflect
        (PlaneGeo Geo pi)
        data.axis Cp).1 =
        hyperplaneReflect4_corrected Geo Sigma C :=
    congrArg Subtype.val hEqC

  rw [hEqAval, hEqBval, hEqCval] at hAmbient

  exact hAmbient


/--
Corrected E4 hyperplane reflection preserves strict betweenness globally.
-/
theorem hyperplaneReflect4_corrected_preserves_between
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    Geo.Between
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C) := by

  have hData :=
    H4O.between_incidence
      A B C hABC

  have hAB :
      Ne A B :=
    hData.1

  have hABCcol :
      PrimCollinear Geo A B C :=
    hData.2.2.2.1

  have hQExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      A B hAB

  let q : Geo.Line :=
    Classical.choose hQExists

  have hQData :=
    Classical.choose_spec hQExists

  have hAq :
      H.OnLine A q :=
    hQData.1

  have hBq :
      H.OnLine B q :=
    hQData.2

  have hCq :
      H.OnLine C q :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAB
      hAq hBq
      hABCcol

  by_cases hASigma :
      Q.OnHyperplane A Sigma

  case neg =>
    exact
      hyperplaneReflect4_corrected_preserves_between_of_off_point_on_line
        (Geo := Geo)
        Sigma q
        A B C A
        hABC
        hAq hBq hCq
        hAq
        hASigma

  case pos =>
    by_cases hBSigma :
        Q.OnHyperplane B Sigma

    case neg =>
      exact
        hyperplaneReflect4_corrected_preserves_between_of_off_point_on_line
          (Geo := Geo)
          Sigma q
          A B C B
          hABC
          hAq hBq hCq
          hBq
          hBSigma

    case pos =>
      have hqSigma :
          HilbertLineInHyperplane4 Geo q Sigma :=
        C4.line_in_hyperplane
          A B hAB
          q hAq hBq
          Sigma
          hASigma hBSigma

      have hCSigma :
          Q.OnHyperplane C Sigma :=
        hqSigma C hCq

      have hFixA :
          hyperplaneReflect4_corrected Geo Sigma A = A :=
        hyperplaneReflect4_corrected_of_on_hyperplane
          (Geo := Geo)
          Sigma A hASigma

      have hFixB :
          hyperplaneReflect4_corrected Geo Sigma B = B :=
        hyperplaneReflect4_corrected_of_on_hyperplane
          (Geo := Geo)
          Sigma B hBSigma

      have hFixC :
          hyperplaneReflect4_corrected Geo Sigma C = C :=
        hyperplaneReflect4_corrected_of_on_hyperplane
          (Geo := Geo)
          Sigma C hCSigma

      rw [hFixA, hFixB, hFixC]

      exact hABC


/-!
## Midpoints
-/

/--
Corrected E4 hyperplane reflection preserves midpoint configurations.
-/
theorem hyperplaneReflect4_corrected_preserves_midpoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (M A B : Geo.Point)
    (hMid :
      HilbertIsMidpoint Geo M A B) :
    HilbertIsMidpoint
      Geo
      (hyperplaneReflect4_corrected Geo Sigma M)
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B) := by

  have hBetween :
      Geo.Between
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma M)
        (hyperplaneReflect4_corrected Geo Sigma B) :=
    hyperplaneReflect4_corrected_preserves_between
      (Geo := Geo)
      Sigma
      A M B
      hMid.1

  have hAM :
      Geo.Congruent
        A M
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma M) :=
    hyperplaneReflect4_corrected_preserves_congruence
      (Geo := Geo)
      Sigma A M

  have hMB :
      Geo.Congruent
        M B
        (hyperplaneReflect4_corrected Geo Sigma M)
        (hyperplaneReflect4_corrected Geo Sigma B) :=
    hyperplaneReflect4_corrected_preserves_congruence
      (Geo := Geo)
      Sigma M B

  have hImageAM_AM :
      Geo.Congruent
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma M)
        A M :=
    hilbert4D_ambient_congruent_symm_corrected
      (Geo := Geo)
      A M
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma M)
      hAM

  have hImageAM_MB :
      Geo.Congruent
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma M)
        M B :=
    hilbert4D_ambient_congruent_transitive_corrected
      (Geo := Geo)
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma M)
      A M
      M B
      hImageAM_AM
      hMid.2

  have hCong :
      Geo.Congruent
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma M)
        (hyperplaneReflect4_corrected Geo Sigma M)
        (hyperplaneReflect4_corrected Geo Sigma B) :=
    hilbert4D_ambient_congruent_transitive_corrected
      (Geo := Geo)
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma M)
      M B
      (hyperplaneReflect4_corrected Geo Sigma M)
      (hyperplaneReflect4_corrected Geo Sigma B)
      hImageAM_MB
      hMB

  exact
    And.intro hBetween hCong

end Geometry

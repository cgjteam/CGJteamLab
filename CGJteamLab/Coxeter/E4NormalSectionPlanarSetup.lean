import CGJteamLab.Coxeter.E4NormalGeometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal sec: planar Coxeter setup

A packaged E4 normal sec already contains its plane N and exact
trace lines s,t. The planar Coxeter layer needs two additional pieces
of infrastructure only once:

* a complete HilbertCongruence instance on PlaneGeo Geo N;
* ReflectionAxis packages whose carriers are exactly the local copies
  of s and t.

This file constructs those data from the normal sec itself. No new
E4 geometry is used.
-/

structure Hilbert4DNormalSectionPlanarData
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
        Geo Sigma Tau Delta hMeet O hODelta) where

  S : Geo.Point
  T : Geo.Point

  S_ne_O : Ne S O
  T_ne_O : Ne T O

  S_on_s : H.OnLine S sec.s.1
  T_on_t : H.OnLine T sec.t.1

  S_on_N :
    Q.toHilbertSpacePrimitive.OnPlane S sec.N
  T_on_N :
    Q.toHilbertSpacePrimitive.OnPlane T sec.N

  O_S_T_noncollinear :
    Not (PrimCollinear Geo O S T)

  plane_congruence :
    HilbertCongruence (PlaneGeo Geo sec.N)

  sigma_axis :
    ReflectionAxis (PlaneGeo Geo sec.N)

  tau_axis :
    ReflectionAxis (PlaneGeo Geo sec.N)

  sigma_axis_carrier :
    sigma_axis.carrier =
      (Subtype.mk sec.s.1 sec.s_in_N :
        PlaneLine Geo sec.N)

  tau_axis_carrier :
    tau_axis.carrier =
      (Subtype.mk sec.t.1 sec.t_in_N :
        PlaneLine Geo sec.N)


noncomputable def hilbert4D_normalSectionPlanarData
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
        Geo Sigma Tau Delta hMeet O hODelta) :
    Hilbert4DNormalSectionPlanarData
      Geo Sigma Tau Delta hMeet O hODelta sec := by

  have hOs :
      H.OnLine O sec.s.1 :=
    (sec.sigma_trace_exact O).mp
      (And.intro
        sec.O_on_N
        (hMeet.2.1 O hODelta))

  have hOt :
      H.OnLine O sec.t.1 :=
    (sec.tau_trace_exact O).mp
      (And.intro
        sec.O_on_N
        (hMeet.2.2.1 O hODelta))

  have hSExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      sec.s.1 O

  let S : Geo.Point :=
    Classical.choose hSExists

  have hSData :=
    Classical.choose_spec hSExists

  have hSO :
      Ne S O :=
    hSData.1

  have hSs :
      H.OnLine S sec.s.1 :=
    hSData.2

  have hTExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      sec.t.1 O

  let T : Geo.Point :=
    Classical.choose hTExists

  have hTData :=
    Classical.choose_spec hTExists

  have hTO :
      Ne T O :=
    hTData.1

  have hTt :
      H.OnLine T sec.t.1 :=
    hTData.2

  have hSN :
      Q.toHilbertSpacePrimitive.OnPlane S sec.N :=
    sec.s_in_N S hSs

  have hTN :
      Q.toHilbertSpacePrimitive.OnPlane T sec.N :=
    sec.t_in_N T hTt

  have hOST :
      Not (PrimCollinear Geo O S T) := by

    intro hCol

    have hTs :
        H.OnLine T sec.s.1 :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hSO.symm
        hOs hSs
        hCol

    have hEq :
        sec.s.1 = sec.t.1 :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O T
        hTO.symm
        sec.s.1 sec.t.1
        hOs hTs
        hOt hTt

    exact
      sec.traces_distinct hEq

  let planeCong :
      HilbertCongruence (PlaneGeo Geo sec.N) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      sec.N
      O S T
      sec.O_on_N hSN hTN
      hOST

  let ON : PlanePoint Geo sec.N :=
    Subtype.mk O sec.O_on_N

  let SN : PlanePoint Geo sec.N :=
    Subtype.mk S hSN

  let TN : PlanePoint Geo sec.N :=
    Subtype.mk T hTN

  let sN : PlaneLine Geo sec.N :=
    Subtype.mk sec.s.1 sec.s_in_N

  let tN : PlaneLine Geo sec.N :=
    Subtype.mk sec.t.1 sec.t_in_N

  have hONsN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sec.N)
        ON sN :=
    hOs

  have hSNsN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sec.N)
        SN sN :=
    hSs

  have hONtN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sec.N)
        ON tN :=
    hOt

  have hTNtN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo sec.N)
        TN tN :=
    hTt

  have hON_SN :
      Ne ON SN := by
    intro hEq
    have hVal : O = S :=
      congrArg Subtype.val hEq
    exact
      hSO hVal.symm

  have hON_TN :
      Ne ON TN := by
    intro hEq
    have hVal : O = T :=
      congrArg Subtype.val hEq
    exact
      hTO hVal.symm

  let sigmaAxis :
      ReflectionAxis (PlaneGeo Geo sec.N) :=
    {
      carrier := sN
      A := ON
      B := SN
      hAB := hON_SN
      hA := hONsN
      hB := hSNsN
    }

  let tauAxis :
      ReflectionAxis (PlaneGeo Geo sec.N) :=
    {
      carrier := tN
      A := ON
      B := TN
      hAB := hON_TN
      hA := hONtN
      hB := hTNtN
    }

  exact
    {
      S := S
      T := T
      S_ne_O := hSO
      T_ne_O := hTO
      S_on_s := hSs
      T_on_t := hTt
      S_on_N := hSN
      T_on_N := hTN
      O_S_T_noncollinear := hOST
      plane_congruence := planeCong
      sigma_axis := sigmaAxis
      tau_axis := tauAxis
      sigma_axis_carrier := rfl
      tau_axis_carrier := rfl
    }

end Geometry

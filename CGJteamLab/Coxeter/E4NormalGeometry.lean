import CGJteamLab.Coxeter.E4NormalSection
import CGJteamLab.Coxeter.E4ReflectionPlaneInvariance
import CGJteamLab.Coxeter.E4HyperplanePerpendicularFrame
import CGJteamLab.Coxeter.E4NormalSectionNormal

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal geometry: production-facing normal-section API

This file is the consolidation checkpoint for the corrected E4 normal
geometry developed in tests52-81.

Downstream Coxeter code should use this API instead of unpacking the
individual construction tests.

The incidence base is now the production dimension-free Smith/Wyler
layer:

  `HilbertDimensionFreeIncidence`

together with the genuinely E4-specific hyperplane core:

  `Hilbert4DHyperplaneIncidenceCore`.

The compatibility instance from refactor01 reconstructs the old
`Hilbert4DAmbientIncidence` expected by the already validated internal
proofs.

One `Hilbert4DNormalSectionData` object contains:

* the two exact trace lines s,t;
* the normal-section plane N;
* exact intersection formulas N cap Sigma = s and N cap Tau = t;
* a Sigma-normal in N and a Tau-normal in N;
* perpendicularity of those normals to their trace lines;
* invariance of N under both corrected hyperplane reflections.

Thus the next Coxeter layer no longer needs to know how these facts were
constructed.
-/

/--
Packaged corrected E4 normal section for a fixed exact intersection
plane Delta and base point O.
-/
structure Hilbert4DNormalSectionData
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
      Q.toHilbertSpacePrimitive.OnPlane O Delta) where

  s : HyperplaneLine4 Geo Sigma
  t : HyperplaneLine4 Geo Tau
  N : Q.toHilbertSpacePrimitive.Plane

  s_perpendicular_delta :
    HilbertLinePerpendicularPlaneAt
      (HyperplaneGeo4 Geo Sigma)
      s
      (Subtype.mk Delta hMeet.2.1)
      (Subtype.mk O (hMeet.2.1 O hODelta))

  t_perpendicular_delta :
    HilbertLinePerpendicularPlaneAt
      (HyperplaneGeo4 Geo Tau)
      t
      (Subtype.mk Delta hMeet.2.2.1)
      (Subtype.mk O (hMeet.2.2.1 O hODelta))

  traces_distinct :
    Ne s.1 t.1

  O_on_N :
    Q.toHilbertSpacePrimitive.OnPlane O N

  s_in_N :
    HilbertLineInPlane Geo s.1 N

  t_in_N :
    HilbertLineInPlane Geo t.1 N

  N_not_in_Sigma :
    Not (HilbertPlaneInHyperplane4 Geo N Sigma)

  N_not_in_Tau :
    Not (HilbertPlaneInHyperplane4 Geo N Tau)

  sigma_trace_exact :
    forall X : Geo.Point,
      (Q.toHilbertSpacePrimitive.OnPlane X N /\
       Q.OnHyperplane X Sigma) <->
        H.OnLine X s.1

  tau_trace_exact :
    forall X : Geo.Point,
      (Q.toHilbertSpacePrimitive.OnPlane X N /\
       Q.OnHyperplane X Tau) <->
        H.OnLine X t.1

  sigma_normal : Geo.Line

  sigma_normal_in_N :
    HilbertLineInPlane Geo sigma_normal N

  O_on_sigma_normal :
    H.OnLine O sigma_normal

  sigma_normal_perpendicular_trace :
    HilbertLinesPerpendicularAt
      Geo sigma_normal s.1 O

  sigma_normal_at_O :
    HilbertLinePerpendicularHyperplaneAt4_corrected
      Geo sigma_normal Sigma O

  tau_normal : Geo.Line

  tau_normal_in_N :
    HilbertLineInPlane Geo tau_normal N

  O_on_tau_normal :
    H.OnLine O tau_normal

  tau_normal_perpendicular_trace :
    HilbertLinesPerpendicularAt
      Geo tau_normal t.1 O

  tau_normal_at_O :
    HilbertLinePerpendicularHyperplaneAt4_corrected
      Geo tau_normal Tau O

  sigma_reflection_invariant :
    forall P : Geo.Point,
      Q.toHilbertSpacePrimitive.OnPlane P N ->
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma P)
        N

  tau_reflection_invariant :
    forall P : Geo.Point,
      Q.toHilbertSpacePrimitive.OnPlane P N ->
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Tau P)
        N


/--
Symmetry of exact hyperplane intersection data.
-/
theorem hyperplanesMeetInPlane4_corrected_symm
    [HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta) :
    HyperplanesMeetInPlane4_corrected
      Geo Tau Sigma Delta := by

  refine And.intro hMeet.1.symm ?_
  refine And.intro hMeet.2.2.1 ?_
  refine And.intro hMeet.2.1 ?_

  intro X

  constructor

  case mp =>
    intro hBoth

    exact
      (hMeet.2.2.2 X).mp
        (And.intro hBoth.2 hBoth.1)

  case mpr =>
    intro hDelta

    have hBoth :=
      (hMeet.2.2.2 X).mpr hDelta

    exact
      And.intro hBoth.2 hBoth.1


/--
Construct the complete packaged normal section.

This theorem consumes the validated internal construction chain once.
Both reflection invariance statements are produced here, so downstream
Coxeter proofs do not need separate Sigma/Tau test files.
-/
noncomputable def hilbert4D_normalSectionData_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta) :
    Hilbert4DNormalSectionData
      Geo Sigma Tau Delta hMeet O hODelta := by

  have hSectionExists :=
    hilbert4D_hyperplane_pair_normal_section_exact_traces_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta

  let s : HyperplaneLine4 Geo Sigma :=
    Classical.choose hSectionExists

  have hTExists :=
    Classical.choose_spec hSectionExists

  let t : HyperplaneLine4 Geo Tau :=
    Classical.choose hTExists

  have hNExists :=
    Classical.choose_spec hTExists

  let N : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hNExists

  have hSectionData :=
    Classical.choose_spec hNExists

  have hSPerp :=
    hSectionData.1

  have hTPerp :=
    hSectionData.2.1

  have hst :=
    hSectionData.2.2.1

  have hON :=
    hSectionData.2.2.2.1

  have hsN :=
    hSectionData.2.2.2.2.1

  have htN :=
    hSectionData.2.2.2.2.2.1

  have hNnotSigma :=
    hSectionData.2.2.2.2.2.2.1

  have hNnotTau :=
    hSectionData.2.2.2.2.2.2.2.1

  have hTraceSigma :=
    hSectionData.2.2.2.2.2.2.2.2.1

  have hTraceTau :=
    hSectionData.2.2.2.2.2.2.2.2.2

  ----------------------------------------------------------------------
  -- Sigma-normal inside N.
  ----------------------------------------------------------------------

  have hSigmaNormalExists :=
    hilbert4D_normal_to_hyperplane_inside_normal_section_corrected
      (Geo := Geo)
      Sigma Tau
      Delta N
      hMeet
      O hODelta
      s t
      hSPerp hTPerp
      hst
      hON
      hsN htN

  let rSigma : Geo.Line :=
    Classical.choose hSigmaNormalExists

  have hSigmaNormalData :=
    Classical.choose_spec hSigmaNormalExists

  have hrSigmaN :=
    hSigmaNormalData.1

  have hOrSigma :=
    hSigmaNormalData.2.1

  have hSigmaPerpTrace :=
    hSigmaNormalData.2.2.1

  have hSigmaNormal :=
    hSigmaNormalData.2.2.2

  ----------------------------------------------------------------------
  -- Tau-normal inside the same N, by exact symmetry.
  ----------------------------------------------------------------------

  have hMeetSymm :
      HyperplanesMeetInPlane4_corrected
        Geo Tau Sigma Delta :=
    hyperplanesMeetInPlane4_corrected_symm
      (Geo := Geo)
      Sigma Tau Delta
      hMeet

  have hTauNormalExists :=
    hilbert4D_normal_to_hyperplane_inside_normal_section_corrected
      (Geo := Geo)
      Tau Sigma
      Delta N
      hMeetSymm
      O hODelta
      t s
      hTPerp hSPerp
      hst.symm
      hON
      htN hsN

  let rTau : Geo.Line :=
    Classical.choose hTauNormalExists

  have hTauNormalData :=
    Classical.choose_spec hTauNormalExists

  have hrTauN :=
    hTauNormalData.1

  have hOrTau :=
    hTauNormalData.2.1

  have hTauPerpTrace :=
    hTauNormalData.2.2.1

  have hTauNormal :=
    hTauNormalData.2.2.2

  ----------------------------------------------------------------------
  -- Both reflections preserve N.
  ----------------------------------------------------------------------

  have hSigmaInvariant :
      forall P : Geo.Point,
        Q.toHilbertSpacePrimitive.OnPlane P N ->
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma P)
          N := by

    intro P hPN

    exact
      hyperplaneReflect4_preserves_plane_of_normal_smith
        (Geo := Geo)
        Sigma N O rSigma
        hrSigmaN
        hSigmaNormal
        P hPN

  have hTauInvariant :
      forall P : Geo.Point,
        Q.toHilbertSpacePrimitive.OnPlane P N ->
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Tau P)
          N := by

    intro P hPN

    exact
      hyperplaneReflect4_preserves_plane_of_normal_smith
        (Geo := Geo)
        Tau N O rTau
        hrTauN
        hTauNormal
        P hPN

  exact
    {
      s := s
      t := t
      N := N
      s_perpendicular_delta := hSPerp
      t_perpendicular_delta := hTPerp
      traces_distinct := hst
      O_on_N := hON
      s_in_N := hsN
      t_in_N := htN
      N_not_in_Sigma := hNnotSigma
      N_not_in_Tau := hNnotTau
      sigma_trace_exact := hTraceSigma
      tau_trace_exact := hTraceTau
      sigma_normal := rSigma
      sigma_normal_in_N := hrSigmaN
      O_on_sigma_normal := hOrSigma
      sigma_normal_perpendicular_trace := hSigmaPerpTrace
      sigma_normal_at_O := hSigmaNormal
      tau_normal := rTau
      tau_normal_in_N := hrTauN
      O_on_tau_normal := hOrTau
      tau_normal_perpendicular_trace := hTauPerpTrace
      tau_normal_at_O := hTauNormal
      sigma_reflection_invariant := hSigmaInvariant
      tau_reflection_invariant := hTauInvariant
    }

end Geometry

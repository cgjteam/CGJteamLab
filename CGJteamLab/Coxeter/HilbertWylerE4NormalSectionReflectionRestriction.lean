import CGJteamLab.Coxeter.HilbertWylerE4NormalSectionData
import CGJteamLab.Coxeter.HilbertWylerE4NormalParallel
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.E4NormalSectionReflectionRestriction

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Restricting E4 hyperplane reflections to a normal section

This is the Hilbert-Wyler-facing bridge from ambient E4 reflection
geometry to the ordinary planar line-reflection theory used in the
Coxeter argument.

The generic restriction theorem itself needs only ambient Groups II and
III once the relevant reflection data are supplied. Group IV enters the
packaged canonical reflection functions through the derived XI.11
normal-existence interface.
-/

/--
Hilbert-Wyler-facing name for the corrected ambient E4
hyperplane-reflection relation.
-/
def HilbertWylerE4IsHyperplaneReflection
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (P P' : Geo.Point) : Prop :=
  IsHyperplaneReflection4_corrected
    Geo Sigma P P'


/--
A normal carrier through a point of an ambient plane `N` is absorbed by
`N` once `N` already contains one normal to the same hyperplane.
-/
theorem hilbertWyler_e4_normal_carrier_absorbed_by_plane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (N : S.Plane)
    (O F P : Geo.Point)
    (r l : Geo.Line)
    (hrN : HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hPl : H.OnLine P l)
    (hPN : S.OnPlane P N) :
    HilbertLineInPlane Geo l N := by

  exact
    hilbert4D_normal_carrier_absorbed_by_plane_smith
      (Geo := Geo)
      Sigma N
      O F P
      r l
      hrN
      hRNormal
      hLNormal
      hPl
      hPN


/--
Generic restriction theorem: an ambient E4 hyperplane reflection becomes
an ordinary line reflection in a plane containing a hyperplane normal,
provided `s` is the exact trace of the hyperplane on that plane.
-/
theorem hilbertWyler_e4_hyperplaneReflection_restricts_to_lineReflection
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (N : S.Plane)
    [HilbertCongruence (PlaneGeo Geo N)]
    (O : Geo.Point)
    (r s : Geo.Line)
    (hrN : HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (hsN : HilbertLineInPlane Geo s N)
    (hTrace :
      forall X : Geo.Point,
        (S.OnPlane X N /\
         E4OnHyperplane Geo X Sigma) <->
          H.OnLine X s)
    (axis : ReflectionAxis (PlaneGeo Geo N))
    (hAxisCarrier :
      axis.carrier =
        (Subtype.mk s hsN : PlaneLine Geo N))
    (Pp Pp' : PlanePoint Geo N)
    (hRefl :
      HilbertWylerE4IsHyperplaneReflection
        Geo Sigma Pp.1 Pp'.1) :
    IsLineReflection
      (PlaneGeo Geo N)
      axis Pp Pp' := by

  unfold HilbertWylerE4IsHyperplaneReflection at hRefl

  exact
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := N)
      Sigma O
      r s
      hrN
      hRNormal
      hsN
      hTrace
      axis
      hAxisCarrier
      Pp Pp'
      hRefl


/--
The canonical planar Sigma reflection on the packaged normal section.
-/
noncomputable def hilbertWylerE4NormalSectionSigmaLineReflect
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      HilbertWylerE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      HilbertWylerE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    PlanePoint Geo sec.N :=
  hilbert4D_normalSectionSigmaLineReflect
    (Geo := Geo)
    Sigma Tau Delta hMeet O hODelta
    sec planar P


/--
The canonical planar Tau reflection on the packaged normal section.
-/
noncomputable def hilbertWylerE4NormalSectionTauLineReflect
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      HilbertWylerE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      HilbertWylerE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    PlanePoint Geo sec.N :=
  hilbert4D_normalSectionTauLineReflect
    (Geo := Geo)
    Sigma Tau Delta hMeet O hODelta
    sec planar P


/--
On the packaged normal section, the planar Sigma line reflection is
exactly the restriction of the Hilbert-Wyler ambient Sigma reflection.
-/
theorem hilbertWylerE4NormalSectionSigmaLineReflect_eq_hyperplaneReflect
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      HilbertWylerE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      HilbertWylerE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    hilbertWylerE4NormalSectionSigmaLineReflect
        (Geo := Geo)
        Sigma Tau Delta hMeet O hODelta
        sec planar P =
      (Subtype.mk
        (hilbertWylerE4HyperplaneReflect
          (Geo := Geo) Sigma P.1)
        (by
          unfold hilbertWylerE4HyperplaneReflect
          exact sec.sigma_reflection_invariant P.1 P.2) :
        PlanePoint Geo sec.N) := by

  unfold hilbertWylerE4NormalSectionSigmaLineReflect
  unfold hilbertWylerE4HyperplaneReflect

  exact
    hilbert4D_normalSectionSigmaLineReflect_eq_hyperplaneReflect
      (Geo := Geo)
      Sigma Tau Delta hMeet O hODelta
      sec planar P


/--
On the packaged normal section, the planar Tau line reflection is exactly
the restriction of the Hilbert-Wyler ambient Tau reflection.
-/
theorem hilbertWylerE4NormalSectionTauLineReflect_eq_hyperplaneReflect
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      HilbertWylerE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      HilbertWylerE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    hilbertWylerE4NormalSectionTauLineReflect
        (Geo := Geo)
        Sigma Tau Delta hMeet O hODelta
        sec planar P =
      (Subtype.mk
        (hilbertWylerE4HyperplaneReflect
          (Geo := Geo) Tau P.1)
        (by
          unfold hilbertWylerE4HyperplaneReflect
          exact sec.tau_reflection_invariant P.1 P.2) :
        PlanePoint Geo sec.N) := by

  unfold hilbertWylerE4NormalSectionTauLineReflect
  unfold hilbertWylerE4HyperplaneReflect

  exact
    hilbert4D_normalSectionTauLineReflect_eq_hyperplaneReflect
      (Geo := Geo)
      Sigma Tau Delta hMeet O hODelta
      sec planar P

end Geometry

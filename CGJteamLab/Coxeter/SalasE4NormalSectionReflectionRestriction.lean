import CGJteamLab.Coxeter.SalasE4NormalSectionData
import CGJteamLab.Coxeter.SalasE4NormalParallel
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.E4NormalSectionReflectionRestriction

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Restricting E4 hyperplane reflections to a normal section

This is the Salas-facing bridge from ambient E4 reflection geometry to
the ordinary planar line-reflection theory used in the Coxeter argument.

Public foundation:

    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

The generic restriction theorem itself needs only Groups II and III once
the relevant reflection data are supplied.  Group IV enters the packaged
canonical reflection functions through the derived XI.11 normal-existence
interface.
-/

@[instance_reducible]
local instance salasE4Primitive_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_reflectionRestriction
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo] :
    Hilbert4DNormalFromExternalPointExistence_corrected Geo :=
  hilbert4D_XI11_implies_normalFromExternalPointExistence_corrected
    (Geo := Geo)


/--
Salas-facing name for the corrected ambient E4 hyperplane-reflection
relation.
-/
def SalasE4IsHyperplaneReflection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
theorem salas_e4_normal_carrier_absorbed_by_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
theorem salas_e4_hyperplaneReflection_restricts_to_lineReflection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
      SalasE4IsHyperplaneReflection
        Geo Sigma Pp.1 Pp'.1) :
    IsLineReflection
      (PlaneGeo Geo N)
      axis Pp Pp' := by

  unfold SalasE4IsHyperplaneReflection at hRefl

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
noncomputable def salasE4NormalSectionSigmaLineReflect
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      SalasE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      SalasE4NormalSectionPlanarData
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
noncomputable def salasE4NormalSectionTauLineReflect
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      SalasE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      SalasE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    PlanePoint Geo sec.N :=
  hilbert4D_normalSectionTauLineReflect
    (Geo := Geo)
    Sigma Tau Delta hMeet O hODelta
    sec planar P


/--
On the packaged normal section, the planar Sigma line reflection is
exactly the restriction of the Salas-based ambient Sigma reflection.
-/
theorem salasE4NormalSectionSigmaLineReflect_eq_hyperplaneReflect
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      SalasE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      SalasE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    salasE4NormalSectionSigmaLineReflect
        (Geo := Geo)
        Sigma Tau Delta hMeet O hODelta
        sec planar P =
      (Subtype.mk
        (salasE4HyperplaneReflect
          (Geo := Geo) Sigma P.1)
        (by
          unfold salasE4HyperplaneReflect
          exact sec.sigma_reflection_invariant P.1 P.2) :
        PlanePoint Geo sec.N) := by

  unfold salasE4NormalSectionSigmaLineReflect
  unfold salasE4HyperplaneReflect

  exact
    hilbert4D_normalSectionSigmaLineReflect_eq_hyperplaneReflect
      (Geo := Geo)
      Sigma Tau Delta hMeet O hODelta
      sec planar P


/--
On the packaged normal section, the planar Tau line reflection is
exactly the restriction of the Salas-based ambient Tau reflection.
-/
theorem salasE4NormalSectionTauLineReflect_eq_hyperplaneReflect
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta)
    (sec :
      SalasE4NormalSectionData
        Geo Sigma Tau Delta hMeet O hODelta)
    (planar :
      SalasE4NormalSectionPlanarData
        Geo Sigma Tau Delta hMeet O hODelta sec)
    (P : PlanePoint Geo sec.N) :
    salasE4NormalSectionTauLineReflect
        (Geo := Geo)
        Sigma Tau Delta hMeet O hODelta
        sec planar P =
      (Subtype.mk
        (salasE4HyperplaneReflect
          (Geo := Geo) Tau P.1)
        (by
          unfold salasE4HyperplaneReflect
          exact sec.tau_reflection_invariant P.1 P.2) :
        PlanePoint Geo sec.N) := by

  unfold salasE4NormalSectionTauLineReflect
  unfold salasE4HyperplaneReflect

  exact
    hilbert4D_normalSectionTauLineReflect_eq_hyperplaneReflect
      (Geo := Geo)
      Sigma Tau Delta hMeet O hODelta
      sec planar P

end Geometry

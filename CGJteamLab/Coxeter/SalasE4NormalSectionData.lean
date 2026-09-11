import CGJteamLab.Coxeter.SalasE4NormalSection
import CGJteamLab.Coxeter.SalasE4HilbertLayers
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.E4HyperplaneXI11
import CGJteamLab.Coxeter.E4NormalGeometry
import CGJteamLab.Coxeter.E4NormalSectionPlanarSetup

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Packaged E4 normal-section data on the Salas foundation

This module provides Salas-facing names and constructors for the two
production data packages used by the planar Coxeter reduction:

* the complete normal-section package;
* the planar reflection-axis package inside that normal section.

Public assumptions:

    HilbertIncidence
    HilbertSpacePrimitive
    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

The historical E4 incidence classes, the perpendicular-frame criterion,
and normal-from-external-point existence are reconstructed locally as
derived compatibility instances.
-/

@[instance_reducible]
local instance salasE4Primitive_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4FrameCriterion_normalSectionData
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo] :
    Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo :=
  hilbert4D_hyperplanePerpendicularFrameCriterion_of_XI4
    (Geo := Geo)


local instance salasE4NormalExistence_normalSectionData
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
Salas-facing name for the complete packaged normal section.
-/
abbrev SalasE4NormalSectionData
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
    (hODelta : S.OnPlane O Delta) :=
  Hilbert4DNormalSectionData
    Geo Sigma Tau Delta hMeet O hODelta


/--
Construct the complete Salas-based normal-section package.
-/
noncomputable def salasE4NormalSectionData
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
    (hODelta : S.OnPlane O Delta) :
    SalasE4NormalSectionData
      Geo Sigma Tau Delta hMeet O hODelta := by

  unfold SalasE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_normalSectionData_exists
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta


/--
Salas-facing name for the planar Coxeter data attached to a packaged
normal section.
-/
abbrev SalasE4NormalSectionPlanarData
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
        Geo Sigma Tau Delta hMeet O hODelta) :=
  Hilbert4DNormalSectionPlanarData
    Geo Sigma Tau Delta hMeet O hODelta sec


/--
Construct the planar reflection-axis package on a Salas-based normal
section.
-/
noncomputable def salasE4NormalSectionPlanarData
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
        Geo Sigma Tau Delta hMeet O hODelta) :
    SalasE4NormalSectionPlanarData
      Geo Sigma Tau Delta hMeet O hODelta sec := by

  unfold SalasE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_normalSectionPlanarData
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta
      sec

end Geometry

import CGJteamLab.Coxeter.HilbertWylerE4NormalSection
import CGJteamLab.HilbertWylerE4HilbertLayers
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.E4HyperplaneXI11
import CGJteamLab.Coxeter.E4NormalGeometry
import CGJteamLab.Coxeter.E4NormalSectionPlanarSetup

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Packaged E4 normal-section data on the Hilbert-Wyler foundation

This module provides Hilbert-Wyler-facing names and constructors for the
two production data packages used by the planar Coxeter reduction:

* the complete normal-section package;
* the planar reflection-axis package inside that normal section.

Public assumptions:

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension
    + Hilbert4DAmbientOrder
    + Hilbert4DAmbientCongruence
    + Hilbert4DAmbientEuclidean.

The historical corrected-E4 incidence interfaces and normal existence
are supplied by `HilbertWylerE4PublicInstances`. The perpendicular-frame
criterion remains a derived local instance from E4-XI.4.
-/

local instance hilbertWylerE4FrameCriterion_normalSectionData
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo] :
    Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo :=
  hilbert4D_hyperplanePerpendicularFrameCriterion_of_XI4
    (Geo := Geo)


/--
Hilbert-Wyler-facing name for the complete packaged normal section.
-/
abbrev HilbertWylerE4NormalSectionData
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
    (hODelta : S.OnPlane O Delta) :=
  Hilbert4DNormalSectionData
    Geo Sigma Tau Delta hMeet O hODelta


/--
Construct the complete Hilbert-Wyler-based normal-section package.
-/
noncomputable def hilbertWylerE4NormalSectionData
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
    (hODelta : S.OnPlane O Delta) :
    HilbertWylerE4NormalSectionData
      Geo Sigma Tau Delta hMeet O hODelta := by

  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_normalSectionData_exists
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta


/--
Hilbert-Wyler-facing name for the planar Coxeter data attached to a
packaged normal section.
-/
abbrev HilbertWylerE4NormalSectionPlanarData
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
        Geo Sigma Tau Delta hMeet O hODelta) :=
  Hilbert4DNormalSectionPlanarData
    Geo Sigma Tau Delta hMeet O hODelta sec


/--
Construct the planar reflection-axis package on a Hilbert-Wyler-based
normal section.
-/
noncomputable def hilbertWylerE4NormalSectionPlanarData
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
        Geo Sigma Tau Delta hMeet O hODelta) :
    HilbertWylerE4NormalSectionPlanarData
      Geo Sigma Tau Delta hMeet O hODelta sec := by

  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_normalSectionPlanarData
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta
      sec

end Geometry

-- Salas / dimension-four incidence foundation.
import CGJteamLab.SalasAxioms
import CGJteamLab.E4Dimension
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.SalasE4Local3D
import CGJteamLab.SalasE4Local3DCompatibility
import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4PlaneHyperplane
import CGJteamLab.SalasE4PublicInstances

-- Derived E4 XI.4 / XI.11 boundary.
import CGJteamLab.E4AmbientXI4
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.E4HyperplaneXI12
import CGJteamLab.E4HyperplaneXI11

-- Hilbert Groups II-IV restricted to derived E4 hyperplanes.
import CGJteamLab.Coxeter.SalasE4HilbertLayers

-- Ambient triangle metric facts.
import CGJteamLab.Coxeter.SalasE4AmbientTriangleSAS
import CGJteamLab.Coxeter.SalasE4AmbientTriangleSSS

-- Exact hyperplane incidence.
import CGJteamLab.Coxeter.SalasE4HyperplaneIntersection

-- Hyperplane reflection and transport.
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionEquiv
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionIncidence
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionLineTransport
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionPlaneTransport
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionHyperplaneTransport
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionOrderTransport
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionIsometry

-- Normal geometry.
import CGJteamLab.Coxeter.SalasE4NormalSection
import CGJteamLab.Coxeter.SalasE4NormalParallel
import CGJteamLab.Coxeter.SalasE4NormalUniqueness
import CGJteamLab.Coxeter.SalasE4NormalSectionData
import CGJteamLab.Coxeter.SalasE4NormalSectionReflectionRestriction
import CGJteamLab.Coxeter.SalasE4ReflectionPlaneInvariance

-- Coxeter A4 and generated S5.
import CGJteamLab.Coxeter.SalasE4CoxeterA4
import CGJteamLab.Coxeter.SalasE4CoxeterA4S5

/-!
# Salas E4 public geometry facade

Public aggregation layer for the corrected E4 / Coxeter route.

The intended foundation is

    SalasIncidence
    + E4Dimension
    + optionally Hilbert4DAmbientOrder
    + optionally Hilbert4DAmbientCongruence
    + optionally Hilbert4DAmbientEuclidean.

Historical corrected-E4 incidence classes remain available internally
through compatibility modules, but are not part of the intended public
foundation.

In particular, the implementation modules

    E4HyperplaneReflectionCarrierCandidate
    E4HyperplaneReflectionCarrierIndependence

are deliberately not imported directly here. Their results are consumed
by the public hyperplane-transport facade.
-/

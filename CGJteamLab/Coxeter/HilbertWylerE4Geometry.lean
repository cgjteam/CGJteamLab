-- Hilbert-Wyler / exact dimension-four incidence foundation.
import CGJteamLab.HilbertWylerAxioms
import CGJteamLab.HilbertWylerTheory
import CGJteamLab.E4Dimension
import CGJteamLab.HilbertWylerE4Compatibility
import CGJteamLab.HilbertWylerE4Local3D
import CGJteamLab.HilbertWylerE4Local3DCompatibility
import CGJteamLab.HilbertWylerE4PlaneHyperplane
import CGJteamLab.HilbertWylerE4PublicInstances

-- Derived E4 XI.4 / XI.11 boundary.
import CGJteamLab.E4AmbientXI4
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.E4HyperplaneXI12
import CGJteamLab.E4HyperplaneXI11

-- Hilbert Groups II-IV restricted to derived E4 hyperplanes.
import CGJteamLab.HilbertWylerE4HilbertLayers

-- Ambient triangle metric facts.
import CGJteamLab.Coxeter.HilbertWylerE4AmbientTriangleSAS
import CGJteamLab.Coxeter.HilbertWylerE4AmbientTriangleSSS

-- Exact hyperplane incidence.
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneIntersection

-- Hyperplane reflection and transport.
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionEquiv
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionIncidence
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionLineTransport
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionPlaneTransport
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionHyperplaneTransport
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionOrderTransport
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionIsometry

-- Normal geometry.
import CGJteamLab.Coxeter.HilbertWylerE4NormalSection
import CGJteamLab.Coxeter.HilbertWylerE4NormalParallel
import CGJteamLab.Coxeter.HilbertWylerE4NormalUniqueness
import CGJteamLab.Coxeter.HilbertWylerE4NormalSectionData
import CGJteamLab.Coxeter.HilbertWylerE4NormalSectionReflectionRestriction
import CGJteamLab.Coxeter.HilbertWylerE4ReflectionPlaneInvariance

-- Coxeter A4 and generated S5.
import CGJteamLab.Coxeter.HilbertWylerE4CoxeterA4
import CGJteamLab.Coxeter.HilbertWylerE4CoxeterA4S5

/-!
# Hilbert-Wyler E4 public geometry facade

Public aggregation layer for the corrected E4 / Coxeter route.

The incidence foundation is

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension.

Metric and Euclidean results add, when needed,

    Hilbert4DAmbientOrder
    + Hilbert4DAmbientCongruence
    + Hilbert4DAmbientEuclidean.

The architectural split is:

    HilbertWylerAxioms
            |
            v
    HilbertWylerTheory
            |
            +--> E4Dimension
            |
            v
    derived E4 hyperplanes
            |
            +--> local E3 Hilbert geometry
            +--> Euclid XI.4 / XI.11 / XI.12
            +--> hyperplane reflections
            +--> normal sections
            |
            v
    Coxeter A4
            |
            v
            S5.

The historical corrected-E4 classes remain implementation compatibility
interfaces. They are derived from the Hilbert-Wyler foundation and are
not intended as public axioms.

In particular, neither `SalasIncidence` nor any Salas-specific axiom is
part of this public route.

No theorem is proved in this file; it is only the public aggregation
boundary for the Hilbert-Wyler E4 development.
-/

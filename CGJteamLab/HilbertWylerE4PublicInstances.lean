import CGJteamLab.HilbertWylerE4Compatibility
import CGJteamLab.HilbertWylerE4Local3DCompatibility
import CGJteamLab.HilbertWylerE4PlaneHyperplane
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.E4HyperplaneXI11

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Public Hilbert-Wyler E4 compatibility instances

This module installs the historical corrected-E4 incidence interfaces as
low-priority derived instances on the public foundation

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension.

`HilbertPlaneIncidence` is part of the shared Hilbert point-line base; it
is not re-derived from the Hilbert-Wyler extension.

These instances add no axioms. They only expose consequences already
proved from the Hilbert-Wyler incidence extension and the dimension-four
assumption.

The low priority is intentional: if a client explicitly supplies one of
the historical E4 interfaces, that explicit instance remains preferred.

The final instance also exposes corrected normal existence as the derived
Euclid XI.11 consequence of the same E4 foundation plus Hilbert Groups
II-IV.
-/

/--
The only non-Prop compatibility class in this layer.
-/
@[instance_reducible]
instance (priority := 100) hilbertWylerE4Primitive_public
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DPrimitive Geo :=
  hilbertWylerE4Primitive (Geo := Geo)

/--
Dimension-free incidence compatibility derived from Hilbert-Wyler.
-/
instance (priority := 100) hilbertWylerE4DimensionFree_public
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  hilbertDimensionFreeIncidence_of_hilbertWyler
    (Geo := Geo)

/--
Historical E4 hyperplane-incidence core derived from Hilbert-Wyler plus
dimension four.
-/
instance (priority := 100) hilbertWylerE4HyperplaneCore_public
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  hilbertWyler_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)

/--
Historical ambient corrected-E4 incidence derived from the dimension-free
Hilbert-Wyler compatibility layer.
-/
instance (priority := 100) hilbertWylerE4AmbientIncidence_public
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)

/--
Historical local 3D incidence inside each E4 hyperplane.
-/
instance (priority := 100) hilbertWylerE4Local3D_public
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  hilbertWyler_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)

/--
Historical plane-hyperplane incidence derived from Hilbert-Wyler plus
dimension four.
-/
instance (priority := 100) hilbertWylerE4PlaneHyperplane_public
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  hilbertWyler_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)

/--
Corrected normal existence from an external point is not an extra E4
axiom. It is derived from XI.11 once Hilbert Groups II-IV are available.
-/
instance (priority := 100) hilbertWylerE4NormalExistence_public
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo] :
    Hilbert4DNormalFromExternalPointExistence_corrected Geo :=
  hilbert4D_XI11_implies_normalFromExternalPointExistence_corrected
    (Geo := Geo)

end Geometry

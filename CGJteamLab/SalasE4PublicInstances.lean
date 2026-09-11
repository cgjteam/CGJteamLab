import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.SalasE4Local3DCompatibility
import CGJteamLab.SalasE4PlaneHyperplane
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.E4HyperplaneXI11

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Public Salas E4 compatibility instances

This module installs the historical corrected-E4 incidence interfaces as
low-priority derived instances on the public foundation

    HilbertIncidence
    + HilbertSpacePrimitive
    + SalasIncidence
    + E4Dimension.

These instances add no axioms. They only expose consequences already
proved from Salas LP1-LP4 and the dimension-four assumption.

The low priority is intentional: if a client explicitly supplies one of
the historical E4 interfaces, that explicit instance remains preferred.

The final instance also exposes corrected normal existence as the derived
Euclid XI.11 consequence of the same Salas E4 foundation plus Hilbert
Groups II-IV.
-/

/--
The only non-Prop compatibility class in this layer.
-/
@[instance_reducible]
instance (priority := 100) salasE4Primitive_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)

/--
Ambient plane incidence derived from Salas + dimension four.
-/
instance (priority := 100) salasE4PlaneIncidence_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)

/--
Dimension-free incidence compatibility derived from Salas.
-/
instance (priority := 100) salasE4DimensionFree_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)

/--
Historical E4 hyperplane-incidence core derived from Salas + dimension four.
-/
instance (priority := 100) salasE4HyperplaneCore_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)

/--
Historical ambient corrected-E4 incidence derived from the
dimension-free Salas compatibility layer.
-/
instance (priority := 100) salasE4AmbientIncidence_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)

/--
Historical local 3D incidence inside each E4 hyperplane, derived from
Salas + dimension four.
-/
instance (priority := 100) salasE4Local3D_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)

/--
Historical plane-hyperplane incidence derived from Salas + dimension four.
-/
instance (priority := 100) salasE4PlaneHyperplane_public
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)

/--
Corrected normal existence from an external point is not an extra E4
axiom. On the public Salas E4 foundation it is derived from XI.11 once
Hilbert Groups II-IV are available.
-/
instance (priority := 100) salasE4NormalExistence_public
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

end Geometry

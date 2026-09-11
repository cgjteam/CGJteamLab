import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.SalasE4Local3DCompatibility
import CGJteamLab.SalasE4PlaneHyperplane
import CGJteamLab.E4HyperplaneXI11
import CGJteamLab.Coxeter.CoxeterA4Smith

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Salas E4 compatibility facade for Coxeter A4

This module connects the new E4 foundation

    SalasIncidence + E4Dimension

to the existing production theorem `coxeter_A4_global_relations_smith`.

No Coxeter theorem is reproved here.  The historical E4 interfaces needed
by `CoxeterA4Smith` are reconstructed locally as derived typeclass
instances.

The only genuinely additional geometric assumptions left at this level are

* Hilbert Group II:  `Hilbert4DAmbientOrder`;
* Hilbert Group III: `Hilbert4DAmbientCongruence`;
* Hilbert Group IV:  `Hilbert4DAmbientEuclidean`.

In particular, the following are derived rather than assumed:

* `HilbertPlaneIncidence`;
* `HilbertDimensionFreeIncidence`;
* `Hilbert4DHyperplaneIncidenceCore`;
* `Hilbert4DAmbientIncidence`;
* `Hilbert4DHyperplaneLocal3DIncidence`;
* `Hilbert4DPlaneHyperplaneIncidence`;
* `Hilbert4DNormalFromExternalPointExistence_corrected`.

The last item is supplied by the derived E4 analogue of Euclid XI.11.
-/

/-!
## 1. Derived historical incidence interfaces
-/

@[instance_reducible]
local instance salasE4Primitive_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


/--
The old ambient E4 incidence package is now only a compatibility view.
-/
local instance salasE4AmbientIncidence_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_coxeterA4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


/-!
## 2. Derived XI.11 boundary
-/

/--
The former XI.11-type existence class is reconstructed from Groups II-IV
and the already derived E4 incidence stack.
-/
local instance salasE4NormalExistence_coxeterA4
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


/-!
## 3. Coxeter A4 on the new foundation
-/

/--
The existing production Coxeter A4 theorem, exposed on the new foundation.

The simplex frame is the same production frame as in `CoxeterA4Smith`;
only its ambient historical E4 typeclasses are now supplied by the Salas
E4 compatibility facade above.
-/
theorem salas_e4_coxeter_A4_global_relations
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    CoxeterA4SmithSimplexFrame.CoxeterA4GlobalRelations
      (Geo := Geo) T :=
  CoxeterA4SmithSimplexFrame.coxeter_A4_global_relations_smith
    (Geo := Geo) T

end Geometry

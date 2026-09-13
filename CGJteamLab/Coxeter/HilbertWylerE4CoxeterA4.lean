import CGJteamLab.HilbertWylerE4PublicInstances
import CGJteamLab.Coxeter.CoxeterA4Smith

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler E4 facade for Coxeter A4

This module connects the E4 foundation

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension

to the production theorem `coxeter_A4_global_relations_smith`.

No Coxeter theorem is reproved here.

The only additional geometric assumptions are the ambient Hilbert
Groups II-IV:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean.

All historical E4 incidence interfaces and the XI.11 normal-existence
boundary are derived by `HilbertWylerE4PublicInstances`.
-/

/--
The production Coxeter A4 theorem exposed on the Hilbert-Wyler E4
foundation.
-/
theorem hilbertWyler_e4_coxeter_A4_global_relations
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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

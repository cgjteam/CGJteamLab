import CGJteamLab.Coxeter.SalasE4Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Salas E4 public API audit

Compile-time audit of the intended external API.

Only the public mathematical assumptions are declared below:

    HilbertIncidence
    HilbertSpacePrimitive
    SalasIncidence
    E4Dimension

plus Hilbert Groups II-IV when required.

No historical E4 incidence compatibility class is assumed explicitly,
and no local compatibility instance is installed in this file.
-/

/--
Normal-line uniqueness requires Salas + dimension four + Groups II-III.
-/
example
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : SpaceHyperplane4 Geo)
    (l m : Geo.Line)
    (F : Geo.Point)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma F) :
    l = m :=
  salas_e4_normal_same_foot_unique
    (Geo := Geo)
    Sigma l m F
    hLNormal hMNormal

/--
Perpendicular-foot uniqueness requires the same public foundation.
-/
example
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : SpaceHyperplane4 Geo)
    (P F G : Geo.Point)
    (hPerpF :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P)
    (hPerpG :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma G P) :
    F = G :=
  salas_e4_hyperplane_perpendicular_foot_unique
    (Geo := Geo)
    Sigma P F G
    hPerpF hPerpG

/--
The production Coxeter A4 relations require exactly the public Salas E4
foundation plus Hilbert Groups II-IV.
-/
example
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
  salas_e4_coxeter_A4_global_relations
    (Geo := Geo) T

end Geometry

import CGJteamLab.SalasToSmith
import CGJteamLab.HilbertDimensionFreeSmithExchange

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Steinitz exchange from Sancho de Salas incidence

This file is the endpoint of the bridge from the source-based
Sancho de Salas LP1-LP4 incidence axioms to the existing
dimension-free Smith/Wyler span calculus.

No new axiom is introduced here.

The proof chain is:

    Salas LP1-LP3
      -> SmithIncidenceCore

    Salas LP4
      -> WylerI7SecondCommonPoint
      -> SmithI5Statement

    SmithI5Statement
      -> SmithSpanExchange

Thus Mac Lane-Steinitz exchange remains a theorem in this development,
not an axiom of `SalasIncidence`.
-/

/--
Sancho de Salas LP1-LP4 imply the full Steinitz exchange law
for the existing `SmithSpan`.
-/
theorem salas_implies_smithSpanExchange
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo] :
    SmithSpanExchange Geo := by

  have hI5 :
      SmithI5Statement Geo :=
    salas_implies_smithI5
      (Geo := Geo)

  exact
    @smithI5_implies_smithSpanExchange
      Geo
      H
      (inferInstance : HilbertPlaneIncidence Geo)
      S
      (salas_to_smithIncidenceCore
        (Geo := Geo))
      hI5

end Geometry

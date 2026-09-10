import CGJteamLab.Hilbert3DSmithBridge
import CGJteamLab.HilbertDimension

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert E3 to Smith/Wyler exchange

This module records the end-to-end incidence-theoretic consequence

    Hilbert E3 incidence
      -> dimension-free Smith incidence
      -> Smith/Wyler generated-flat calculus
      -> Steinitz exchange for SmithSpan.

No new class, axiom, or global instance is introduced.

In particular, the theorem requires no spatial order, congruence,
Euclidean parallel, metric, orthogonality, reflection, or continuity
assumption.
-/

/--
Hilbert spatial incidence in E3 implies full Steinitz exchange for
`SmithSpan` through the production dimension-free Smith/Wyler chain.
-/
theorem hilbert3D_implies_smithSpanExchange
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo] :
    SmithSpanExchange Geo := by

  let D : HilbertDimensionFreeIncidence Geo :=
    hilbert3D_to_dimension_free_incidence
      (Geo := Geo)

  exact
    @dimensionFreeIncidence_implies_smithSpanExchange
      Geo
      H
      HP
      S
      D

end Geometry

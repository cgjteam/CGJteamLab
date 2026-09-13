import CGJteamLab.Coxeter.HilbertWylerE4CoxeterA4
import CGJteamLab.E4HyperplaneFrameCriterionDerived
import CGJteamLab.Coxeter.CoxeterA4S5

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler E4 facade for the Coxeter A4 -> S5 theorem

This module exposes the final production S5 identification on the
Hilbert-Wyler E4 foundation.

Geometric assumptions:

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension
    + Hilbert4DAmbientOrder
    + Hilbert4DAmbientCongruence
    + Hilbert4DAmbientEuclidean.

All historical E4 incidence interfaces and normal existence are derived.
The hyperplane perpendicular-frame criterion is also derived from E4-XI.4.

Thus no additional A4/S5-specific geometric axiom is introduced here.
-/

local instance hilbertWylerE4FrameCriterion_coxeterA4S5
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
The canonical action of the generated geometric A4 reflection group on
the five simplex vertices is injective.
-/
theorem hilbertWyler_e4_vertexActionHom_injective
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Function.Injective
      (CoxeterA4S5.vertexActionHom (Geo := Geo) T) :=
  CoxeterA4S5.vertexActionHom_injective
    (Geo := Geo) T


/--
The canonical action is surjective onto `Perm (Fin 5)`.
-/
theorem hilbertWyler_e4_vertexActionHom_surjective
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Function.Surjective
      (CoxeterA4S5.vertexActionHom (Geo := Geo) T) :=
  CoxeterA4S5.vertexActionHom_surjective
    (Geo := Geo) T


/--
The generated geometric A4 reflection group is explicitly equivalent,
as a multiplicative group, to S5.
-/
noncomputable def hilbertWyler_e4_generatedGroupMulEquivS5
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    MulEquiv
      (CoxeterA4S5.generatedGroup (Geo := Geo) T)
      (Equiv.Perm (Fin 5)) :=
  CoxeterA4S5.generatedGroupMulEquivS5
    (Geo := Geo) T


/--
Final group-theoretic statement on the Hilbert-Wyler E4 foundation:
the geometric Coxeter A4 reflection group is isomorphic to S5.
-/
theorem hilbertWyler_e4_generatedGroup_isomorphic_S5
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Nonempty
      (MulEquiv
        (CoxeterA4S5.generatedGroup (Geo := Geo) T)
        (Equiv.Perm (Fin 5))) :=
  Nonempty.intro
    (hilbertWyler_e4_generatedGroupMulEquivS5
      (Geo := Geo) T)


/--
The four geometric generators are sent to the four adjacent
transpositions under the Hilbert-Wyler-based S5 equivalence.
-/
theorem hilbertWyler_e4_generatedGroupMulEquivS5_r1
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    hilbertWyler_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR1
          (Geo := Geo) T) =
      CoxeterA4S5.sigma1 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r1
      (Geo := Geo) T


theorem hilbertWyler_e4_generatedGroupMulEquivS5_r2
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    hilbertWyler_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR2
          (Geo := Geo) T) =
      CoxeterA4S5.sigma2 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r2
      (Geo := Geo) T


theorem hilbertWyler_e4_generatedGroupMulEquivS5_r3
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    hilbertWyler_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR3
          (Geo := Geo) T) =
      CoxeterA4S5.sigma3 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r3
      (Geo := Geo) T


theorem hilbertWyler_e4_generatedGroupMulEquivS5_r4
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    hilbertWyler_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR4
          (Geo := Geo) T) =
      CoxeterA4S5.sigma4 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r4
      (Geo := Geo) T

end Geometry

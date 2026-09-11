import CGJteamLab.Coxeter.SalasE4CoxeterA4
import CGJteamLab.Coxeter.CoxeterA4S5

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Salas E4 facade for the Coxeter A4 -> S5 theorem

This module exposes the final production S5 identification on the new
E4 foundation.

Geometric assumptions:

    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

All historical E4 incidence interfaces, the hyperplane perpendicular-frame
criterion, and normal existence are reconstructed locally as theorems.

Thus no additional A4/S5-specific geometric axiom is introduced here.
-/

/-! ## Derived historical interfaces -/

@[instance_reducible]
local instance salasE4Primitive_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4FrameCriterion_coxeterA4S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo] :
    Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo :=
  hilbert4D_hyperplanePerpendicularFrameCriterion_of_XI4
    (Geo := Geo)


local instance salasE4NormalExistence_coxeterA4S5
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


/-! ## Final A4 -> S5 results on the Salas foundation -/

/--
The canonical action of the generated geometric A4 reflection group on
the five simplex vertices is injective.
-/
theorem salas_e4_vertexActionHom_injective
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
theorem salas_e4_vertexActionHom_surjective
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
noncomputable def salas_e4_generatedGroupMulEquivS5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    CoxeterA4S5.generatedGroup (Geo := Geo) T ≃*
      Equiv.Perm (Fin 5) :=
  CoxeterA4S5.generatedGroupMulEquivS5
    (Geo := Geo) T


/--
Final group-theoretic statement on the Salas E4 foundation:
the geometric Coxeter A4 reflection group is isomorphic to S5.
-/
theorem salas_e4_generatedGroup_isomorphic_S5
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Nonempty
      (CoxeterA4S5.generatedGroup (Geo := Geo) T ≃*
        Equiv.Perm (Fin 5)) :=
  ⟨salas_e4_generatedGroupMulEquivS5
      (Geo := Geo) T⟩


/--
The four geometric generators are sent to the four adjacent
transpositions under the Salas-based S5 equivalence.
-/
theorem salas_e4_generatedGroupMulEquivS5_r1
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    salas_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR1
          (Geo := Geo) T) =
      CoxeterA4S5.sigma1 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r1
      (Geo := Geo) T


theorem salas_e4_generatedGroupMulEquivS5_r2
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    salas_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR2
          (Geo := Geo) T) =
      CoxeterA4S5.sigma2 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r2
      (Geo := Geo) T


theorem salas_e4_generatedGroupMulEquivS5_r3
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    salas_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR3
          (Geo := Geo) T) =
      CoxeterA4S5.sigma3 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r3
      (Geo := Geo) T


theorem salas_e4_generatedGroupMulEquivS5_r4
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (T : CoxeterA4SmithSimplexFrame Geo) :
    salas_e4_generatedGroupMulEquivS5
        (Geo := Geo) T
        (CoxeterA4S5.generatedR4
          (Geo := Geo) T) =
      CoxeterA4S5.sigma4 := by
  exact
    CoxeterA4S5.generatedGroupMulEquivS5_r4
      (Geo := Geo) T

end Geometry

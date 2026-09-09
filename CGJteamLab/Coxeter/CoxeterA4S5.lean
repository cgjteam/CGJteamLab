import CGJteamLab.Coxeter.CoxeterA4Smith
import CGJteamLab.Coxeter.E4AmbientTriangleSSS
import CGJteamLab.Coxeter.E4HyperplaneReflectionIncidence
import CGJteamLab.Coxeter.E4MarkedPlaneMetric
import CGJteamLab.Coxeter.E4HyperplanePerpendicularFrame
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-!
# Coxeter A4 -> S5

Production consolidation of the synthetic E4 Coxeter A4 construction.

The four geometric hyperplane reflections associated with a Coxeter A4 Smith
simplex frame act on the five distinguished vertices as the adjacent
transpositions of `Fin 5`.  The generated geometric reflection group is proved
isomorphic to `Equiv.Perm (Fin 5)`.

The faithfulness argument uses the synthetic five-anchor rigidity theorem proved
below from the corrected E4 perpendicular-bisector hyperplane machinery.  No
`Hilbert4DFiveAnchorDistanceUniqueness` assumption is used.
-/


-- ============================================================
-- Consolidated layer from CoxeterA4S5_test01_fix4.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

/-!
# Coxeter A4 -> S5, test01

First algebraic layer for the final identification of the generated
geometric reflection group with S5.

The five abstract vertices are indexed by `Fin 5`.

  0 -> A
  1 -> B
  2 -> C
  3 -> D
  4 -> E

The four abstract generators are the adjacent transpositions

  sigma1 = (0 1)
  sigma2 = (1 2)
  sigma3 = (2 3)
  sigma4 = (3 4)

This file proves that the four geometric hyperplane reflections intertwine
with these four permutations on the five distinguished vertices.

No generated subgroup, faithfulness theorem, or S5 isomorphism is
introduced yet.
-/

/-! ## 1. Five abstract vertices -/

section Vertices

variable
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]

/-- The five geometric simplex vertices indexed by `Fin 5`. -/
def point
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Fin 5 -> Geo.Point :=
  Fin.cases T.A
    (Fin.cases T.B
      (Fin.cases T.C
        (Fin.cases T.D
          (fun _ => T.E))))

@[simp] theorem point_zero
    (T : CoxeterA4SmithSimplexFrame Geo) :
    point (Geo := Geo) T 0 = T.A := by
  rfl

@[simp] theorem point_one
    (T : CoxeterA4SmithSimplexFrame Geo) :
    point (Geo := Geo) T 1 = T.B := by
  rfl

@[simp] theorem point_two
    (T : CoxeterA4SmithSimplexFrame Geo) :
    point (Geo := Geo) T 2 = T.C := by
  rfl

@[simp] theorem point_three
    (T : CoxeterA4SmithSimplexFrame Geo) :
    point (Geo := Geo) T 3 = T.D := by
  rfl

@[simp] theorem point_four
    (T : CoxeterA4SmithSimplexFrame Geo) :
    point (Geo := Geo) T 4 = T.E := by
  rfl

end Vertices

/-! ## 2. Adjacent transpositions on `Fin 5` -/

/-- Abstract adjacent transposition corresponding to r1 = (A B). -/
def sigma1 : Equiv.Perm (Fin 5) :=
  Equiv.swap (0 : Fin 5) (1 : Fin 5)

/-- Abstract adjacent transposition corresponding to r2 = (B C). -/
def sigma2 : Equiv.Perm (Fin 5) :=
  Equiv.swap (1 : Fin 5) (2 : Fin 5)

/-- Abstract adjacent transposition corresponding to r3 = (C D). -/
def sigma3 : Equiv.Perm (Fin 5) :=
  Equiv.swap (2 : Fin 5) (3 : Fin 5)

/-- Abstract adjacent transposition corresponding to r4 = (D E). -/
def sigma4 : Equiv.Perm (Fin 5) :=
  Equiv.swap (3 : Fin 5) (4 : Fin 5)

@[simp] theorem sigma1_zero :
    sigma1 (0 : Fin 5) = 1 := by
  simp [sigma1]

@[simp] theorem sigma1_one :
    sigma1 (1 : Fin 5) = 0 := by
  simp [sigma1]

@[simp] theorem sigma1_two :
    sigma1 (2 : Fin 5) = 2 := by
  simp [sigma1, Equiv.swap_apply_def]

@[simp] theorem sigma1_three :
    sigma1 (3 : Fin 5) = 3 := by
  simp [sigma1, Equiv.swap_apply_def]

@[simp] theorem sigma1_four :
    sigma1 (4 : Fin 5) = 4 := by
  simp [sigma1, Equiv.swap_apply_def]

@[simp] theorem sigma2_zero :
    sigma2 (0 : Fin 5) = 0 := by
  simp [sigma2, Equiv.swap_apply_def]

@[simp] theorem sigma2_one :
    sigma2 (1 : Fin 5) = 2 := by
  simp [sigma2]

@[simp] theorem sigma2_two :
    sigma2 (2 : Fin 5) = 1 := by
  simp [sigma2]

@[simp] theorem sigma2_three :
    sigma2 (3 : Fin 5) = 3 := by
  simp [sigma2, Equiv.swap_apply_def]

@[simp] theorem sigma2_four :
    sigma2 (4 : Fin 5) = 4 := by
  simp [sigma2, Equiv.swap_apply_def]

@[simp] theorem sigma3_zero :
    sigma3 (0 : Fin 5) = 0 := by
  simp [sigma3, Equiv.swap_apply_def]

@[simp] theorem sigma3_one :
    sigma3 (1 : Fin 5) = 1 := by
  simp [sigma3, Equiv.swap_apply_def]

@[simp] theorem sigma3_two :
    sigma3 (2 : Fin 5) = 3 := by
  simp [sigma3]

@[simp] theorem sigma3_three :
    sigma3 (3 : Fin 5) = 2 := by
  simp [sigma3]

@[simp] theorem sigma3_four :
    sigma3 (4 : Fin 5) = 4 := by
  simp [sigma3, Equiv.swap_apply_def]

@[simp] theorem sigma4_zero :
    sigma4 (0 : Fin 5) = 0 := by
  simp [sigma4, Equiv.swap_apply_def]

@[simp] theorem sigma4_one :
    sigma4 (1 : Fin 5) = 1 := by
  simp [sigma4, Equiv.swap_apply_def]

@[simp] theorem sigma4_two :
    sigma4 (2 : Fin 5) = 2 := by
  simp [sigma4, Equiv.swap_apply_def]

@[simp] theorem sigma4_three :
    sigma4 (3 : Fin 5) = 4 := by
  simp [sigma4]

@[simp] theorem sigma4_four :
    sigma4 (4 : Fin 5) = 3 := by
  simp [sigma4]

/-! ## 3. Geometric action on the five vertices -/

section GeometricAction

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/--
The first geometric reflection acts on the five vertices as (0 1).
-/
theorem r1_point
    (T : CoxeterA4SmithSimplexFrame Geo)
    (v : Fin 5) :
    r1 (Geo := Geo) T (point (Geo := Geo) T v) =
      point (Geo := Geo) T (sigma1 v) := by
  fin_cases v
  next =>
    change r1 (Geo := Geo) T T.A =
      point (Geo := Geo) T (sigma1 (0 : Fin 5))
    rw [sigma1_zero, point_one]
    exact r1_A (Geo := Geo) T
  next =>
    change r1 (Geo := Geo) T T.B =
      point (Geo := Geo) T (sigma1 (1 : Fin 5))
    rw [sigma1_one, point_zero]
    exact r1_B (Geo := Geo) T
  next =>
    change r1 (Geo := Geo) T T.C =
      point (Geo := Geo) T (sigma1 (2 : Fin 5))
    rw [sigma1_two, point_two]
    exact r1_C (Geo := Geo) T
  next =>
    change r1 (Geo := Geo) T T.D =
      point (Geo := Geo) T (sigma1 (3 : Fin 5))
    rw [sigma1_three, point_three]
    exact r1_D (Geo := Geo) T
  next =>
    change r1 (Geo := Geo) T T.E =
      point (Geo := Geo) T (sigma1 (4 : Fin 5))
    rw [sigma1_four, point_four]
    exact r1_E (Geo := Geo) T

/--
The second geometric reflection acts on the five vertices as (1 2).
-/
theorem r2_point
    (T : CoxeterA4SmithSimplexFrame Geo)
    (v : Fin 5) :
    r2 (Geo := Geo) T (point (Geo := Geo) T v) =
      point (Geo := Geo) T (sigma2 v) := by
  fin_cases v
  next =>
    change r2 (Geo := Geo) T T.A =
      point (Geo := Geo) T (sigma2 (0 : Fin 5))
    rw [sigma2_zero, point_zero]
    exact r2_A (Geo := Geo) T
  next =>
    change r2 (Geo := Geo) T T.B =
      point (Geo := Geo) T (sigma2 (1 : Fin 5))
    rw [sigma2_one, point_two]
    exact r2_B (Geo := Geo) T
  next =>
    change r2 (Geo := Geo) T T.C =
      point (Geo := Geo) T (sigma2 (2 : Fin 5))
    rw [sigma2_two, point_one]
    exact r2_C (Geo := Geo) T
  next =>
    change r2 (Geo := Geo) T T.D =
      point (Geo := Geo) T (sigma2 (3 : Fin 5))
    rw [sigma2_three, point_three]
    exact r2_D (Geo := Geo) T
  next =>
    change r2 (Geo := Geo) T T.E =
      point (Geo := Geo) T (sigma2 (4 : Fin 5))
    rw [sigma2_four, point_four]
    exact r2_E (Geo := Geo) T

/--
The third geometric reflection acts on the five vertices as (2 3).
-/
theorem r3_point
    (T : CoxeterA4SmithSimplexFrame Geo)
    (v : Fin 5) :
    r3 (Geo := Geo) T (point (Geo := Geo) T v) =
      point (Geo := Geo) T (sigma3 v) := by
  fin_cases v
  next =>
    change r3 (Geo := Geo) T T.A =
      point (Geo := Geo) T (sigma3 (0 : Fin 5))
    rw [sigma3_zero, point_zero]
    exact r3_A (Geo := Geo) T
  next =>
    change r3 (Geo := Geo) T T.B =
      point (Geo := Geo) T (sigma3 (1 : Fin 5))
    rw [sigma3_one, point_one]
    exact r3_B (Geo := Geo) T
  next =>
    change r3 (Geo := Geo) T T.C =
      point (Geo := Geo) T (sigma3 (2 : Fin 5))
    rw [sigma3_two, point_three]
    exact r3_C (Geo := Geo) T
  next =>
    change r3 (Geo := Geo) T T.D =
      point (Geo := Geo) T (sigma3 (3 : Fin 5))
    rw [sigma3_three, point_two]
    exact r3_D (Geo := Geo) T
  next =>
    change r3 (Geo := Geo) T T.E =
      point (Geo := Geo) T (sigma3 (4 : Fin 5))
    rw [sigma3_four, point_four]
    exact r3_E (Geo := Geo) T

/--
The fourth geometric reflection acts on the five vertices as (3 4).
-/
theorem r4_point
    (T : CoxeterA4SmithSimplexFrame Geo)
    (v : Fin 5) :
    r4 (Geo := Geo) T (point (Geo := Geo) T v) =
      point (Geo := Geo) T (sigma4 v) := by
  fin_cases v
  next =>
    change r4 (Geo := Geo) T T.A =
      point (Geo := Geo) T (sigma4 (0 : Fin 5))
    rw [sigma4_zero, point_zero]
    exact r4_A (Geo := Geo) T
  next =>
    change r4 (Geo := Geo) T T.B =
      point (Geo := Geo) T (sigma4 (1 : Fin 5))
    rw [sigma4_one, point_one]
    exact r4_B (Geo := Geo) T
  next =>
    change r4 (Geo := Geo) T T.C =
      point (Geo := Geo) T (sigma4 (2 : Fin 5))
    rw [sigma4_two, point_two]
    exact r4_C (Geo := Geo) T
  next =>
    change r4 (Geo := Geo) T T.D =
      point (Geo := Geo) T (sigma4 (3 : Fin 5))
    rw [sigma4_three, point_four]
    exact r4_D (Geo := Geo) T
  next =>
    change r4 (Geo := Geo) T T.E =
      point (Geo := Geo) T (sigma4 (4 : Fin 5))
    rw [sigma4_four, point_three]
    exact r4_E (Geo := Geo) T

end GeometricAction

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test02.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test02

Second algebraic layer.

We now form the subgroup of ambient point permutations generated by the
four geometric hyperplane reflections r1,r2,r3,r4.

No vertex-action homomorphism is introduced yet.
-/

/-- The four geometric A4 generators as ambient point permutations. -/
noncomputable def geometricGenerators
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Set (Equiv.Perm Geo.Point) :=
  {
    r1 (Geo := Geo) T,
    r2 (Geo := Geo) T,
    r3 (Geo := Geo) T,
    r4 (Geo := Geo) T
  }

/-- The geometric Coxeter A4 subgroup generated by r1,r2,r3,r4. -/
noncomputable def generatedGroup
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Subgroup (Equiv.Perm Geo.Point) :=
  Subgroup.closure
    (geometricGenerators (Geo := Geo) T)

/-- r1 as an element of the generated subgroup. -/
noncomputable def generatedR1
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  {
    val := r1 (Geo := Geo) T
    property := Subgroup.subset_closure (by
      simp [geometricGenerators])
  }

/-- r2 as an element of the generated subgroup. -/
noncomputable def generatedR2
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  {
    val := r2 (Geo := Geo) T
    property := Subgroup.subset_closure (by
      simp [geometricGenerators])
  }

/-- r3 as an element of the generated subgroup. -/
noncomputable def generatedR3
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  {
    val := r3 (Geo := Geo) T
    property := Subgroup.subset_closure (by
      simp [geometricGenerators])
  }

/-- r4 as an element of the generated subgroup. -/
noncomputable def generatedR4
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  {
    val := r4 (Geo := Geo) T
    property := Subgroup.subset_closure (by
      simp [geometricGenerators])
  }

@[simp] theorem generatedR1_val
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (generatedR1 (Geo := Geo) T : Equiv.Perm Geo.Point) =
      r1 (Geo := Geo) T := by
  rfl

@[simp] theorem generatedR2_val
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (generatedR2 (Geo := Geo) T : Equiv.Perm Geo.Point) =
      r2 (Geo := Geo) T := by
  rfl

@[simp] theorem generatedR3_val
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (generatedR3 (Geo := Geo) T : Equiv.Perm Geo.Point) =
      r3 (Geo := Geo) T := by
  rfl

@[simp] theorem generatedR4_val
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (generatedR4 (Geo := Geo) T : Equiv.Perm Geo.Point) =
      r4 (Geo := Geo) T := by
  rfl

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test03_fix3.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test03

Every element of the geometric subgroup generated by r1,r2,r3,r4
realizes some permutation of the five abstract vertices `Fin 5`.

This is only the existence layer. Uniqueness of the realized
permutation, the vertex-action homomorphism, faithfulness, and
surjectivity are postponed.
-/

/--
A geometric permutation realizes an abstract permutation of the five
simplex vertices when the two actions intertwine through `point`.
-/
def RealizesVertexPerm
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (sigma : Equiv.Perm (Fin 5)) :
    Prop :=
  forall v : Fin 5,
    g (point (Geo := Geo) T v) =
      point (Geo := Geo) T (sigma v)

/--
Every element of the subgroup generated by r1,r2,r3,r4 realizes some
permutation of the five abstract vertices.
-/
theorem generated_realizes_vertex_perm
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (hg :
      g ∈ generatedGroup (Geo := Geo) T) :
    exists sigma : Equiv.Perm (Fin 5),
      RealizesVertexPerm
        (Geo := Geo) T g sigma := by

  change
    g ∈
      Subgroup.closure
        (geometricGenerators
          (Geo := Geo) T) at hg

  induction hg using Subgroup.closure_induction with

  | mem x hx =>
      simp only
        [geometricGenerators,
         Set.mem_insert_iff,
         Set.mem_singleton_iff] at hx

      rcases hx with hx | hx | hx | hx

      · subst x
        exact
          ⟨sigma1,
           r1_point
             (Geo := Geo) T⟩

      · subst x
        exact
          ⟨sigma2,
           r2_point
             (Geo := Geo) T⟩

      · subst x
        exact
          ⟨sigma3,
           r3_point
             (Geo := Geo) T⟩

      · subst x
        exact
          ⟨sigma4,
           r4_point
             (Geo := Geo) T⟩

  | one =>
      refine Exists.intro 1 ?_
      intro v
      rfl

  | mul x y _hx _hy ihx ihy =>
      rcases ihx with ⟨sigma, hsigma⟩
      rcases ihy with ⟨tau, htau⟩

      refine ⟨sigma * tau, ?_⟩
      intro v

      simp only [Equiv.Perm.mul_apply]
      rw [htau v]
      rw [hsigma (tau v)]

  | inv x _hx ih =>
      rcases ih with ⟨sigma, hsigma⟩

      refine ⟨sigma⁻¹, ?_⟩
      intro v

      have h :
          x
            (point
              (Geo := Geo) T
              ((sigma⁻¹) v)) =
            point
              (Geo := Geo) T v := by
        simpa using
          hsigma ((sigma⁻¹) v)

      apply x.injective
      simpa using h.symm

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test04_fix1.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]

/-!
# Coxeter A4 -> S5, test04

The five distinguished simplex vertices are pairwise distinct.

The four adjacent inequalities come from midpoint betweenness:
AB, BC, CD, DE.

The remaining six inequalities come directly from the mirror incidence
data stored in `CoxeterA4SmithSimplexFrame`: one point is off a mirror
while the other is on it.
-/

/-- The five A4 simplex vertices are pairwise distinct. -/
theorem vertices_pairwise_ne
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Ne T.A T.B /\
    Ne T.A T.C /\
    Ne T.A T.D /\
    Ne T.A T.E /\
    Ne T.B T.C /\
    Ne T.B T.D /\
    Ne T.B T.E /\
    Ne T.C T.D /\
    Ne T.C T.E /\
    Ne T.D T.E := by

  have hAB : Ne T.A T.B :=
    (H4O.between_incidence
      T.A T.F1 T.B T.F1_mid_AB.1).2.2.1

  have hBC : Ne T.B T.C :=
    (H4O.between_incidence
      T.B T.F2 T.C T.F2_mid_BC.1).2.2.1

  have hCD : Ne T.C T.D :=
    (H4O.between_incidence
      T.C T.F3 T.D T.F3_mid_CD.1).2.2.1

  have hDE : Ne T.D T.E :=
    (H4O.between_incidence
      T.D T.F4 T.E T.F4_mid_DE.1).2.2.1

  have hAC : Ne T.A T.C := by
    intro hAC
    apply T.A_off_Sigma1
    rw [hAC]
    exact T.C_on_Sigma1

  have hAD : Ne T.A T.D := by
    intro hAD
    apply T.A_off_Sigma1
    rw [hAD]
    exact T.D_on_Sigma1

  have hAE : Ne T.A T.E := by
    intro hAE
    apply T.A_off_Sigma1
    rw [hAE]
    exact T.E_on_Sigma1

  have hBD : Ne T.B T.D := by
    intro hBD
    apply T.B_off_Sigma2
    rw [hBD]
    exact T.D_on_Sigma2

  have hBE : Ne T.B T.E := by
    intro hBE
    apply T.B_off_Sigma2
    rw [hBE]
    exact T.E_on_Sigma2

  have hCE : Ne T.C T.E := by
    intro hCE
    apply T.C_off_Sigma3
    rw [hCE]
    exact T.E_on_Sigma3

  exact
    ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE⟩

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test05.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]

/-!
# Coxeter A4 -> S5, test05

The geometric realization of the five abstract vertices `Fin 5`
is injective.

This uses only the ten pairwise inequalities proved in test04.
-/

/--
The geometric realization of the five abstract vertices is injective.
-/
theorem point_injective
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Function.Injective
      (point (Geo := Geo) T) := by

  rcases
      vertices_pairwise_ne
        (Geo := Geo) T with
    ⟨hAB, hAC, hAD, hAE,
     hBC, hBD, hBE,
     hCD, hCE,
     hDE⟩

  intro v w h

  fin_cases v <;> fin_cases w

  · rfl

  · have h' : T.A = T.B := by
      simpa using h
    exact (hAB h').elim

  · have h' : T.A = T.C := by
      simpa using h
    exact (hAC h').elim

  · have h' : T.A = T.D := by
      simpa using h
    exact (hAD h').elim

  · have h' : T.A = T.E := by
      simpa using h
    exact (hAE h').elim

  · have h' : T.A = T.B := by
      simpa using h.symm
    exact (hAB h').elim

  · rfl

  · have h' : T.B = T.C := by
      simpa using h
    exact (hBC h').elim

  · have h' : T.B = T.D := by
      simpa using h
    exact (hBD h').elim

  · have h' : T.B = T.E := by
      simpa using h
    exact (hBE h').elim

  · have h' : T.A = T.C := by
      simpa using h.symm
    exact (hAC h').elim

  · have h' : T.B = T.C := by
      simpa using h.symm
    exact (hBC h').elim

  · rfl

  · have h' : T.C = T.D := by
      simpa using h
    exact (hCD h').elim

  · have h' : T.C = T.E := by
      simpa using h
    exact (hCE h').elim

  · have h' : T.A = T.D := by
      simpa using h.symm
    exact (hAD h').elim

  · have h' : T.B = T.D := by
      simpa using h.symm
    exact (hBD h').elim

  · have h' : T.C = T.D := by
      simpa using h.symm
    exact (hCD h').elim

  · rfl

  · have h' : T.D = T.E := by
      simpa using h
    exact (hDE h').elim

  · have h' : T.A = T.E := by
      simpa using h.symm
    exact (hAE h').elim

  · have h' : T.B = T.E := by
      simpa using h.symm
    exact (hBE h').elim

  · have h' : T.C = T.E := by
      simpa using h.symm
    exact (hCE h').elim

  · have h' : T.D = T.E := by
      simpa using h.symm
    exact (hDE h').elim

  · rfl

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test06.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]

/-!
# Coxeter A4 -> S5, test06

Uniqueness of the abstract permutation realized by a geometric
permutation on the five distinguished vertices.
-/

/--
A geometric permutation can realize at most one permutation of the
five abstract vertices.
-/
theorem realized_vertex_perm_unique
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (sigma tau : Equiv.Perm (Fin 5))
    (hsigma :
      RealizesVertexPerm
        (Geo := Geo) T g sigma)
    (htau :
      RealizesVertexPerm
        (Geo := Geo) T g tau) :
    sigma = tau := by

  apply Equiv.ext
  intro v

  apply point_injective
    (Geo := Geo) T

  rw [← hsigma v]
  rw [← htau v]

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test07_fix2.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test07

Canonical permutation induced on the five abstract vertices by an
element of the generated geometric subgroup.
-/

/--
The canonical permutation of `Fin 5` induced by an element of the
geometric A4 subgroup.
-/
noncomputable def vertexPerm
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    Equiv.Perm (Fin 5) :=
  Classical.choose
    (generated_realizes_vertex_perm
      (Geo := Geo)
      T g.1 g.2)

/--
The canonical `vertexPerm` really is realized by the ambient
permutation underlying `g`.
-/
theorem vertexPerm_realizes
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    RealizesVertexPerm
      (Geo := Geo)
      T
      g.1
      (vertexPerm (Geo := Geo) T g) := by
  exact
    Classical.choose_spec
      (generated_realizes_vertex_perm
        (Geo := Geo)
        T g.1 g.2)

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test08.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test08

Multiplicativity and identity law for the canonical permutation induced
on the five abstract vertices.
-/

/-- The induced vertex permutation is multiplicative. -/
theorem vertexPerm_mul
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g h : generatedGroup (Geo := Geo) T) :
    vertexPerm (Geo := Geo) T (g * h) =
      vertexPerm (Geo := Geo) T g *
      vertexPerm (Geo := Geo) T h := by

  apply
    realized_vertex_perm_unique
      (Geo := Geo)
      T
      (g * h).1

  · exact
      vertexPerm_realizes
        (Geo := Geo)
        T (g * h)

  · intro v

    change
      g.1
          (h.1
            (point
              (Geo := Geo) T v)) =
        point
          (Geo := Geo) T
          (vertexPerm
              (Geo := Geo) T g
            (vertexPerm
              (Geo := Geo) T h v))

    rw [
      vertexPerm_realizes
        (Geo := Geo) T h v
    ]

    rw [
      vertexPerm_realizes
        (Geo := Geo) T g
          (vertexPerm
            (Geo := Geo) T h v)
    ]

/-- The identity element induces the identity permutation on Fin 5. -/
theorem vertexPerm_one
    (T : CoxeterA4SmithSimplexFrame Geo) :
    vertexPerm
        (Geo := Geo)
        T
        (1 : generatedGroup
          (Geo := Geo) T) =
      1 := by

  apply
    realized_vertex_perm_unique
      (Geo := Geo)
      T
      (1 : Equiv.Perm Geo.Point)

  · simpa using
      vertexPerm_realizes
        (Geo := Geo)
        T
        (1 : generatedGroup
          (Geo := Geo) T)

  · intro v
    rfl

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test09.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test09

Canonical action homomorphism of the generated geometric reflection
group on the five simplex vertices.
-/

/--
Canonical action homomorphism on the five distinguished vertices.
-/
noncomputable def vertexActionHom
    (T : CoxeterA4SmithSimplexFrame Geo) :
    MonoidHom
      (generatedGroup (Geo := Geo) T)
      (Equiv.Perm (Fin 5)) where
  toFun :=
    vertexPerm (Geo := Geo) T
  map_one' :=
    vertexPerm_one
      (Geo := Geo) T
  map_mul' :=
    vertexPerm_mul
      (Geo := Geo) T

@[simp] theorem vertexActionHom_apply
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    vertexActionHom (Geo := Geo) T g =
      vertexPerm (Geo := Geo) T g := by
  rfl

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test10.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test10

The four adjacent transpositions belong to the range of the canonical
vertex action.
-/

/-- The four abstract adjacent transpositions. -/
def abstractGenerators :
    Set (Equiv.Perm (Fin 5)) :=
  {sigma1, sigma2, sigma3, sigma4}

theorem sigma1_isSwap :
    Equiv.Perm.IsSwap sigma1 := by
  exact
    ⟨(0 : Fin 5),
     (1 : Fin 5),
     by decide,
     rfl⟩

theorem sigma2_isSwap :
    Equiv.Perm.IsSwap sigma2 := by
  exact
    ⟨(1 : Fin 5),
     (2 : Fin 5),
     by decide,
     rfl⟩

theorem sigma3_isSwap :
    Equiv.Perm.IsSwap sigma3 := by
  exact
    ⟨(2 : Fin 5),
     (3 : Fin 5),
     by decide,
     rfl⟩

theorem sigma4_isSwap :
    Equiv.Perm.IsSwap sigma4 := by
  exact
    ⟨(3 : Fin 5),
     (4 : Fin 5),
     by decide,
     rfl⟩

/-- Every abstract generator is a transposition. -/
theorem abstractGenerators_isSwap
    (sigma : Equiv.Perm (Fin 5))
    (hsigma :
      sigma ∈ abstractGenerators) :
    Equiv.Perm.IsSwap sigma := by

  simp only
    [abstractGenerators,
     Set.mem_insert_iff,
     Set.mem_singleton_iff] at hsigma

  rcases hsigma with h | h | h | h

  · subst sigma
    exact sigma1_isSwap

  · subst sigma
    exact sigma2_isSwap

  · subst sigma
    exact sigma3_isSwap

  · subst sigma
    exact sigma4_isSwap

/-- The induced action of generatedR1 is sigma1. -/
theorem vertexAction_generatedR1
    (T : CoxeterA4SmithSimplexFrame Geo) :
    vertexActionHom
        (Geo := Geo) T
        (generatedR1
          (Geo := Geo) T) =
      sigma1 := by

  change
    vertexPerm
        (Geo := Geo) T
        (generatedR1
          (Geo := Geo) T) =
      sigma1

  apply
    realized_vertex_perm_unique
      (Geo := Geo)
      T
      (r1 (Geo := Geo) T)

  · exact
      vertexPerm_realizes
        (Geo := Geo)
        T
        (generatedR1
          (Geo := Geo) T)

  · exact
      r1_point
        (Geo := Geo) T

/-- The induced action of generatedR2 is sigma2. -/
theorem vertexAction_generatedR2
    (T : CoxeterA4SmithSimplexFrame Geo) :
    vertexActionHom
        (Geo := Geo) T
        (generatedR2
          (Geo := Geo) T) =
      sigma2 := by

  change
    vertexPerm
        (Geo := Geo) T
        (generatedR2
          (Geo := Geo) T) =
      sigma2

  apply
    realized_vertex_perm_unique
      (Geo := Geo)
      T
      (r2 (Geo := Geo) T)

  · exact
      vertexPerm_realizes
        (Geo := Geo)
        T
        (generatedR2
          (Geo := Geo) T)

  · exact
      r2_point
        (Geo := Geo) T

/-- The induced action of generatedR3 is sigma3. -/
theorem vertexAction_generatedR3
    (T : CoxeterA4SmithSimplexFrame Geo) :
    vertexActionHom
        (Geo := Geo) T
        (generatedR3
          (Geo := Geo) T) =
      sigma3 := by

  change
    vertexPerm
        (Geo := Geo) T
        (generatedR3
          (Geo := Geo) T) =
      sigma3

  apply
    realized_vertex_perm_unique
      (Geo := Geo)
      T
      (r3 (Geo := Geo) T)

  · exact
      vertexPerm_realizes
        (Geo := Geo)
        T
        (generatedR3
          (Geo := Geo) T)

  · exact
      r3_point
        (Geo := Geo) T

/-- The induced action of generatedR4 is sigma4. -/
theorem vertexAction_generatedR4
    (T : CoxeterA4SmithSimplexFrame Geo) :
    vertexActionHom
        (Geo := Geo) T
        (generatedR4
          (Geo := Geo) T) =
      sigma4 := by

  change
    vertexPerm
        (Geo := Geo) T
        (generatedR4
          (Geo := Geo) T) =
      sigma4

  apply
    realized_vertex_perm_unique
      (Geo := Geo)
      T
      (r4 (Geo := Geo) T)

  · exact
      vertexPerm_realizes
        (Geo := Geo)
        T
        (generatedR4
          (Geo := Geo) T)

  · exact
      r4_point
        (Geo := Geo) T

/--
Every abstract adjacent-transposition generator lies in the range of
the geometric vertex-action homomorphism.
-/
theorem abstractGenerators_subset_vertexAction_range
    (T : CoxeterA4SmithSimplexFrame Geo) :
    abstractGenerators ⊆
      (vertexActionHom
        (Geo := Geo) T).range := by

  intro sigma hsigma

  simp only
    [abstractGenerators,
     Set.mem_insert_iff,
     Set.mem_singleton_iff] at hsigma

  rcases hsigma with h | h | h | h

  · subst sigma
    exact
      ⟨generatedR1
          (Geo := Geo) T,
       vertexAction_generatedR1
         (Geo := Geo) T⟩

  · subst sigma
    exact
      ⟨generatedR2
          (Geo := Geo) T,
       vertexAction_generatedR2
         (Geo := Geo) T⟩

  · subst sigma
    exact
      ⟨generatedR3
          (Geo := Geo) T,
       vertexAction_generatedR3
         (Geo := Geo) T⟩

  · subst sigma
    exact
      ⟨generatedR4
          (Geo := Geo) T,
       vertexAction_generatedR4
         (Geo := Geo) T⟩

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test11_fix1.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test11

The four adjacent transpositions generate the full symmetric group on
`Fin 5`. Therefore the canonical vertex-action homomorphism is
surjective.
-/

/--
The subgroup generated by sigma1,sigma2,sigma3,sigma4 acts
transitively on Fin 5.
-/
theorem abstractGenerators_closure_isPretransitive :
    let K :=
      Subgroup.closure abstractGenerators
    MulAction.IsPretransitive
      K (Fin 5) := by

  let K :
      Subgroup (Equiv.Perm (Fin 5)) :=
    Subgroup.closure abstractGenerators

  let k1 : K :=
    ⟨sigma1,
     Subgroup.subset_closure
       (by simp [abstractGenerators])⟩

  let k2 : K :=
    ⟨sigma2,
     Subgroup.subset_closure
       (by simp [abstractGenerators])⟩

  let k3 : K :=
    ⟨sigma3,
     Subgroup.subset_closure
       (by simp [abstractGenerators])⟩

  let k4 : K :=
    ⟨sigma4,
     Subgroup.subset_closure
       (by simp [abstractGenerators])⟩

  let reach : Fin 5 -> K :=
    fun v =>
      if v = 0 then
        1
      else if v = 1 then
        k1
      else if v = 2 then
        k2 * k1
      else if v = 3 then
        k3 * k2 * k1
      else
        k4 * k3 * k2 * k1

  have hreach :
      forall v : Fin 5,
        (reach v).1 (0 : Fin 5) = v := by
    intro v
    fin_cases v <;>
      simp
        [reach, k1, k2, k3, k4,
         sigma1, sigma2, sigma3, sigma4,
         Equiv.Perm.mul_apply]

  have hreach_smul :
      forall v : Fin 5,
        reach v • (0 : Fin 5) = v := by
    intro v
    change
      (reach v).1 (0 : Fin 5) = v
    exact hreach v

  exact
    {
      exists_smul_eq := by
        intro x y

        refine
          ⟨reach y * (reach x)⁻¹, ?_⟩

        calc
          (reach y * (reach x)⁻¹) • x =
              reach y • ((reach x)⁻¹ • x) := by
                rw [mul_smul]

          _ =
              reach y •
                ((reach x)⁻¹ •
                  (reach x • (0 : Fin 5))) := by
                rw [hreach_smul x]

          _ =
              reach y • (0 : Fin 5) := by
                rw [inv_smul_smul]

          _ = y :=
                hreach_smul y
    }

/--
The canonical vertex action is surjective onto the full symmetric
group on Fin 5.
-/
theorem vertexActionHom_surjective
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Function.Surjective
      (vertexActionHom (Geo := Geo) T) := by

  let hPre :
      MulAction.IsPretransitive
        (Subgroup.closure abstractGenerators)
        (Fin 5) :=
    abstractGenerators_closure_isPretransitive

  have hAll :=
    @closure_of_isSwap_of_isPretransitive
      (Fin 5)
      inferInstance
      inferInstance
      abstractGenerators
      abstractGenerators_isSwap
      hPre

  have hClosureLe :
      Subgroup.closure abstractGenerators ≤
        (vertexActionHom
          (Geo := Geo) T).range := by
    exact
      (Subgroup.closure_le
        (vertexActionHom
          (Geo := Geo) T).range).2
        (abstractGenerators_subset_vertexAction_range
          (Geo := Geo) T)

  intro sigma

  have hsigmaClosure :
      sigma ∈
        Subgroup.closure abstractGenerators := by
    rw [hAll]
    simp

  exact
    hClosureLe hsigmaClosure

end CoxeterA4S5

end Geometry

-- ============================================================
-- Consolidated layer from CoxeterA4S5_test12.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-!
# Coxeter A4 -> S5, test12

First faithfulness layer.

Every element of the geometric subgroup generated by the four corrected
E4 hyperplane reflections preserves ambient segment congruence.
-/

/--
Every element of the generated geometric subgroup preserves ambient
segment congruence.
-/
theorem generated_preserves_congruence
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (hg :
      g ∈ generatedGroup (Geo := Geo) T) :
    forall P Q : Geo.Point,
      Geo.Congruent
        P Q
        (g P)
        (g Q) := by

  change
    g ∈
      Subgroup.closure
        (geometricGenerators
          (Geo := Geo) T) at hg

  induction hg using Subgroup.closure_induction with

  | mem x hx =>
      simp only
        [geometricGenerators,
         Set.mem_insert_iff,
         Set.mem_singleton_iff] at hx

      rcases hx with hx | hx | hx | hx

      · subst x
        intro P Q
        simpa only [r1_apply] using
          hyperplaneReflect4_corrected_preserves_congruence
            (Geo := Geo)
            T.Sigma1 P Q

      · subst x
        intro P Q
        simpa only [r2_apply] using
          hyperplaneReflect4_corrected_preserves_congruence
            (Geo := Geo)
            T.Sigma2 P Q

      · subst x
        intro P Q
        simpa only [r3_apply] using
          hyperplaneReflect4_corrected_preserves_congruence
            (Geo := Geo)
            T.Sigma3 P Q

      · subst x
        intro P Q
        simpa only [r4_apply] using
          hyperplaneReflect4_corrected_preserves_congruence
            (Geo := Geo)
            T.Sigma4 P Q

  | one =>
      intro P Q
      simpa using
        hilbert4D_ambient_congruent_reflexive_corrected
          (Geo := Geo)
          P Q

  | mul x y _hx _hy ihx ihy =>
      intro P Q

      have h1 :
          Geo.Congruent
            P Q
            (y P)
            (y Q) :=
        ihy P Q

      have h2 :
          Geo.Congruent
            (y P)
            (y Q)
            (x (y P))
            (x (y Q)) :=
        ihx (y P) (y Q)

      have h3 :
          Geo.Congruent
            P Q
            (x (y P))
            (x (y Q)) :=
        hilbert4D_ambient_congruent_transitive_corrected
          (Geo := Geo)
          P Q
          (y P) (y Q)
          (x (y P)) (x (y Q))
          h1 h2

      simpa only [Equiv.Perm.mul_apply] using h3

  | inv x _hx ih =>
      intro P Q

      have hForward :
          Geo.Congruent
            (x⁻¹ P)
            (x⁻¹ Q)
            P Q := by
        have h :=
          ih (x⁻¹ P) (x⁻¹ Q)
        simpa using h

      exact
        hilbert4D_ambient_congruent_symm_corrected
          (Geo := Geo)
          (x⁻¹ P)
          (x⁻¹ Q)
          P Q
          hForward

end CoxeterA4S5

end Geometry


-- ============================================================
-- Fixed vertices from trivial vertex action
-- ============================================================

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-- If the induced action is trivial, every distinguished vertex is fixed. -/
theorem fixes_vertex_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct : vertexActionHom (Geo := Geo) T g = 1)
    (v : Fin 5) :
    g.1 (point (Geo := Geo) T v) =
      point (Geo := Geo) T v := by

  have hSpec :=
    vertexPerm_realizes
      (Geo := Geo) T g v

  have hVertex :
      vertexPerm (Geo := Geo) T g = 1 := by
    simpa [vertexActionHom_apply] using hAct

  rw [hVertex] at hSpec
  simpa using hSpec

theorem fixes_A_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct : vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.A = T.A := by
  simpa using
    fixes_vertex_of_vertexAction_eq_one
      (Geo := Geo) T g hAct (0 : Fin 5)

theorem fixes_B_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct : vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.B = T.B := by
  simpa using
    fixes_vertex_of_vertexAction_eq_one
      (Geo := Geo) T g hAct (1 : Fin 5)

theorem fixes_C_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct : vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.C = T.C := by
  simpa using
    fixes_vertex_of_vertexAction_eq_one
      (Geo := Geo) T g hAct (2 : Fin 5)

theorem fixes_D_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct : vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.D = T.D := by
  simpa using
    fixes_vertex_of_vertexAction_eq_one
      (Geo := Geo) T g hAct (3 : Fin 5)

theorem fixes_E_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct : vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.E = T.E := by
  simpa using
    fixes_vertex_of_vertexAction_eq_one
      (Geo := Geo) T g hAct (4 : Fin 5)

end CoxeterA4S5
end Geometry

-- ============================================================
-- Corrected E4 rigidity layer from CoxeterA4S5_test15_fix3.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

/-!
# Coxeter A4 -> S5, test15

Corrected E4 perpendicular-bisector kernel.

This file ports the old 3D equidistant-point lemmas to the genuine E4
architecture.  No ambient `HilbertSpaceIncidence`, `HilbertSpaceOrder`, or
`HilbertSpaceCongruence` instance is used.

The three main outputs are:

* ambient midpoint existence in corrected E4;
* an equidistant non-midpoint point gives a right angle at the midpoint;
* hence the line through that point and the midpoint is perpendicular to the
  endpoint line.

These are the metric ingredients needed for the synthetic proof of the
five-anchor uniqueness boundary used in test14.
-/

/--
Local generic midpoint uniqueness used inside induced `PlaneGeo` slices.

This lemma is purely planar.  It is copied here from the old 3D workshop
argument so that the corrected E4 route does not import any ambient 3D module.
-/
theorem hilbert_midpoint_unique_generic
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B M N : Geo.Point)
    (hM : HilbertIsMidpoint Geo M A B)
    (hN : HilbertIsMidpoint Geo N A B) :
    M = N := by

  by_contra hMN

  have hMData :=
    HilbertOrder.between_incidence
      A M B hM.1

  have hNData :=
    HilbertOrder.between_incidence
      A N B hN.1

  have hAM : Ne A M :=
    hMData.1

  have hAN : Ne A N :=
    hNData.1

  have hAB : Ne A B :=
    hMData.2.2.1

  rcases hMData.2.2.2.1 with
    ⟨l, hAl, hMl, hBl⟩

  have hNl :
      HilbertIncidence.OnLine N l :=
    hilbert_between_on_line
      Geo A N B l
      hAl hBl hN.1

  have hAMN :
      PrimCollinear Geo A M N :=
    ⟨l, hAl, hMl, hNl⟩

  rcases
      hilbert_between_trichotomy
        Geo A M N
        hAM hMN hAN
        hAMN with
    hA_M_N | hM_A_N | hA_N_M

  ----------------------------------------------------------------------
  -- Case A-M-N.
  ----------------------------------------------------------------------

  · have hM_N_B :
        Geo.Between M N B :=
      (hilbert_between_inner_trans
        Geo A M N B
        hA_M_N hN.1).1

    have hAM_AN :
        HilbertSegmentLess Geo A M A N :=
      ⟨M,
       hA_M_N,
       hilbert_congruent_reflexive
         Geo A M⟩

    have hMB_AN :
        HilbertSegmentLess Geo M B A N :=
      bookZero_32_lessThanCongruence2
        Geo
        A M A N
        M B
        hAM_AN
        hM.2

    have hMB_NB :
        HilbertSegmentLess Geo M B N B :=
      bookZero_30_lessThanCongruence
        Geo
        M B A N
        N B
        hMB_AN
        hN.2

    have hB_N_M :
        Geo.Between B N M :=
      (HilbertOrder.between_incidence
        M N B hM_N_B).2.2.2.2

    have hBN_BM :
        HilbertSegmentLess Geo B N B M :=
      ⟨N,
       hB_N_M,
       hilbert_congruent_reflexive
         Geo B N⟩

    have hBN_NB :
        Geo.Congruent B N N B :=
      (Geometry.Geo.congruent_reverse_second
        Geo B N B N).mp
        (hilbert_congruent_reflexive
          Geo B N)

    have hNB_BM :
        HilbertSegmentLess Geo N B B M :=
      bookZero_32_lessThanCongruence2
        Geo
        B N B M
        N B
        hBN_BM
        hBN_NB

    have hBM_MB :
        Geo.Congruent B M M B :=
      (Geometry.Geo.congruent_reverse_second
        Geo B M B M).mp
        (hilbert_congruent_reflexive
          Geo B M)

    have hNB_MB :
        HilbertSegmentLess Geo N B M B :=
      bookZero_30_lessThanCongruence
        Geo
        N B B M
        M B
        hNB_BM
        hBM_MB

    have hSelf :
        HilbertSegmentLess Geo M B M B :=
      bookZero_52_lessThanTransitive
        Geo
        M B N B M B
        hMB_NB
        hNB_MB

    rcases hSelf with
      ⟨Q, hMQB, hMB_MQ⟩

    have hMQ_MB :
        Geo.Congruent M Q M B :=
      hilbert_congruent_symmetry
        Geo
        M B M Q
        hMB_MQ

    exact
      (bookZero_45_partNotEqualWhole
        Geo M Q B hMQB)
        hMQ_MB

  ----------------------------------------------------------------------
  -- Case M-A-N is impossible because M itself is between A and B.
  ----------------------------------------------------------------------

  · have hM_A_B :
        Geo.Between M A B :=
      (hilbert_between_outer_trans
        Geo M A N B
        hM_A_N hN.1).2

    have hNo :
        Not (Geo.Between M A B) :=
      (HilbertOrder.between_unique
        A M B
        hMData.2.2.2.1
        hM.1).1

    exact hNo hM_A_B

  ----------------------------------------------------------------------
  -- Case A-N-M, symmetric to the first case.
  ----------------------------------------------------------------------

  · have hN_M_B :
        Geo.Between N M B :=
      (hilbert_between_inner_trans
        Geo A N M B
        hA_N_M hM.1).1

    have hAN_AM :
        HilbertSegmentLess Geo A N A M :=
      ⟨N,
       hA_N_M,
       hilbert_congruent_reflexive
         Geo A N⟩

    have hNB_AM :
        HilbertSegmentLess Geo N B A M :=
      bookZero_32_lessThanCongruence2
        Geo
        A N A M
        N B
        hAN_AM
        hN.2

    have hNB_MB :
        HilbertSegmentLess Geo N B M B :=
      bookZero_30_lessThanCongruence
        Geo
        N B A M
        M B
        hNB_AM
        hM.2

    have hB_M_N :
        Geo.Between B M N :=
      (HilbertOrder.between_incidence
        N M B hN_M_B).2.2.2.2

    have hBM_BN :
        HilbertSegmentLess Geo B M B N :=
      ⟨M,
       hB_M_N,
       hilbert_congruent_reflexive
         Geo B M⟩

    have hBM_MB :
        Geo.Congruent B M M B :=
      (Geometry.Geo.congruent_reverse_second
        Geo B M B M).mp
        (hilbert_congruent_reflexive
          Geo B M)

    have hMB_BN :
        HilbertSegmentLess Geo M B B N :=
      bookZero_32_lessThanCongruence2
        Geo
        B M B N
        M B
        hBM_BN
        hBM_MB

    have hBN_NB :
        Geo.Congruent B N N B :=
      (Geometry.Geo.congruent_reverse_second
        Geo B N B N).mp
        (hilbert_congruent_reflexive
          Geo B N)

    have hMB_NB :
        HilbertSegmentLess Geo M B N B :=
      bookZero_30_lessThanCongruence
        Geo
        M B B N
        N B
        hMB_BN
        hBN_NB

    have hSelf :
        HilbertSegmentLess Geo N B N B :=
      bookZero_52_lessThanTransitive
        Geo
        N B M B N B
        hNB_MB
        hMB_NB

    rcases hSelf with
      ⟨Q, hNQB, hNB_NQ⟩

    have hNQ_NB :
        Geo.Congruent N Q N B :=
      hilbert_congruent_symmetry
        Geo
        N B N Q
        hNB_NQ

    exact
      (bookZero_45_partNotEqualWhole
        Geo N Q B hNQB)
        hNQ_NB


variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]

/--
Every nondegenerate ambient E4 segment has a strict midpoint.

The midpoint is constructed in one dimension-free ambient plane containing
that segment and then transported back to the ambient point type.
-/
theorem hilbert4D_midpoint_exists_corrected
    (X Y : Geo.Point)
    (hXY : Ne X Y) :
    exists M : Geo.Point,
      HilbertIsMidpoint Geo M X Y := by

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X Y hXY with
    ⟨l, hXl, hYl⟩

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨R, hRl⟩

  have hXYR :
      Not (PrimCollinear Geo X Y R) := by
    intro hCol
    apply hRl
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hXY
        hXl hYl
        hCol

  rcases
      D.plane_through
        X Y R hXYR with
    ⟨sigma, hXsigma, hYsigma, hRsigma⟩

  have hlsigma :
      HilbertLineInPlane Geo l sigma :=
    D.line_in_plane
      X Y hXY
      l hXl hYl
      sigma hXsigma hYsigma

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hXsigma⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hYsigma⟩

  have hXYp : Ne Xp Yp := by
    intro h
    apply hXY
    exact congrArg Subtype.val h

  let : HilbertCongruence (PlaneGeo Geo sigma) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      sigma
      X Y R
      hXsigma hYsigma hRsigma
      hXYR

  rcases
      HilbertMidpointExists
        (PlaneGeo Geo sigma)
        Xp Yp hXYp with
    ⟨Mp, hMidPlane⟩

  let M : Geo.Point := Mp.1

  have hBetween :
      Geo.Between X M Y := by
    have h :=
      (planeGeo_between
        (Geo := Geo)
        sigma Xp Mp Yp).mp
        hMidPlane.1
    simpa [Xp, Yp, M] using h

  have hCong :
      Geo.Congruent X M M Y := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        sigma Xp Mp Mp Yp).mp
        hMidPlane.2
    simpa [Xp, Yp, M] using h

  exact
    ⟨M, hBetween, hCong⟩


/--
If `P` is equidistant from `X` and `Y` and differs from their midpoint `M`,
then `X,M,P` are noncollinear.

The proof stays in one dimension-free plane and uses ordinary planar midpoint
uniqueness there.
-/
theorem hilbert4D_equidistant_noncollinear_of_ne_midpoint_corrected
    (X Y M P : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M X Y)
    (hPX_PY : Geo.Congruent P X P Y)
    (hPM : Ne P M) :
    Not (PrimCollinear Geo X M P) := by

  intro hXMP

  have hMidData :=
    H4O.between_incidence
      X M Y hMid.1

  have hXM : Ne X M :=
    hMidData.1

  have hXY : Ne X Y :=
    hMidData.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X Y hXY with
    ⟨l, hXl, hYl⟩

  have hXYM :
      PrimCollinear Geo X Y M :=
    PrimCollinearRotate
      Geo X M Y hMidData.2.2.2.1

  have hMl :
      H.OnLine M l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hXY
      hXl hYl
      hXYM

  have hPl :
      H.OnLine P l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hXM
      hXl hMl
      hXMP

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨R, hRl⟩

  have hXYR :
      Not (PrimCollinear Geo X Y R) := by
    intro hCol
    apply hRl
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hXY
        hXl hYl
        hCol

  rcases
      D.plane_through
        X Y R hXYR with
    ⟨sigma, hXsigma, hYsigma, hRsigma⟩

  have hlsigma :
      HilbertLineInPlane Geo l sigma :=
    D.line_in_plane
      X Y hXY
      l hXl hYl
      sigma hXsigma hYsigma

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hXsigma⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hYsigma⟩

  let Mp : PlanePoint Geo sigma :=
    ⟨M, hlsigma M hMl⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hlsigma P hPl⟩

  have hXYp : Ne Xp Yp := by
    intro h
    apply hXY
    exact congrArg Subtype.val h

  let : HilbertCongruence (PlaneGeo Geo sigma) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      sigma
      X Y R
      hXsigma hYsigma hRsigma
      hXYR

  have hMidPlane :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        Mp Xp Yp := by
    constructor
    · apply
        (planeGeo_between
          (Geo := Geo)
          sigma Xp Mp Yp).mpr
      exact hMid.1
    · apply
        (planeGeo_congruent
          (Geo := Geo)
          sigma Xp Mp Mp Yp).mpr
      exact hMid.2

  have hEqPlane :
      (PlaneGeo Geo sigma).Congruent
        Pp Xp Pp Yp := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma Pp Xp Pp Yp).mpr
    exact hPX_PY

  have hPpXp : Ne Pp Xp := by
    intro hPX

    have hNull :
        (PlaneGeo Geo sigma).Congruent
          Xp Yp Xp Xp := by
      have hEq := hEqPlane
      rw [hPX] at hEq
      exact
        hilbert_congruent_symmetry
          (PlaneGeo Geo sigma)
          Xp Xp Xp Yp
          hEq

    have hBad :
        Xp = Yp :=
      bookZero_nullSegment1
        (PlaneGeo Geo sigma)
        Xp Yp Xp
        hNull

    exact hXYp hBad

  have hPpYp : Ne Pp Yp := by
    intro hPY

    have hEq := hEqPlane
    rw [hPY] at hEq

    have hBad :
        Yp = Xp :=
      bookZero_nullSegment1
        (PlaneGeo Geo sigma)
        Yp Xp Yp
        hEq

    exact hXYp hBad.symm

  have hColPlane :
      PrimCollinear
        (PlaneGeo Geo sigma)
        Xp Pp Yp := by
    let lp : PlaneLine Geo sigma :=
      ⟨l, hlsigma⟩
    exact
      ⟨lp, hXl, hPl, hYl⟩

  have hBetweenP :
      (PlaneGeo Geo sigma).Between
        Xp Pp Yp :=
    hilbert_between_of_collinear_equidistant
      (PlaneGeo Geo sigma)
      Xp Pp Yp
      hPpXp
      hPpYp
      hXYp
      hColPlane
      hEqPlane

  have hXP_PY :
      (PlaneGeo Geo sigma).Congruent
        Xp Pp Pp Yp :=
    (Geometry.Geo.congruent_reverse_first
      (PlaneGeo Geo sigma)
      Pp Xp Pp Yp).mp
      hEqPlane

  have hMidP :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        Pp Xp Yp :=
    ⟨hBetweenP, hXP_PY⟩

  have hMP :
      Mp = Pp :=
    hilbert_midpoint_unique_generic
      (PlaneGeo Geo sigma)
      Xp Yp Mp Pp
      hMidPlane
      hMidP

  apply hPM
  exact congrArg Subtype.val hMP.symm


/--
A non-midpoint point equidistant from `X` and `Y` determines a right angle
at the midpoint:

    angle XMP is right.

The metric step is the corrected ambient E4 SSS theorem.
-/
theorem hilbert4D_equidistant_rightAngle_at_midpoint_corrected
    (X Y M P : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M X Y)
    (hPX_PY : Geo.Congruent P X P Y)
    (hPM : Ne P M) :
    HilbertRightAngle Geo X M P := by

  have hXMP :
      Not (PrimCollinear Geo X M P) :=
    hilbert4D_equidistant_noncollinear_of_ne_midpoint_corrected
      (Geo := Geo)
      X Y M P
      hMid hPX_PY hPM

  have hMidData :=
    H4O.between_incidence
      X M Y hMid.1

  have hXY : Ne X Y :=
    hMidData.2.2.1

  have hXM : Ne X M :=
    hMidData.1

  have hMY : Ne M Y :=
    hMidData.2.1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X Y hXY with
    ⟨n, hXn, hYn⟩

  have hXYM :
      PrimCollinear Geo X Y M :=
    PrimCollinearRotate
      Geo X M Y hMidData.2.2.2.1

  have hMn :
      H.OnLine M n :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hXY
      hXn hYn
      hXYM

  have hMYP :
      Not (PrimCollinear Geo M Y P) := by
    intro hCol
    rcases hCol with
      ⟨k, hMk, hYk, hPk⟩

    have hnk : n = k :=
      HilbertPlaneIncidence.line_unique
        M Y hMY
        n k
        hMn hYn
        hMk hYk

    have hPn : H.OnLine P n := by
      rw [hnk]
      exact hPk

    exact
      hXMP
        ⟨n, hXn, hMn, hPn⟩

  rcases
      D.plane_through
        M Y P hMYP with
    ⟨sigma, hMsigma, hYsigma, hPsigma⟩

  let Mp : PlanePoint Geo sigma :=
    ⟨M, hMsigma⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hYsigma⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hPsigma⟩

  have hMX_MY :
      Geo.Congruent M X M Y :=
    (Geometry.Geo.congruent_reverse_first
      Geo X M M Y).mp
      hMid.2

  have hXP_YP :
      Geo.Congruent X P Y P := by
    have h1 :
        Geo.Congruent X P P Y :=
      (Geometry.Geo.congruent_reverse_first
        Geo P X P Y).mp
        hPX_PY

    exact
      (Geometry.Geo.congruent_reverse_second
        Geo X P P Y).mp
        h1

  have hMP_MP :
      Geo.Congruent M P M P :=
    hilbert4D_ambient_congruent_reflexive_corrected
      (Geo := Geo)
      M P

  have hAngle :
      Geo.AngleCongruent
        X M P
        Y M P :=
    hilbert4D_ambient_sss_angleA_in_plane_corrected
      (Geo := Geo)
      sigma
      M X P
      Mp Yp Pp
      (by
        intro h
        exact
          hXMP
            (PrimCollinearSwap
              Geo M X P h))
      hMYP
      hMX_MY
      hXP_YP
      hMP_MP

  have hAngleRight :
      Geo.AngleCongruent
        X M P
        P M Y := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [Geometry.Geo.angle_swap
      Geo Y M P] at hAngle

    exact hAngle

  exact
    ⟨Y,
     hMid.1,
     hAngleRight⟩


/--
The endpoint line `XY` is perpendicular at the midpoint `M` to the line `MP`
for every non-midpoint point `P` equidistant from `X` and `Y`.
-/
theorem hilbert4D_equidistant_line_perpendicular_corrected
    (X Y M P : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M X Y)
    (hPX_PY : Geo.Congruent P X P Y)
    (hPM : Ne P M) :
    exists n m : Geo.Line,
      H.OnLine X n /\
      H.OnLine Y n /\
      H.OnLine M m /\
      H.OnLine P m /\
      HilbertLinesPerpendicularAt Geo n m M := by

  have hMidData :=
    H4O.between_incidence
      X M Y hMid.1

  have hXY : Ne X Y :=
    hMidData.2.2.1

  have hXM : Ne X M :=
    hMidData.1

  have hXMP :
      Not (PrimCollinear Geo X M P) :=
    hilbert4D_equidistant_noncollinear_of_ne_midpoint_corrected
      (Geo := Geo)
      X Y M P
      hMid hPX_PY hPM

  have hRight :
      HilbertRightAngle Geo X M P :=
    hilbert4D_equidistant_rightAngle_at_midpoint_corrected
      (Geo := Geo)
      X Y M P
      hMid hPX_PY hPM

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X Y hXY with
    ⟨n, hXn, hYn⟩

  have hXYM :
      PrimCollinear Geo X Y M :=
    PrimCollinearRotate
      Geo X M Y hMidData.2.2.2.1

  have hMn :
      H.OnLine M n :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hXY
      hXn hYn
      hXYM

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        M P hPM.symm with
    ⟨m, hMm, hPm⟩

  have hPerp :
      HilbertLinesPerpendicularAt
        Geo n m M := by
    exact
      ⟨hMn,
       hMm,
       ⟨X, P,
        hXM,
        hPM,
        hXn,
        hPm,
        hXMP,
        hRight⟩⟩

  exact
    ⟨n, m,
     hXn, hYn,
     hMm, hPm,
     hPerp⟩

end CoxeterA4S5

end Geometry

-- ============================================================
-- Corrected E4 rigidity layer from CoxeterA4S5_test16.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]

/-!
# Coxeter A4 -> S5, test16

Hyperplane closure of the corrected E4 perpendicular-bisector locus.

This file proves two dimension-safe facts.

1. If `n` is normal to an E4 hyperplane `Sigma` at `M`, then every line
   through `M` perpendicular to `n` lies in `Sigma`.

2. Consequently, if `M` is the midpoint of `XY`, the line `XY` is normal
   to `Sigma` at `M`, and `P` is equidistant from `X` and `Y`, then
   `P` lies in `Sigma`.

No new E4 axiom is introduced here.  The proof of the first fact uses:

* the dimension-free plane through two intersecting lines;
* the corrected plane-hyperplane common-line theorem;
* the marked-plane metric package;
* uniqueness of a perpendicular through a fixed point inside one 2-plane.
-/

/--
If `n` is normal to `Sigma` at `M`, every line `m` through `M`
perpendicular to `n` is contained in `Sigma`.

The argument is two-dimensional after constructing `pi = plane(n,m)`.
The intersection `pi cap Sigma` contains a line `s` through `M`.
Both `m` and `s` are perpendicular to `n` in `pi`, hence planar
perpendicular uniqueness gives `m = s`.
-/
theorem hilbert4D_line_in_hyperplane_of_perpendicular_to_normal_corrected
    (Sigma : Q.Hyperplane)
    (n m : Geo.Line)
    (M : Geo.Point)
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo n Sigma M)
    (hPerp :
      HilbertLinesPerpendicularAt
        Geo n m M) :
    HilbertLineInHyperplane4
      Geo m Sigma := by

  have hMn :
      H.OnLine M n :=
    hNormal.1

  have hMm :
      H.OnLine M m :=
    hPerp.2.1

  have hMSigma :
      Q.OnHyperplane M Sigma :=
    hNormal.2.1

  have hPiExists :=
    hilbert_dimension_free_plane_through_intersecting_lines
      (Geo := Geo)
      n m M
      hMn hMm

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hPiExists

  have hPiData :=
    Classical.choose_spec hPiExists

  have hnpi :
      HilbertLineInPlane Geo n pi :=
    hPiData.1

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    hPiData.2

  have hMpi :
      Q.toHilbertSpacePrimitive.OnPlane M pi :=
    hnpi M hMn

  rcases
      hilbert4D_plane_hyperplane_common_line
        (Geo := Geo)
        pi Sigma M
        hMpi hMSigma with
    ⟨s, hMs, hspi, hsSigma⟩

  have hNperpS :
      HilbertLinesPerpendicularAt
        Geo n s M :=
    hNormal.2.2
      s hsSigma hMs

  rcases
      D.three_noncollinear_on_plane pi with
    ⟨U, V, W,
     hUpi, hVpi, hWpi,
     hUVW⟩

  let : HilbertCongruence
      (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi
      U V W
      hUpi hVpi hWpi
      hUVW

  let np : PlaneLine Geo pi :=
    ⟨n, hnpi⟩

  let mp : PlaneLine Geo pi :=
    ⟨m, hmpi⟩

  let sp : PlaneLine Geo pi :=
    ⟨s, hspi⟩

  let Mp : PlanePoint Geo pi :=
    ⟨M, hMpi⟩

  have hNperpMPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi)
        np mp Mp :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi np mp Mp).mpr
      hPerp

  have hMperpNPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi)
        mp np Mp :=
    hilbert_linesPerpendicularAt_symm_neutral
      (PlaneGeo Geo pi)
      np mp Mp
      hNperpMPlane

  have hNperpSPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi)
        np sp Mp :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi np sp Mp).mpr
      hNperpS

  have hSperpNPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi)
        sp np Mp :=
    hilbert_linesPerpendicularAt_symm_neutral
      (PlaneGeo Geo pi)
      np sp Mp
      hNperpSPlane

  have hMperpN :
      HilbertLinesPerpendicularAt
        Geo m n M :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi mp np Mp).mp
      hMperpNPlane

  have hSperpN :
      HilbertLinesPerpendicularAt
        Geo s n M :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi sp np Mp).mp
      hSperpNPlane

  have hEqPlane :
      mp = sp :=
    planeGeo_perpendicular_same_foot_unique4_corrected
      (Geo := Geo)
      pi
      U V W
      hUpi hVpi hWpi
      hUVW
      mp sp np Mp
      hMperpN
      hSperpN

  have hms :
      m = s :=
    congrArg Subtype.val hEqPlane

  rw [hms]

  exact hsSigma


/--
Let `M` be the midpoint of `XY`, and let `n = XY` be normal to
`Sigma` at `M`.  Then every point equidistant from `X` and `Y`
lies in `Sigma`.

For `P != M`, test15 supplies the line `MP` perpendicular to `XY`.
The preceding theorem then puts the whole line `MP` in `Sigma`.
-/
theorem hilbert4D_equidistant_point_on_hyperplane_of_normal_corrected
    (Sigma : Q.Hyperplane)
    (n : Geo.Line)
    (X Y M P : Geo.Point)
    (hXn : H.OnLine X n)
    (hYn : H.OnLine Y n)
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo n Sigma M)
    (hMid :
      HilbertIsMidpoint Geo M X Y)
    (hPX_PY :
      Geo.Congruent P X P Y) :
    Q.OnHyperplane P Sigma := by

  by_cases hPM :
      P = M

  · subst P
    exact hNormal.2.1

  · have hMidData :=
      H4O.between_incidence
        X M Y hMid.1

    have hXY :
        Ne X Y :=
      hMidData.2.2.1

    rcases
        hilbert4D_equidistant_line_perpendicular_corrected
          (Geo := Geo)
          X Y M P
          hMid hPX_PY hPM with
      ⟨n', m,
       hXn', hYn',
       hMm, hPm,
       hNperpM⟩

    have hn'n :
        n' = n :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        n' n
        hXn' hYn'
        hXn hYn

    subst n'

    have hmSigma :
        HilbertLineInHyperplane4
          Geo m Sigma :=
      hilbert4D_line_in_hyperplane_of_perpendicular_to_normal_corrected
        (Geo := Geo)
        Sigma n m M
        hNormal
        hNperpM

    exact
      hmSigma P hPm

end CoxeterA4S5

end Geometry

-- ============================================================
-- Corrected E4 rigidity layer from CoxeterA4S5_test17.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo]

/-!
# Coxeter A4 -> S5, test17

Synthetic E4 perpendicular-bisector hyperplane from three independent
equidistant points.

Let M be the midpoint of XY. Assume P1, P2, P3 are all equidistant
from X and Y and that M,P1,P2,P3 are noncoplanar.

Then:

* M,P1,P2,P3 determine an E4 hyperplane Sigma;
* the lines MP1, MP2, MP3 form a spanning frame of Sigma;
* the line XY is perpendicular to each of those three frame directions;
* the corrected E4 hyperplane XI.4 criterion therefore gives
  XY perpendicular to Sigma at M;
* test16 then shows that every further point equidistant from X and Y
  lies in Sigma.

The only explicit extra boundary is
`Hilbert4DHyperplanePerpendicularFrameCriterion_corrected`.
-/

/--
Three independent points of the equidistant locus determine the whole
corrected E4 perpendicular-bisector hyperplane.

The conclusion includes the universal closure statement:
every Z satisfying ZX = ZY lies in the same hyperplane Sigma.
-/
theorem hilbert4D_equidistant_hyperplane_of_three_independent_points_corrected
    (X Y M P1 P2 P3 : Geo.Point)
    (hMid :
      HilbertIsMidpoint Geo M X Y)
    (hP1X_P1Y :
      Geo.Congruent P1 X P1 Y)
    (hP2X_P2Y :
      Geo.Congruent P2 X P2 Y)
    (hP3X_P3Y :
      Geo.Congruent P3 X P3 Y)
    (hP1M : Ne P1 M)
    (hP2M : Ne P2 M)
    (hP3M : Ne P3 M)
    (hNoncop :
      Not (HilbertCoplanar4 Geo M P1 P2 P3)) :
    exists Sigma : Q.Hyperplane,
      Q.OnHyperplane M Sigma /\
      Q.OnHyperplane P1 Sigma /\
      Q.OnHyperplane P2 Sigma /\
      Q.OnHyperplane P3 Sigma /\
      exists n : Geo.Line,
        H.OnLine X n /\
        H.OnLine Y n /\
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo n Sigma M /\
        forall Z : Geo.Point,
          Geo.Congruent Z X Z Y ->
          Q.OnHyperplane Z Sigma := by

  have hMidData :=
    H4O.between_incidence
      X M Y hMid.1

  have hXY :
      Ne X Y :=
    hMidData.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X Y hXY with
    ⟨n, hXn, hYn⟩

  have hXYM :
      PrimCollinear Geo X Y M :=
    PrimCollinearRotate
      Geo X M Y
      hMidData.2.2.2.1

  have hMn :
      H.OnLine M n :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hXY
      hXn hYn
      hXYM

  rcases
      hilbert4D_equidistant_line_perpendicular_corrected
        (Geo := Geo)
        X Y M P1
        hMid hP1X_P1Y hP1M with
    ⟨n1, a,
     hXn1, hYn1,
     hMa, hP1a,
     hN1perpA⟩

  have hn1 :
      n1 = n :=
    HilbertPlaneIncidence.line_unique
      X Y hXY
      n1 n
      hXn1 hYn1
      hXn hYn

  subst n1

  rcases
      hilbert4D_equidistant_line_perpendicular_corrected
        (Geo := Geo)
        X Y M P2
        hMid hP2X_P2Y hP2M with
    ⟨n2, b,
     hXn2, hYn2,
     hMb, hP2b,
     hN2perpB⟩

  have hn2 :
      n2 = n :=
    HilbertPlaneIncidence.line_unique
      X Y hXY
      n2 n
      hXn2 hYn2
      hXn hYn

  subst n2

  rcases
      hilbert4D_equidistant_line_perpendicular_corrected
        (Geo := Geo)
        X Y M P3
        hMid hP3X_P3Y hP3M with
    ⟨n3, c,
     hXn3, hYn3,
     hMc, hP3c,
     hN3perpC⟩

  have hn3 :
      n3 = n :=
    HilbertPlaneIncidence.line_unique
      X Y hXY
      n3 n
      hXn3 hYn3
      hXn hYn

  subst n3

  rcases
      C4.hyperplane_through
        M P1 P2 P3
        hNoncop with
    ⟨Sigma,
     hMSigma,
     hP1Sigma,
     hP2Sigma,
     hP3Sigma⟩

  have haSigma :
      HilbertLineInHyperplane4
        Geo a Sigma :=
    C4.line_in_hyperplane
      M P1 hP1M.symm
      a hMa hP1a
      Sigma hMSigma hP1Sigma

  have hbSigma :
      HilbertLineInHyperplane4
        Geo b Sigma :=
    C4.line_in_hyperplane
      M P2 hP2M.symm
      b hMb hP2b
      Sigma hMSigma hP2Sigma

  have hcSigma :
      HilbertLineInHyperplane4
        Geo c Sigma :=
    C4.line_in_hyperplane
      M P3 hP3M.symm
      c hMc hP3c
      Sigma hMSigma hP3Sigma

  have hFrame :
      Hilbert4DHyperplaneFrameAt_corrected
        Geo Sigma M a b c := by

    unfold Hilbert4DHyperplaneFrameAt_corrected

    refine
      ⟨haSigma,
       hbSigma,
       hcSigma,
       hMa,
       hMb,
       hMc,
       ?_⟩

    exact
      ⟨P1, P2, P3,
       hP1a,
       hP2b,
       hP3c,
       hNoncop⟩

  have hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo n Sigma M :=
    hilbert4D_normal_of_spanning_perpendicular_frame_corrected
      (Geo := Geo)
      Sigma M
      n a b c
      hMn
      hFrame
      hN1perpA
      hN2perpB
      hN3perpC

  refine
    ⟨Sigma,
     hMSigma,
     hP1Sigma,
     hP2Sigma,
     hP3Sigma,
     n,
     hXn,
     hYn,
     hNormal,
     ?_⟩

  intro Z hZX_ZY

  exact
    hilbert4D_equidistant_point_on_hyperplane_of_normal_corrected
      (Geo := Geo)
      Sigma n
      X Y M Z
      hXn hYn
      hNormal
      hMid
      hZX_ZY

end CoxeterA4S5

end Geometry

-- ============================================================
-- Corrected E4 rigidity layer from CoxeterA4S5_test18_fix2.lean
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

/-!
# Coxeter A4 -> S5, test18

Selection of three independent anchors and frame-specific five-anchor
distance rigidity.

The five-anchor rigidity used in test14 is no longer assumed as a class.
For a Coxeter A4 simplex frame it is derived from:

* the incidence data already stored in the frame;
* the corrected E4 hyperplane-local 3D incidence layer;
* the perpendicular-bisector hyperplane theorem from test17;
* the corrected E4 hyperplane XI.4 frame criterion.

The key selection is economical.  The frame itself shows that A,B,C are
noncollinear and A,B,C,D are noncoplanar.  For an arbitrary point M:

* if M is outside plane ABC, use A,B,C;
* if M is in plane ABC, at least one of MAB, MAC, MBC is noncollinear,
  and adjoining D gives the required noncoplanar four-tuple.
-/

/-
Among three noncollinear points A,B,C and an arbitrary point M, at least
one of MAB, MAC, MBC is noncollinear.
-/
section PairSelection

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]

theorem noncollinear_pair_with_plane_point_A4
    (M A B C : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C)) :
    Not (PrimCollinear Geo M A B) \/
    Not (PrimCollinear Geo M A C) \/
    Not (PrimCollinear Geo M B C) := by

  by_cases hMA : M = A

  · subst A
    exact Or.inr (Or.inr hABC)

  · by_cases hMB : M = B

    · subst B

      have hAMC :
          Not (PrimCollinear Geo M A C) := by
        intro hCol
        apply hABC
        exact
          PrimCollinearSwap
            (Geo := Geo)
            M A C
            hCol

      exact Or.inr (Or.inl hAMC)

    · by_cases hMC : M = C

      · subst C

        have hMAB :
            Not (PrimCollinear Geo M A B) := by
          intro hCol
          apply hABC

          have hABM :
              PrimCollinear Geo A B M :=
            PrimCollinearCycle
              (Geo := Geo)
              M A B
              hCol

          exact hABM

        exact Or.inl hMAB

      · by_cases hMAB :
          PrimCollinear Geo M A B

        · by_cases hMAC :
            PrimCollinear Geo M A C

          · rcases hMAB with
              ⟨l, hMl, hAl, hBl⟩

            rcases hMAC with
              ⟨m, hMm, hAm, hCm⟩

            have hlm :
                l = m :=
              HilbertPlaneIncidence.line_unique
                M A hMA
                l m
                hMl hAl
                hMm hAm

            subst m

            exact
              False.elim
                (hABC
                  ⟨l,
                   hAl,
                   hBl,
                   hCm⟩)

          · exact Or.inr (Or.inl hMAC)

        · exact Or.inl hMAB


end PairSelection


/-
If A,B,C are noncollinear points of pi and D0 is outside pi, then
A,B,C,D0 are noncoplanar.
-/
section PlaneHelpers

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]

theorem not_coplanar4_of_three_on_plane_fourth_off_A4
    (A B C D0 : Geo.Point)
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hBpi :
      Q.toHilbertSpacePrimitive.OnPlane B pi)
    (hCpi :
      Q.toHilbertSpacePrimitive.OnPlane C pi)
    (hDoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane D0 pi)) :
    Not (HilbertCoplanar4 Geo A B C D0) := by

  intro hCop

  rcases hCop with
    ⟨rho,
     hArho,
     hBrho,
     hCrho,
     hDrho⟩

  have hrhopi :
      rho = pi :=
    D.plane_unique
      A B C hABC
      rho pi
      hArho hBrho hCrho
      hApi hBpi hCpi

  rw [hrhopi] at hDrho

  exact hDoff hDrho


/-
A line together with a point outside it lies in a primitive ambient plane.

This local helper keeps test18 on the production dimension-free incidence
interface and avoids importing the older Smith-flat workshop files.
-/
theorem plane_through_line_and_external_point_A4
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l)) :
    exists pi : Q.toHilbertSpacePrimitive.Plane,
      HilbertLineInPlane Geo l pi /\
      Q.toHilbertSpacePrimitive.OnPlane P pi := by

  rcases
      HilbertDimensionFreeIncidence.two_points_on_each_line
        (Geo := Geo) l with
    ⟨A, B, hAB, hAl, hBl⟩

  have hABP :
      Not (PrimCollinear Geo A B P) := by
    intro hCol
    exact
      hPl
        (hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hAB hAl hBl hCol)

  rcases
      HilbertDimensionFreeIncidence.plane_through
        (Geo := Geo)
        A B P hABP with
    ⟨pi, hApi, hBpi, hPpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi := by
    exact
      HilbertDimensionFreeIncidence.line_in_plane
        (Geo := Geo)
        A B hAB
        l hAl hBl
        pi hApi hBpi

  exact ⟨pi, hlpi, hPpi⟩


/-
If four points are not coplanar, then the first three are noncollinear.

This is the dimension-free incidence proof used locally by test18.
-/
theorem noncoplanar4_first_three_noncollinear_A4
    (A B C D0 : Geo.Point)
    (hNoncop :
      Not (HilbertCoplanar4 Geo A B C D0)) :
    Not (PrimCollinear Geo A B C) := by

  intro hABC
  rcases hABC with ⟨l, hAl, hBl, hCl⟩

  by_cases hDl : H.OnLine D0 l

  · rcases
        hilbert_point_off_line
          (Geo := Geo) l with
      ⟨P, hPl⟩

    rcases
        plane_through_line_and_external_point_A4
          (Geo := Geo) l P hPl with
      ⟨pi, hlpi, _hPpi⟩

    exact
      hNoncop
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hlpi D0 hDl⟩

  · rcases
        plane_through_line_and_external_point_A4
          (Geo := Geo) l D0 hDl with
      ⟨pi, hlpi, hDpi⟩

    exact
      hNoncop
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hDpi⟩


/-
A noncoplanar four-tuple A,B,C,D has A distinct from B,C,D.
-/
theorem noncoplanar4_first_ne_others_A4
    (A B C D0 : Geo.Point)
    (hNoncop :
      Not (HilbertCoplanar4 Geo A B C D0)) :
    Ne B A /\ Ne C A /\ Ne D0 A := by

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    noncoplanar4_first_three_noncollinear_A4
      (Geo := Geo)
      A B C D0
      hNoncop

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC :
      Ne A C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (by
        intro h
        apply hABC
        exact
          PrimCollinearRotate
            Geo A C B h)

  have hPerm :
      Not (HilbertCoplanar4 Geo A B D0 C) := by
    intro hCop
    rcases hCop with
      ⟨pi, hApi, hBpi, hDpi, hCpi⟩
    exact
      hNoncop
        ⟨pi,
         hApi,
         hBpi,
         hCpi,
         hDpi⟩

  have hABD :
      Not (PrimCollinear Geo A B D0) :=
    noncoplanar4_first_three_noncollinear_A4
      (Geo := Geo)
      A B D0 C
      hPerm

  have hAD :
      Ne A D0 :=
    hilbert_noncollinear_ne_first
      Geo A D0 B
      (by
        intro h
        apply hABD
        exact
          PrimCollinearRotate
            Geo A D0 B h)

  exact
    ⟨hAB.symm,
     hAC.symm,
     hAD.symm⟩


end PlaneHelpers


/-
The first face A,B,C of a Coxeter A4 simplex frame is noncollinear.

A and B lie in Sigma3, while C is outside Sigma3.
-/
section FrameFace

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]

theorem simplexFrame_ABC_noncollinear
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Not (PrimCollinear Geo T.A T.B T.C) := by

  rcases
      vertices_pairwise_ne
        (Geo := Geo) T with
    ⟨hAB, _hAC, _hAD, _hAE,
     _hBC, _hBD, _hBE,
     _hCD, _hCE, _hDE⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        T.A T.B hAB with
    ⟨l, hAl, hBl⟩

  have hlSigma3 :
      HilbertLineInHyperplane4
        Geo l T.Sigma3 :=
    C4.line_in_hyperplane
      T.A T.B hAB
      l hAl hBl
      T.Sigma3
      T.A_on_Sigma3
      T.B_on_Sigma3

  intro hABC

  have hCl :
      H.OnLine T.C l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAB
      hAl hBl
      hABC

  exact
    T.C_off_Sigma3
      (hlSigma3 T.C hCl)


end FrameFace


/-
The four vertices A,B,C,D of a Coxeter A4 simplex frame are noncoplanar.

The plane through A,B,C would lie in Sigma4, whereas D is outside Sigma4.
-/
section FrameSelection

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]

theorem simplexFrame_ABCD_noncoplanar
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Not (HilbertCoplanar4 Geo T.A T.B T.C T.D) := by

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    simplexFrame_ABC_noncollinear
      (Geo := Geo) T

  intro hCop

  rcases hCop with
    ⟨pi,
     hApi,
     hBpi,
     hCpi,
     hDpi⟩

  have hpiSigma4 :
      HilbertPlaneInHyperplane4
        Geo pi T.Sigma4 :=
    H4L.plane_in_hyperplane
      T.A T.B T.C hABC
      pi
      hApi hBpi hCpi
      T.Sigma4
      T.A_on_Sigma4
      T.B_on_Sigma4
      T.C_on_Sigma4

  exact
    T.D_off_Sigma4
      (hpiSigma4 T.D hDpi)


/-
For every ambient point M, three of A,B,C,D form with M a noncoplanar
four-tuple.
-/
theorem simplexFrame_three_anchor_noncoplanar_with_point
    (T : CoxeterA4SmithSimplexFrame Geo)
    (M : Geo.Point) :
    Not (HilbertCoplanar4 Geo M T.A T.B T.C) \/
    Not (HilbertCoplanar4 Geo M T.A T.B T.D) \/
    Not (HilbertCoplanar4 Geo M T.A T.C T.D) \/
    Not (HilbertCoplanar4 Geo M T.B T.C T.D) := by

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    simplexFrame_ABC_noncollinear
      (Geo := Geo) T

  have hABCD :
      Not (HilbertCoplanar4 Geo T.A T.B T.C T.D) :=
    simplexFrame_ABCD_noncoplanar
      (Geo := Geo) T

  rcases
      D.plane_through
        T.A T.B T.C hABC with
    ⟨pi,
     hApi,
     hBpi,
     hCpi⟩

  have hDoffpi :
      Not
        (Q.toHilbertSpacePrimitive.OnPlane
          T.D pi) := by
    intro hDpi
    exact
      hABCD
        ⟨pi,
         hApi,
         hBpi,
         hCpi,
         hDpi⟩

  by_cases hMpi :
      Q.toHilbertSpacePrimitive.OnPlane
        M pi

  · rcases
        noncollinear_pair_with_plane_point_A4
          (Geo := Geo)
          M T.A T.B T.C hABC with
      hMAB | hMAC | hMBC

    · exact
        Or.inr
          (Or.inl
            (not_coplanar4_of_three_on_plane_fourth_off_A4
              (Geo := Geo)
              M T.A T.B T.D
              pi
              hMAB
              hMpi hApi hBpi
              hDoffpi))

    · exact
        Or.inr
          (Or.inr
            (Or.inl
              (not_coplanar4_of_three_on_plane_fourth_off_A4
                (Geo := Geo)
                M T.A T.C T.D
                pi
                hMAC
                hMpi hApi hCpi
                hDoffpi)))

    · exact
        Or.inr
          (Or.inr
            (Or.inr
              (not_coplanar4_of_three_on_plane_fourth_off_A4
                (Geo := Geo)
                M T.B T.C T.D
                pi
                hMBC
                hMpi hBpi hCpi
                hDoffpi)))

  · have hABCM :
        Not (HilbertCoplanar4 Geo T.A T.B T.C M) :=
      not_coplanar4_of_three_on_plane_fourth_off_A4
        (Geo := Geo)
        T.A T.B T.C M
        pi
        hABC
        hApi hBpi hCpi
        hMpi

    have hMABC :
        Not (HilbertCoplanar4 Geo M T.A T.B T.C) := by
      intro hCop
      rcases hCop with
        ⟨rho,
         hMrho,
         hArho,
         hBrho,
         hCrho⟩
      exact
        hABCM
          ⟨rho,
           hArho,
           hBrho,
           hCrho,
           hMrho⟩

    exact Or.inl hMABC


end FrameSelection


/-
Five-anchor distance rigidity for one Coxeter A4 simplex frame.

This is the frame-specific replacement for the old abstract
`Hilbert4DFiveAnchorDistanceUniqueness` boundary.
-/
section FiveAnchorRigidity

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo]

theorem simplexFrame_five_anchor_distance_unique
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X Y : Geo.Point)
    (hAX_AY :
      Geo.Congruent T.A X T.A Y)
    (hBX_BY :
      Geo.Congruent T.B X T.B Y)
    (hCX_CY :
      Geo.Congruent T.C X T.C Y)
    (hDX_DY :
      Geo.Congruent T.D X T.D Y)
    (hEX_EY :
      Geo.Congruent T.E X T.E Y) :
    X = Y := by

  by_contra hXY

  rcases
      hilbert4D_midpoint_exists_corrected
        (Geo := Geo)
        X Y hXY with
    ⟨M, hMid⟩

  have hSelect :=
    simplexFrame_three_anchor_noncoplanar_with_point
      (Geo := Geo)
      T M

  rcases hSelect with
    hMABC | hMABD | hMACD | hMBCD

  · rcases
        noncoplanar4_first_ne_others_A4
          (Geo := Geo)
          M T.A T.B T.C
          hMABC with
      ⟨hAM, hBM, hCM⟩

    rcases
        hilbert4D_equidistant_hyperplane_of_three_independent_points_corrected
          (Geo := Geo)
          X Y M
          T.A T.B T.C
          hMid
          hAX_AY hBX_BY hCX_CY
          hAM hBM hCM
          hMABC with
      ⟨Sigma,
       _hMSigma,
       _hASigma0,
       _hBSigma0,
       _hCSigma0,
       _n,
       _hXn,
       _hYn,
       _hNormal,
       hAll⟩

    apply T.nonhyperplanar

    exact
      ⟨Sigma,
       hAll T.A hAX_AY,
       hAll T.B hBX_BY,
       hAll T.C hCX_CY,
       hAll T.D hDX_DY,
       hAll T.E hEX_EY⟩

  · rcases
        noncoplanar4_first_ne_others_A4
          (Geo := Geo)
          M T.A T.B T.D
          hMABD with
      ⟨hAM, hBM, hDM⟩

    rcases
        hilbert4D_equidistant_hyperplane_of_three_independent_points_corrected
          (Geo := Geo)
          X Y M
          T.A T.B T.D
          hMid
          hAX_AY hBX_BY hDX_DY
          hAM hBM hDM
          hMABD with
      ⟨Sigma,
       _hMSigma,
       _hASigma0,
       _hBSigma0,
       _hDSigma0,
       _n,
       _hXn,
       _hYn,
       _hNormal,
       hAll⟩

    apply T.nonhyperplanar

    exact
      ⟨Sigma,
       hAll T.A hAX_AY,
       hAll T.B hBX_BY,
       hAll T.C hCX_CY,
       hAll T.D hDX_DY,
       hAll T.E hEX_EY⟩

  · rcases
        noncoplanar4_first_ne_others_A4
          (Geo := Geo)
          M T.A T.C T.D
          hMACD with
      ⟨hAM, hCM, hDM⟩

    rcases
        hilbert4D_equidistant_hyperplane_of_three_independent_points_corrected
          (Geo := Geo)
          X Y M
          T.A T.C T.D
          hMid
          hAX_AY hCX_CY hDX_DY
          hAM hCM hDM
          hMACD with
      ⟨Sigma,
       _hMSigma,
       _hASigma0,
       _hCSigma0,
       _hDSigma0,
       _n,
       _hXn,
       _hYn,
       _hNormal,
       hAll⟩

    apply T.nonhyperplanar

    exact
      ⟨Sigma,
       hAll T.A hAX_AY,
       hAll T.B hBX_BY,
       hAll T.C hCX_CY,
       hAll T.D hDX_DY,
       hAll T.E hEX_EY⟩

  · rcases
        noncoplanar4_first_ne_others_A4
          (Geo := Geo)
          M T.B T.C T.D
          hMBCD with
      ⟨hBM, hCM, hDM⟩

    rcases
        hilbert4D_equidistant_hyperplane_of_three_independent_points_corrected
          (Geo := Geo)
          X Y M
          T.B T.C T.D
          hMid
          hBX_BY hCX_CY hDX_DY
          hBM hCM hDM
          hMBCD with
      ⟨Sigma,
       _hMSigma,
       _hBSigma0,
       _hCSigma0,
       _hDSigma0,
       _n,
       _hXn,
       _hYn,
       _hNormal,
       hAll⟩

    apply T.nonhyperplanar

    exact
      ⟨Sigma,
       hAll T.A hAX_AY,
       hAll T.B hBX_BY,
       hAll T.C hCX_CY,
       hAll T.D hDX_DY,
       hAll T.E hEX_EY⟩

end FiveAnchorRigidity


end CoxeterA4S5

end Geometry

-- ============================================================
-- Final faithful action and S5 identification
-- ============================================================


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

namespace CoxeterA4S5

open CoxeterA4SmithSimplexFrame

/-!
# Coxeter A4 -> S5, test19

Close the faithfulness argument without the old abstract
`Hilbert4DFiveAnchorDistanceUniqueness` boundary.

The geometric input is now the frame-specific theorem proved in test18:
`simplexFrame_five_anchor_distance_unique`.

Thus the kernel of the vertex action is trivial for the corrected E4
architecture, and the generated geometric reflection group is isomorphic to
`Perm (Fin 5) = S5` without assuming the old five-anchor uniqueness class.
-/

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/--
The kernel of the vertex action is trivial, now using the proved
frame-specific five-anchor rigidity theorem from test18.
-/
theorem eq_one_of_vertexAction_eq_one
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct :
      vertexActionHom (Geo := Geo) T g = 1) :
    g = 1 := by

  have hA :
      g.1 T.A = T.A :=
    fixes_A_of_vertexAction_eq_one
      (Geo := Geo) T g hAct

  have hB :
      g.1 T.B = T.B :=
    fixes_B_of_vertexAction_eq_one
      (Geo := Geo) T g hAct

  have hC :
      g.1 T.C = T.C :=
    fixes_C_of_vertexAction_eq_one
      (Geo := Geo) T g hAct

  have hD :
      g.1 T.D = T.D :=
    fixes_D_of_vertexAction_eq_one
      (Geo := Geo) T g hAct

  have hE :
      g.1 T.E = T.E :=
    fixes_E_of_vertexAction_eq_one
      (Geo := Geo) T g hAct

  apply Subtype.ext

  change
    g.1 = Equiv.refl Geo.Point

  apply Equiv.ext
  intro X

  have hAX :
      Geo.Congruent
        T.A X
        T.A (g.1 X) := by
    have h :=
      generated_preserves_congruence
        (Geo := Geo)
        T g.1 g.2
        T.A X
    rw [hA] at h
    exact h

  have hBX :
      Geo.Congruent
        T.B X
        T.B (g.1 X) := by
    have h :=
      generated_preserves_congruence
        (Geo := Geo)
        T g.1 g.2
        T.B X
    rw [hB] at h
    exact h

  have hCX :
      Geo.Congruent
        T.C X
        T.C (g.1 X) := by
    have h :=
      generated_preserves_congruence
        (Geo := Geo)
        T g.1 g.2
        T.C X
    rw [hC] at h
    exact h

  have hDX :
      Geo.Congruent
        T.D X
        T.D (g.1 X) := by
    have h :=
      generated_preserves_congruence
        (Geo := Geo)
        T g.1 g.2
        T.D X
    rw [hD] at h
    exact h

  have hEX :
      Geo.Congruent
        T.E X
        T.E (g.1 X) := by
    have h :=
      generated_preserves_congruence
        (Geo := Geo)
        T g.1 g.2
        T.E X
    rw [hE] at h
    exact h

  have hUnique :
      X = g.1 X :=
    simplexFrame_five_anchor_distance_unique
      (Geo := Geo)
      T
      X (g.1 X)
      hAX hBX hCX hDX hEX

  exact hUnique.symm

/--
The canonical vertex action is faithful in the corrected E4 architecture.
-/
theorem vertexActionHom_injective
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Function.Injective
      (vertexActionHom (Geo := Geo) T) := by

  rw [← MonoidHom.ker_eq_bot_iff]

  apply le_antisymm

  · intro g hg

    have hAct :
        vertexActionHom (Geo := Geo) T g = 1 := by
      exact hg

    have hgOne :
        g = 1 :=
      eq_one_of_vertexAction_eq_one
        (Geo := Geo) T g hAct

    simp [hgOne]

  · exact bot_le

/--
The generated geometric Coxeter A4 reflection group is multiplicatively
isomorphic to the full symmetric group on five vertices, with no U5 boundary.
-/
noncomputable def generatedGroupMulEquivS5
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroup (Geo := Geo) T ≃*
      Equiv.Perm (Fin 5) :=
  MulEquiv.ofBijective
    (vertexActionHom (Geo := Geo) T)
    ⟨vertexActionHom_injective
        (Geo := Geo) T,
     vertexActionHom_surjective
        (Geo := Geo) T⟩

@[simp] theorem generatedGroupMulEquivS5_apply
    (T : CoxeterA4SmithSimplexFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    generatedGroupMulEquivS5
        (Geo := Geo) T g =
      vertexActionHom
        (Geo := Geo) T g := by
  rfl

@[simp] theorem generatedGroupMulEquivS5_r1
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroupMulEquivS5
        (Geo := Geo) T
        (generatedR1
          (Geo := Geo) T) =
      sigma1 := by
  rw [generatedGroupMulEquivS5_apply]
  exact
    vertexAction_generatedR1
      (Geo := Geo) T

@[simp] theorem generatedGroupMulEquivS5_r2
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroupMulEquivS5
        (Geo := Geo) T
        (generatedR2
          (Geo := Geo) T) =
      sigma2 := by
  rw [generatedGroupMulEquivS5_apply]
  exact
    vertexAction_generatedR2
      (Geo := Geo) T

@[simp] theorem generatedGroupMulEquivS5_r3
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroupMulEquivS5
        (Geo := Geo) T
        (generatedR3
          (Geo := Geo) T) =
      sigma3 := by
  rw [generatedGroupMulEquivS5_apply]
  exact
    vertexAction_generatedR3
      (Geo := Geo) T

@[simp] theorem generatedGroupMulEquivS5_r4
    (T : CoxeterA4SmithSimplexFrame Geo) :
    generatedGroupMulEquivS5
        (Geo := Geo) T
        (generatedR4
          (Geo := Geo) T) =
      sigma4 := by
  rw [generatedGroupMulEquivS5_apply]
  exact
    vertexAction_generatedR4
      (Geo := Geo) T

/--
Final corrected group-theoretic statement for a fixed A4 simplex frame.
-/
theorem generatedGroup_isomorphic_S5
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Nonempty
      (generatedGroup (Geo := Geo) T ≃*
        Equiv.Perm (Fin 5)) :=
  ⟨generatedGroupMulEquivS5
      (Geo := Geo) T⟩

end CoxeterA4S5

end Geometry


namespace Geometry
universe u
variable (Geo : Geometry.Geo)
namespace CoxeterA4S5

/-- The symmetric group on five vertices has 120 elements. -/
theorem S5_card :
    Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
  simpa [Nat.factorial] using
    (Fintype.card_perm (α := Fin 5))

end CoxeterA4S5
end Geometry

import CGJteamLab.Coxeter.CoxeterRelations3DExistence
import Mathlib.GroupTheory.Perm.ClosureSwap

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3: identification of the generated reflection group with S4

This production module completes the group-theoretic identification of
the three-dimensional Coxeter system A3 constructed geometrically in
`CoxeterRelations3D` and `CoxeterRelations3DExistence`.

For a tetrahedral Coxeter frame `T`, let

  G_T = <r1, r2, r3>

be the subgroup of all permutations of the ambient point space generated
by the three plane reflections.

The four tetrahedral vertices define an abstract four-element type.  The
geometric reflections induce the adjacent transpositions

  r1 |-> (A B),
  r2 |-> (B C),
  r3 |-> (C D).

The induced action homomorphism

  G_T -> Perm({A,B,C,D})

is proved:

* well-defined, by closure induction;
* faithful, by synthetic four-anchor rigidity in Hilbert 3-space;
* surjective, because the three adjacent transpositions generate the
  full symmetric group.

Hence the generated geometric reflection group is multiplicatively
equivalent to S4.
-/



/-! ## 1. Abstract tetrahedral vertices and generator action -/

/-!
# Coxeter A3 -> S4, test01

First algebraic layer for the final identification of the generated
reflection group with S4.

This file introduces:
* an abstract four-element vertex type;
* the map from abstract vertices to the tetrahedral frame;
* pairwise distinctness of the four geometric vertices;
* injectivity of the vertex map;
* the three adjacent transpositions on the abstract vertices;
* intertwining of those transpositions with r1, r2, r3.

No subgroup or group isomorphism is introduced yet.
-/


/--
The four abstract vertices of the A3 tetrahedral frame.
-/
inductive CoxeterA3Vertex where
  | vA
  | vB
  | vC
  | vD
  deriving DecidableEq


namespace CoxeterA3TetrahedralFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]


/--
The four vertices of a tetrahedral frame are pairwise distinct.

Only noncoplanarity is used.  The first three inequalities come from
noncollinearity of A,B,C.  The remaining ones are obtained by permuting
the four noncoplanar anchors.
-/
theorem vertices_pairwise_ne
    (T : CoxeterA3TetrahedralFrame Geo) :
    Ne T.A T.B /\
    Ne T.A T.C /\
    Ne T.A T.D /\
    Ne T.B T.C /\
    Ne T.B T.D /\
    Ne T.C T.D := by

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.C T.D
      T.noncoplanar

  have hAB : Ne T.A T.B :=
    hilbert_noncollinear_ne_first
      Geo T.A T.B T.C hABC

  have hAC : Ne T.A T.C :=
    hilbert_noncollinear_ne_first
      Geo T.A T.C T.B
      (by
        intro h
        exact
          hABC
            (PrimCollinearRotate
              Geo T.A T.C T.B h))

  have hBC : Ne T.B T.C :=
    hilbert_noncollinear_ne_first
      Geo T.B T.C T.A
      (by
        intro h
        exact
          hABC
            (PrimCollinearCycle
              Geo T.C T.A T.B
              (PrimCollinearCycle
                Geo T.B T.C T.A h)))

  have hNonABDC :
      Not
        (HilbertCoplanar4
          Geo T.A T.B T.D T.C) := by
    intro h
    rcases h with
      ⟨pi, hApi, hBpi, hDpi, hCpi⟩
    exact
      T.noncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hABD :
      Not (PrimCollinear Geo T.A T.B T.D) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.D T.C
      hNonABDC

  have hAD : Ne T.A T.D :=
    hilbert_noncollinear_ne_first
      Geo T.A T.D T.B
      (by
        intro h
        exact
          hABD
            (PrimCollinearRotate
              Geo T.A T.D T.B h))

  have hBD : Ne T.B T.D :=
    hilbert_noncollinear_ne_first
      Geo T.B T.D T.A
      (by
        intro h
        exact
          hABD
            (PrimCollinearCycle
              Geo T.D T.A T.B
              (PrimCollinearCycle
                Geo T.B T.D T.A h)))

  have hNonACDB :
      Not
        (HilbertCoplanar4
          Geo T.A T.C T.D T.B) := by
    intro h
    rcases h with
      ⟨pi, hApi, hCpi, hDpi, hBpi⟩
    exact
      T.noncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hACD :
      Not (PrimCollinear Geo T.A T.C T.D) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.C T.D T.B
      hNonACDB

  have hCD : Ne T.C T.D :=
    hilbert_noncollinear_ne_first
      Geo T.C T.D T.A
      (by
        intro h
        exact
          hACD
            (PrimCollinearCycle
              Geo T.D T.A T.C
              (PrimCollinearCycle
                Geo T.C T.D T.A h)))

  exact
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩


end CoxeterA3TetrahedralFrame


namespace CoxeterA3Vertex

/--
Interpret an abstract A3 vertex as a geometric vertex of the frame.
-/
def point
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (T : CoxeterA3TetrahedralFrame Geo) :
    CoxeterA3Vertex -> Geo.Point
  | .vA => T.A
  | .vB => T.B
  | .vC => T.C
  | .vD => T.D


@[simp]
theorem point_vA
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (T : CoxeterA3TetrahedralFrame Geo) :
    point (Geo := Geo) T .vA = T.A := by
  rfl


@[simp]
theorem point_vB
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (T : CoxeterA3TetrahedralFrame Geo) :
    point (Geo := Geo) T .vB = T.B := by
  rfl


@[simp]
theorem point_vC
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (T : CoxeterA3TetrahedralFrame Geo) :
    point (Geo := Geo) T .vC = T.C := by
  rfl


@[simp]
theorem point_vD
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (T : CoxeterA3TetrahedralFrame Geo) :
    point (Geo := Geo) T .vD = T.D := by
  rfl


/--
The geometric realization of the four abstract vertices is injective.
-/
theorem point_injective
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (T : CoxeterA3TetrahedralFrame Geo) :
    Function.Injective
      (point (Geo := Geo) T) := by

  rcases
      T.vertices_pairwise_ne
        (Geo := Geo) with
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩

  intro v w h

  cases v <;> cases w

  · rfl

  · exact
      (hAB
        (by simpa [point] using h)).elim

  · exact
      (hAC
        (by simpa [point] using h)).elim

  · exact
      (hAD
        (by simpa [point] using h)).elim

  · exact
      (hAB
        (by simpa [point] using h.symm)).elim

  · rfl

  · exact
      (hBC
        (by simpa [point] using h)).elim

  · exact
      (hBD
        (by simpa [point] using h)).elim

  · exact
      (hAC
        (by simpa [point] using h.symm)).elim

  · exact
      (hBC
        (by simpa [point] using h.symm)).elim

  · rfl

  · exact
      (hCD
        (by simpa [point] using h)).elim

  · exact
      (hAD
        (by simpa [point] using h.symm)).elim

  · exact
      (hBD
        (by simpa [point] using h.symm)).elim

  · exact
      (hCD
        (by simpa [point] using h.symm)).elim

  · rfl


/--
Abstract adjacent transposition corresponding to r1 = (A B).
-/
def sigma1 :
    Equiv CoxeterA3Vertex CoxeterA3Vertex where
  toFun
    | .vA => .vB
    | .vB => .vA
    | .vC => .vC
    | .vD => .vD
  invFun
    | .vA => .vB
    | .vB => .vA
    | .vC => .vC
    | .vD => .vD
  left_inv := by
    intro v
    cases v <;> rfl
  right_inv := by
    intro v
    cases v <;> rfl


/--
Abstract adjacent transposition corresponding to r2 = (B C).
-/
def sigma2 :
    Equiv CoxeterA3Vertex CoxeterA3Vertex where
  toFun
    | .vA => .vA
    | .vB => .vC
    | .vC => .vB
    | .vD => .vD
  invFun
    | .vA => .vA
    | .vB => .vC
    | .vC => .vB
    | .vD => .vD
  left_inv := by
    intro v
    cases v <;> rfl
  right_inv := by
    intro v
    cases v <;> rfl


/--
Abstract adjacent transposition corresponding to r3 = (C D).
-/
def sigma3 :
    Equiv CoxeterA3Vertex CoxeterA3Vertex where
  toFun
    | .vA => .vA
    | .vB => .vB
    | .vC => .vD
    | .vD => .vC
  invFun
    | .vA => .vA
    | .vB => .vB
    | .vC => .vD
    | .vD => .vC
  left_inv := by
    intro v
    cases v <;> rfl
  right_inv := by
    intro v
    cases v <;> rfl


/--
The geometric generator r1 intertwines with sigma1 on the four vertices.
-/
theorem r1_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T : CoxeterA3TetrahedralFrame Geo)
    (v : CoxeterA3Vertex) :
    CoxeterA3TetrahedralFrame.r1
        (Geo := Geo) T
        (point (Geo := Geo) T v) =
      point (Geo := Geo) T
        (sigma1 v) := by
  cases v

  · simpa [point, sigma1] using
      (CoxeterA3TetrahedralFrame.r1_A
        (Geo := Geo) T)

  · simpa [point, sigma1] using
      (CoxeterA3TetrahedralFrame.r1_B
        (Geo := Geo) T)

  · simpa [point, sigma1] using
      (CoxeterA3TetrahedralFrame.r1_C
        (Geo := Geo) T)

  · simpa [point, sigma1] using
      (CoxeterA3TetrahedralFrame.r1_D
        (Geo := Geo) T)


/--
The geometric generator r2 intertwines with sigma2 on the four vertices.
-/
theorem r2_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T : CoxeterA3TetrahedralFrame Geo)
    (v : CoxeterA3Vertex) :
    CoxeterA3TetrahedralFrame.r2
        (Geo := Geo) T
        (point (Geo := Geo) T v) =
      point (Geo := Geo) T
        (sigma2 v) := by
  cases v

  · simpa [point, sigma2] using
      (CoxeterA3TetrahedralFrame.r2_A
        (Geo := Geo) T)

  · simpa [point, sigma2] using
      (CoxeterA3TetrahedralFrame.r2_B
        (Geo := Geo) T)

  · simpa [point, sigma2] using
      (CoxeterA3TetrahedralFrame.r2_C
        (Geo := Geo) T)

  · simpa [point, sigma2] using
      (CoxeterA3TetrahedralFrame.r2_D
        (Geo := Geo) T)


/--
The geometric generator r3 intertwines with sigma3 on the four vertices.
-/
theorem r3_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T : CoxeterA3TetrahedralFrame Geo)
    (v : CoxeterA3Vertex) :
    CoxeterA3TetrahedralFrame.r3
        (Geo := Geo) T
        (point (Geo := Geo) T v) =
      point (Geo := Geo) T
        (sigma3 v) := by
  cases v

  · simpa [point, sigma3] using
      (CoxeterA3TetrahedralFrame.r3_A
        (Geo := Geo) T)

  · simpa [point, sigma3] using
      (CoxeterA3TetrahedralFrame.r3_B
        (Geo := Geo) T)

  · simpa [point, sigma3] using
      (CoxeterA3TetrahedralFrame.r3_C
        (Geo := Geo) T)

  · simpa [point, sigma3] using
      (CoxeterA3TetrahedralFrame.r3_D
        (Geo := Geo) T)


end CoxeterA3Vertex


/-! ## 2. Generated subgroup and canonical vertex action -/

namespace CoxeterA3Vertex

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]


/-!
# Coxeter A3 -> S4, test02

This file constructs the group generated by the three geometric
reflections and its canonical action on the four abstract tetrahedral
vertices.
-/


/--
The three geometric A3 reflection generators as a set of permutations
of the ambient point space.
-/
noncomputable def geometricGenerators
    (T : CoxeterA3TetrahedralFrame Geo) :
    Set (Equiv.Perm Geo.Point) :=
  {
    CoxeterA3TetrahedralFrame.r1
      (Geo := Geo) T,
    CoxeterA3TetrahedralFrame.r2
      (Geo := Geo) T,
    CoxeterA3TetrahedralFrame.r3
      (Geo := Geo) T
  }


/--
The subgroup of ambient point permutations generated by the three
tetrahedral reflections.
-/
noncomputable def generatedGroup
    (T : CoxeterA3TetrahedralFrame Geo) :
    Subgroup (Equiv.Perm Geo.Point) :=
  Subgroup.closure
    (geometricGenerators (Geo := Geo) T)


/--
A geometric permutation realizes an abstract permutation of the four
tetrahedral vertices when the two actions intertwine through `point`.
-/
def RealizesVertexPerm
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (sigma : Equiv.Perm CoxeterA3Vertex) :
    Prop :=
  forall v : CoxeterA3Vertex,
    g (point (Geo := Geo) T v) =
      point (Geo := Geo) T (sigma v)


/--
Every element of the subgroup generated by r1,r2,r3 realizes some
permutation of the four abstract vertices.

The proof is closure induction.  The generator cases are exactly
`r1_point`, `r2_point`, and `r3_point`.
-/
theorem generated_realizes_vertex_perm
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (hg :
      g ∈ generatedGroup (Geo := Geo) T) :
    exists sigma : Equiv.Perm CoxeterA3Vertex,
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

      rcases hx with hx | hx | hx

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

  | one =>

      refine
        ⟨1, ?_⟩

      intro v
      rfl

  | mul x y _hx _hy ihx ihy =>

      rcases ihx with
        ⟨sigma, hsigma⟩

      rcases ihy with
        ⟨tau, htau⟩

      refine
        ⟨sigma * tau, ?_⟩

      intro v

      simp only [Equiv.Perm.mul_apply]

      rw [htau v]
      rw [hsigma (tau v)]

  | inv x _hx ih =>

      rcases ih with
        ⟨sigma, hsigma⟩

      refine
        ⟨sigma⁻¹, ?_⟩

      intro v

      have h :
          x
            (point
              (Geo := Geo) T
              (sigma⁻¹ v)) =
            point
              (Geo := Geo) T v := by
        simpa using
          hsigma (sigma⁻¹ v)

      apply x.injective

      simpa using h.symm


end CoxeterA3Vertex

namespace CoxeterA3Vertex

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]


/--
A geometric permutation can realize at most one permutation of the
four abstract vertices.
-/
theorem realized_vertex_perm_unique
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : Equiv.Perm Geo.Point)
    (sigma tau : Equiv.Perm CoxeterA3Vertex)
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


end CoxeterA3Vertex

namespace CoxeterA3Vertex

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]


/--
The canonical permutation induced on the four vertices by an element of
the generated geometric subgroup.
-/
noncomputable def vertexPerm
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    Equiv.Perm CoxeterA3Vertex :=
  Classical.choose
    (generated_realizes_vertex_perm
      (Geo := Geo)
      T g.1 g.2)


/--
Specification of the canonical induced vertex permutation.
-/
theorem vertexPerm_spec
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    RealizesVertexPerm
      (Geo := Geo)
      T
      g.1
      (vertexPerm (Geo := Geo) T g) :=
  Classical.choose_spec
    (generated_realizes_vertex_perm
      (Geo := Geo)
      T g.1 g.2)


/--
The induced vertex permutation is multiplicative.
-/
theorem vertexPerm_mul
    (T : CoxeterA3TetrahedralFrame Geo)
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
      vertexPerm_spec
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
      vertexPerm_spec
        (Geo := Geo) T h v
    ]

    rw [
      vertexPerm_spec
        (Geo := Geo) T g
          (vertexPerm
            (Geo := Geo) T h v)
    ]


/--
The identity geometric permutation induces the identity vertex
permutation.
-/
theorem vertexPerm_one
    (T : CoxeterA3TetrahedralFrame Geo) :
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
      vertexPerm_spec
        (Geo := Geo)
        T
        (1 : generatedGroup
          (Geo := Geo) T)

  · intro v
    rfl


/--
Canonical action homomorphism of the generated geometric reflection
group on the four tetrahedral vertices.
-/
noncomputable def vertexActionHom
    (T : CoxeterA3TetrahedralFrame Geo) :
    MonoidHom
      (generatedGroup (Geo := Geo) T)
      (Equiv.Perm CoxeterA3Vertex) where

  toFun :=
    vertexPerm (Geo := Geo) T

  map_one' :=
    vertexPerm_one
      (Geo := Geo) T

  map_mul' :=
    vertexPerm_mul
      (Geo := Geo) T


@[simp]
theorem vertexActionHom_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    vertexActionHom (Geo := Geo) T g =
      vertexPerm (Geo := Geo) T g := by
  rfl


end CoxeterA3Vertex


/-! ## 3. Faithfulness from synthetic four-point rigidity -/

namespace CoxeterA3Vertex

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/-!
# Coxeter A3 -> S4, test03

Faithfulness of the action on the four tetrahedral vertices.

The strategy is purely synthetic:

1. every element of the generated reflection subgroup preserves ambient
   segment congruence;
2. therefore every such element is a `HilbertSpaceIsometry3D`;
3. an element acting trivially on the four vertices fixes four
   noncoplanar points;
4. four-point rigidity forces that element to be the identity.

This proves injectivity of `vertexActionHom`.
-/


/--
Every element of the geometric subgroup generated by r1,r2,r3
preserves ambient segment congruence.
-/
theorem generated_preserves_congruence
    (T : CoxeterA3TetrahedralFrame Geo)
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

      rcases hx with hx | hx | hx

      · subst x
        intro P Q
        exact
          planeReflect_preserves_congruence
            (Geo := Geo)
            T.pi1 P Q

      · subst x
        intro P Q
        exact
          planeReflect_preserves_congruence
            (Geo := Geo)
            T.pi2 P Q

      · subst x
        intro P Q
        exact
          planeReflect_preserves_congruence
            (Geo := Geo)
            T.pi3 P Q

  | one =>

      intro P Q

      simpa using
        hilbert_space_congruent_reflexive_all
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
        hilbert_space_congruent_transitivity_all
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

      have hBackward :
          Geo.Congruent
            P Q
            (x⁻¹ P)
            (x⁻¹ Q) :=
        hilbert_space_congruent_symmetry_all
          (Geo := Geo)
          (x⁻¹ P)
          (x⁻¹ Q)
          P Q
          hForward

      exact hBackward


/--
Every element of the generated geometric subgroup can be packaged as
a synthetic 3D isometry.
-/
noncomputable def generatedIsometry
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    HilbertSpaceIsometry3D Geo where

  toEquiv :=
    g.1

  preserves_congruence := by
    intro P Q
    exact
      generated_preserves_congruence
        (Geo := Geo)
        T g.1 g.2
        P Q


@[simp]
theorem generatedIsometry_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    (generatedIsometry
      (Geo := Geo) T g).toEquiv =
      g.1 := by
  rfl


/--
If the induced action on the four abstract vertices is trivial, then
the geometric permutation fixes A.
-/
theorem fixes_A_of_vertexAction_eq_one
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct :
      vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.A = T.A := by

  have hSpec :=
    vertexPerm_spec
      (Geo := Geo) T g .vA

  have hVertex :
      vertexPerm (Geo := Geo) T g = 1 := by
    simpa [vertexActionHom_apply] using hAct

  rw [hVertex] at hSpec

  simpa [point] using hSpec


/--
If the induced action on the four abstract vertices is trivial, then
the geometric permutation fixes B.
-/
theorem fixes_B_of_vertexAction_eq_one
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct :
      vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.B = T.B := by

  have hSpec :=
    vertexPerm_spec
      (Geo := Geo) T g .vB

  have hVertex :
      vertexPerm (Geo := Geo) T g = 1 := by
    simpa [vertexActionHom_apply] using hAct

  rw [hVertex] at hSpec

  simpa [point] using hSpec


/--
If the induced action on the four abstract vertices is trivial, then
the geometric permutation fixes C.
-/
theorem fixes_C_of_vertexAction_eq_one
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct :
      vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.C = T.C := by

  have hSpec :=
    vertexPerm_spec
      (Geo := Geo) T g .vC

  have hVertex :
      vertexPerm (Geo := Geo) T g = 1 := by
    simpa [vertexActionHom_apply] using hAct

  rw [hVertex] at hSpec

  simpa [point] using hSpec


/--
If the induced action on the four abstract vertices is trivial, then
the geometric permutation fixes D.
-/
theorem fixes_D_of_vertexAction_eq_one
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T)
    (hAct :
      vertexActionHom (Geo := Geo) T g = 1) :
    g.1 T.D = T.D := by

  have hSpec :=
    vertexPerm_spec
      (Geo := Geo) T g .vD

  have hVertex :
      vertexPerm (Geo := Geo) T g = 1 := by
    simpa [vertexActionHom_apply] using hAct

  rw [hVertex] at hSpec

  simpa [point] using hSpec


/--
The kernel of the vertex action is trivial.

This is the exact point where synthetic four-point rigidity enters.
-/
theorem eq_one_of_vertexAction_eq_one
    (T : CoxeterA3TetrahedralFrame Geo)
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

  have hRigid :
      (generatedIsometry
        (Geo := Geo) T g).toEquiv =
        Equiv.refl Geo.Point :=
    HilbertSpaceIsometry3D.eq_refl_of_fix_noncoplanar4
      (Geo := Geo)
      (generatedIsometry
        (Geo := Geo) T g)
      T.A T.B T.C T.D
      T.noncoplanar
      hA hB hC hD

  apply Subtype.ext

  change
    g.1 = Equiv.refl Geo.Point

  exact hRigid


/--
The canonical action of the generated reflection group on the four
tetrahedral vertices is faithful.
-/
theorem vertexActionHom_injective
    (T : CoxeterA3TetrahedralFrame Geo) :
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


end CoxeterA3Vertex


/-! ## 4. Surjectivity onto the full symmetric group -/

namespace CoxeterA3Vertex

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/-!
# Coxeter A3 -> S4, test04

Surjectivity of the canonical vertex action.

The abstract generators sigma1, sigma2, sigma3 are the adjacent
transpositions

  (A B), (B C), (C D).

They generate the full symmetric group on the four vertices.  We use
the general mathlib theorem that a pretransitive permutation group
generated by transpositions is the whole symmetric group.

Then we show that sigma1, sigma2, sigma3 are all in the range of the
geometric vertex-action homomorphism.
-/


/--
Explicit finite structure on the four abstract vertices.
-/
instance coxeterA3VertexFintype :
    Fintype CoxeterA3Vertex where
  elems :=
    {
      CoxeterA3Vertex.vA,
      CoxeterA3Vertex.vB,
      CoxeterA3Vertex.vC,
      CoxeterA3Vertex.vD
    }
  complete := by
    intro v
    cases v <;> simp


/--
The three abstract adjacent transpositions.
-/
def abstractGenerators :
    Set (Equiv.Perm CoxeterA3Vertex) :=
  {sigma1, sigma2, sigma3}


/--
sigma1 is literally the transposition (A B).
-/
theorem sigma1_eq_swap :
    sigma1 =
      Equiv.swap
        CoxeterA3Vertex.vA
        CoxeterA3Vertex.vB := by

  apply Equiv.ext
  intro v
  cases v <;>
    simp [sigma1, Equiv.swap_apply_def]


/--
sigma2 is literally the transposition (B C).
-/
theorem sigma2_eq_swap :
    sigma2 =
      Equiv.swap
        CoxeterA3Vertex.vB
        CoxeterA3Vertex.vC := by

  apply Equiv.ext
  intro v
  cases v <;>
    simp [sigma2, Equiv.swap_apply_def]


/--
sigma3 is literally the transposition (C D).
-/
theorem sigma3_eq_swap :
    sigma3 =
      Equiv.swap
        CoxeterA3Vertex.vC
        CoxeterA3Vertex.vD := by

  apply Equiv.ext
  intro v
  cases v <;>
    simp [sigma3, Equiv.swap_apply_def]


theorem sigma1_isSwap :
    Equiv.Perm.IsSwap sigma1 := by

  exact
    ⟨CoxeterA3Vertex.vA,
     CoxeterA3Vertex.vB,
     by decide,
     sigma1_eq_swap⟩


theorem sigma2_isSwap :
    Equiv.Perm.IsSwap sigma2 := by

  exact
    ⟨CoxeterA3Vertex.vB,
     CoxeterA3Vertex.vC,
     by decide,
     sigma2_eq_swap⟩


theorem sigma3_isSwap :
    Equiv.Perm.IsSwap sigma3 := by

  exact
    ⟨CoxeterA3Vertex.vC,
     CoxeterA3Vertex.vD,
     by decide,
     sigma3_eq_swap⟩


/--
Every abstract generator is a transposition.
-/
theorem abstractGenerators_isSwap
    (sigma : Equiv.Perm CoxeterA3Vertex)
    (hsigma :
      sigma ∈ abstractGenerators) :
    Equiv.Perm.IsSwap sigma := by

  simp only
    [abstractGenerators,
     Set.mem_insert_iff,
     Set.mem_singleton_iff] at hsigma

  rcases hsigma with h | h | h

  · subst sigma
    exact sigma1_isSwap

  · subst sigma
    exact sigma2_isSwap

  · subst sigma
    exact sigma3_isSwap


/--
The subgroup generated by sigma1,sigma2,sigma3 acts transitively on
the four abstract vertices.
-/
theorem abstractGenerators_closure_isPretransitive :
    let K :=
      Subgroup.closure abstractGenerators
    MulAction.IsPretransitive
      K CoxeterA3Vertex := by

  let K :
      Subgroup
        (Equiv.Perm CoxeterA3Vertex) :=
    Subgroup.closure abstractGenerators

  let k1 : K :=
    ⟨sigma1,
     Subgroup.subset_closure
       (by
         simp [abstractGenerators])⟩

  let k2 : K :=
    ⟨sigma2,
     Subgroup.subset_closure
       (by
         simp [abstractGenerators])⟩

  let k3 : K :=
    ⟨sigma3,
     Subgroup.subset_closure
       (by
         simp [abstractGenerators])⟩

  let reach :
      CoxeterA3Vertex -> K
    | .vA => 1
    | .vB => k1
    | .vC => k2 * k1
    | .vD => k3 * k2 * k1

  have hreach :
      forall v : CoxeterA3Vertex,
        (reach v).1 CoxeterA3Vertex.vA = v := by

    intro v
    cases v <;>
      simp
        [reach, k1, k2, k3,
         sigma1, sigma2, sigma3,
         Equiv.Perm.mul_apply]

  have hreach_smul :
      forall v : CoxeterA3Vertex,
        reach v • CoxeterA3Vertex.vA = v := by

    intro v

    change
      (reach v).1 CoxeterA3Vertex.vA = v

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
                  (reach x • CoxeterA3Vertex.vA)) := by
                rw [hreach_smul x]

          _ =
              reach y • CoxeterA3Vertex.vA := by
                rw [inv_smul_smul]

          _ = y :=
                hreach_smul y
    }


/--
The first geometric generator as an element of the generated subgroup.
-/
noncomputable def generatedR1
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  ⟨CoxeterA3TetrahedralFrame.r1
      (Geo := Geo) T,
   Subgroup.subset_closure
     (by
       simp [geometricGenerators])⟩


/--
The second geometric generator as an element of the generated subgroup.
-/
noncomputable def generatedR2
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  ⟨CoxeterA3TetrahedralFrame.r2
      (Geo := Geo) T,
   Subgroup.subset_closure
     (by
       simp [geometricGenerators])⟩


/--
The third geometric generator as an element of the generated subgroup.
-/
noncomputable def generatedR3
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroup (Geo := Geo) T :=
  ⟨CoxeterA3TetrahedralFrame.r3
      (Geo := Geo) T,
   Subgroup.subset_closure
     (by
       simp [geometricGenerators])⟩


/--
The induced action of the first geometric generator is sigma1.
-/
theorem vertexAction_generatedR1
    (T : CoxeterA3TetrahedralFrame Geo) :
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
      (CoxeterA3TetrahedralFrame.r1
        (Geo := Geo) T)

  · exact
      vertexPerm_spec
        (Geo := Geo)
        T
        (generatedR1
          (Geo := Geo) T)

  · exact
      r1_point
        (Geo := Geo) T


/--
The induced action of the second geometric generator is sigma2.
-/
theorem vertexAction_generatedR2
    (T : CoxeterA3TetrahedralFrame Geo) :
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
      (CoxeterA3TetrahedralFrame.r2
        (Geo := Geo) T)

  · exact
      vertexPerm_spec
        (Geo := Geo)
        T
        (generatedR2
          (Geo := Geo) T)

  · exact
      r2_point
        (Geo := Geo) T


/--
The induced action of the third geometric generator is sigma3.
-/
theorem vertexAction_generatedR3
    (T : CoxeterA3TetrahedralFrame Geo) :
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
      (CoxeterA3TetrahedralFrame.r3
        (Geo := Geo) T)

  · exact
      vertexPerm_spec
        (Geo := Geo)
        T
        (generatedR3
          (Geo := Geo) T)

  · exact
      r3_point
        (Geo := Geo) T


/--
Every abstract adjacent-transposition generator lies in the range of
the geometric vertex-action homomorphism.
-/
theorem abstractGenerators_subset_vertexAction_range
    (T : CoxeterA3TetrahedralFrame Geo) :
    abstractGenerators ⊆
      (vertexActionHom
        (Geo := Geo) T).range := by

  intro sigma hsigma

  simp only
    [abstractGenerators,
     Set.mem_insert_iff,
     Set.mem_singleton_iff] at hsigma

  rcases hsigma with h | h | h

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


/--
The canonical vertex action is surjective onto the full symmetric
group on the four abstract vertices.
-/
theorem vertexActionHom_surjective
    (T : CoxeterA3TetrahedralFrame Geo) :
    Function.Surjective
      (vertexActionHom (Geo := Geo) T) := by

  let hPretransitive :
      MulAction.IsPretransitive
        (Subgroup.closure abstractGenerators)
        CoxeterA3Vertex :=
    abstractGenerators_closure_isPretransitive

  have hAll :=
    closure_of_isSwap_of_isPretransitive
      abstractGenerators_isSwap

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


end CoxeterA3Vertex


/-! ## 5. Final multiplicative equivalence with S4 -/

namespace CoxeterA3Vertex

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/-!
# Coxeter A3 -> S4, test05

Final identification of the geometric reflection group generated by
r1,r2,r3 with the full symmetric group on the four tetrahedral
vertices.

The canonical vertex action

  vertexActionHom :
    generatedGroup T ->* Equiv.Perm CoxeterA3Vertex

was proved injective in test03 and surjective in test04.
Therefore it upgrades directly to a multiplicative equivalence.
-/


/--
The geometric Coxeter A3 reflection group generated by r1,r2,r3 is
isomorphic to the full symmetric group on the four tetrahedral
vertices.
-/
noncomputable def generatedGroupMulEquivS4
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroup (Geo := Geo) T ≃*
      Equiv.Perm CoxeterA3Vertex :=
  MulEquiv.ofBijective
    (vertexActionHom (Geo := Geo) T)
    ⟨vertexActionHom_injective
        (Geo := Geo) T,
     vertexActionHom_surjective
        (Geo := Geo) T⟩


@[simp]
theorem generatedGroupMulEquivS4_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (g : generatedGroup (Geo := Geo) T) :
    generatedGroupMulEquivS4
        (Geo := Geo) T g =
      vertexActionHom
        (Geo := Geo) T g := by
  rfl


/--
Under the final S4 identification, the first geometric reflection is
the adjacent transposition sigma1 = (A B).
-/
@[simp]
theorem generatedGroupMulEquivS4_r1
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroupMulEquivS4
        (Geo := Geo) T
        (generatedR1
          (Geo := Geo) T) =
      sigma1 := by

  rw [generatedGroupMulEquivS4_apply]

  exact
    vertexAction_generatedR1
      (Geo := Geo) T


/--
Under the final S4 identification, the second geometric reflection is
the adjacent transposition sigma2 = (B C).
-/
@[simp]
theorem generatedGroupMulEquivS4_r2
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroupMulEquivS4
        (Geo := Geo) T
        (generatedR2
          (Geo := Geo) T) =
      sigma2 := by

  rw [generatedGroupMulEquivS4_apply]

  exact
    vertexAction_generatedR2
      (Geo := Geo) T


/--
Under the final S4 identification, the third geometric reflection is
the adjacent transposition sigma3 = (C D).
-/
@[simp]
theorem generatedGroupMulEquivS4_r3
    (T : CoxeterA3TetrahedralFrame Geo) :
    generatedGroupMulEquivS4
        (Geo := Geo) T
        (generatedR3
          (Geo := Geo) T) =
      sigma3 := by

  rw [generatedGroupMulEquivS4_apply]

  exact
    vertexAction_generatedR3
      (Geo := Geo) T


/--
Final group-theoretic statement for a fixed tetrahedral Coxeter A3
frame: the subgroup generated by the three geometric plane reflections
is multiplicatively equivalent to S4.
-/
theorem generatedGroup_isomorphic_S4
    (T : CoxeterA3TetrahedralFrame Geo) :
    Nonempty
      (generatedGroup (Geo := Geo) T ≃*
        Equiv.Perm CoxeterA3Vertex) :=
  ⟨generatedGroupMulEquivS4
      (Geo := Geo) T⟩


end CoxeterA3Vertex

end Geometry

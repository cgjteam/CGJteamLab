import CGJteamLab.Coxeter.PlaneReflectionIsometry
import CGJteamLab.Proposition11_5

/-!
# Synthetic Coxeter relations of type A3 in Hilbert 3-space

Production merge of the verified 3D Coxeter development.

The construction is entirely synthetic:
* reflections in ambient planes;
* induced planar slices;
* Hilbert congruence and order;
* Euclid Book XI perpendicularity;
* four-point noncoplanar rigidity.

No coordinates, vectors, scalar products, matrices, or trigonometric
representations are used.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter relations in 3D: algebraic isometry layer

This file begins the genuinely spatial Coxeter layer.

The mirror objects are ambient planes and the generators are the
canonical plane reflections already constructed in `PlaneReflection.lean`.

No coordinates, vectors, scalar products, matrices, or numerical angles
are introduced.
-/

/--
Ambient segment congruence is reflexive for every segment, including a
degenerate one.

Unlike the earlier nondegenerate helper, this proof does not use the
endpoints of the segment as the target ray for Hilbert III.1.  It first
chooses an arbitrary nondegenerate ambient ray and copies the prescribed
segment onto it.  Hilbert III.2 then gives reflexivity.
-/
theorem hilbert_space_congruent_reflexive_all
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B : Geo.Point) :
    Geo.Congruent A B A B := by

  rcases
      HilbertPlaneIncidence.two_points_on_line
        (Geo := Geo) with
    ⟨l, O, R, hOR, _hOl, _hRl⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        A B O R hOR with
    ⟨X, _hRay, hOX_AB⟩

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      O X
      A B
      A B
      hOX_AB
      hOX_AB


/--
Ambient symmetry of segment congruence without a nondegeneracy
assumption on the source segment.
-/
theorem hilbert_space_congruent_symmetry_all
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by

  have hRefl :
      Geo.Congruent A B A B :=
    hilbert_space_congruent_reflexive_all
      (Geo := Geo) A B

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A B
      C D
      A B
      h
      hRefl


/--
Ambient transitivity of segment congruence for arbitrary, possibly
degenerate, segments.
-/
theorem hilbert_space_congruent_transitivity_all
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D E F : Geo.Point)
    (h1 : Geo.Congruent A B C D)
    (h2 : Geo.Congruent C D E F) :
    Geo.Congruent A B E F := by

  have h1sym :
      Geo.Congruent C D A B :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      A B C D h1

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      C D
      A B
      E F
      h1sym
      h2


/--
A synthetic ambient isometry of Hilbert 3-space.

For the Coxeter development we retain exactly the data currently needed:
a permutation of points preserving segment congruence.
-/
structure HilbertSpaceIsometry3D
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)] where

  toEquiv : Equiv Geo.Point Geo.Point

  preserves_congruence :
    forall A B : Geo.Point,
      Geo.Congruent
        A B
        (toEquiv A)
        (toEquiv B)


namespace HilbertSpaceIsometry3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]


/--
Composition of synthetic 3D isometries.
-/
def trans
    (f g : HilbertSpaceIsometry3D Geo) :
    HilbertSpaceIsometry3D Geo where

  toEquiv :=
    f.toEquiv.trans g.toEquiv

  preserves_congruence := by
    intro A B

    have h1 :
        Geo.Congruent
          A B
          (f.toEquiv A)
          (f.toEquiv B) :=
      f.preserves_congruence A B

    have h2 :
        Geo.Congruent
          (f.toEquiv A)
          (f.toEquiv B)
          (g.toEquiv (f.toEquiv A))
          (g.toEquiv (f.toEquiv B)) :=
      g.preserves_congruence
        (f.toEquiv A)
        (f.toEquiv B)

    exact
      hilbert_space_congruent_transitivity_all
        (Geo := Geo)
        A B
        (f.toEquiv A)
        (f.toEquiv B)
        (g.toEquiv (f.toEquiv A))
        (g.toEquiv (f.toEquiv B))
        h1 h2


@[simp]
theorem trans_apply
    (f g : HilbertSpaceIsometry3D Geo)
    (P : Geo.Point) :
    (trans (Geo := Geo) f g).toEquiv P =
      g.toEquiv (f.toEquiv P) := by
  rfl


end HilbertSpaceIsometry3D


/--
Reflection in an ambient plane, packaged as a synthetic 3D isometry.
-/
noncomputable def planeReflectionIsometry3D
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane) :
    HilbertSpaceIsometry3D Geo where

  toEquiv :=
    planeReflectEquiv Geo pi

  preserves_congruence := by
    intro A B
    exact
      planeReflect_preserves_congruence
        (Geo := Geo)
        pi A B


@[simp]
theorem planeReflectionIsometry3D_apply
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point) :
    (planeReflectionIsometry3D
      (Geo := Geo) pi).toEquiv P =
      planeReflect Geo pi P := by
  rfl


/--
First Coxeter relation in 3D, in literal transformation form:

    r_pi^2 = 1.
-/
theorem planeReflectionEquiv_sq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane) :
    (planeReflectEquiv Geo pi).trans
        (planeReflectEquiv Geo pi) =
      Equiv.refl Geo.Point := by

  apply Equiv.ext
  intro P

  exact
    planeReflect_involutive
      (Geo := Geo)
      pi P


/--
The same involution relation at the packaged 3D-isometry level,
expressed on the underlying point equivalence.
-/
theorem planeReflectionIsometry3D_sq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane) :
    (HilbertSpaceIsometry3D.trans
      (Geo := Geo)
      (planeReflectionIsometry3D
        (Geo := Geo) pi)
      (planeReflectionIsometry3D
        (Geo := Geo) pi)).toEquiv =
      Equiv.refl Geo.Point := by

  exact
    planeReflectionEquiv_sq
      (Geo := Geo)
      pi


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 in 3D: tetrahedral mirror frame

The structure below contains only geometric mirror data.

For the three mirrors:
* pi1 is the perpendicular-bisector plane of AB and contains C,D;
* pi2 is the perpendicular-bisector plane of BC and contains A,D;
* pi3 is the perpendicular-bisector plane of CD and contains A,B.

No permutation action is assumed.  The adjacent transposition action is
derived from `planeReflect_eq_of_perpendicular_midpoint`,
`planeReflect_swap_of_perpendicular_midpoint`, and fixed-point theorems.
-/

/--
Synthetic tetrahedral mirror frame for Coxeter type A3.
-/
structure CoxeterA3TetrahedralFrame
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] where

  A : Geo.Point
  B : Geo.Point
  C : Geo.Point
  D : Geo.Point

  noncoplanar :
    Not (HilbertCoplanar4 Geo A B C D)

  pi1 : S.Plane
  F1 : Geo.Point

  A_off_pi1 :
    Not (S.OnPlane A pi1)

  AB_perp_pi1 :
    PerpendicularToPlaneThrough Geo pi1 F1 A

  F1_mid_AB :
    HilbertIsMidpoint Geo F1 A B

  C_on_pi1 :
    S.OnPlane C pi1

  D_on_pi1 :
    S.OnPlane D pi1

  pi2 : S.Plane
  F2 : Geo.Point

  B_off_pi2 :
    Not (S.OnPlane B pi2)

  BC_perp_pi2 :
    PerpendicularToPlaneThrough Geo pi2 F2 B

  F2_mid_BC :
    HilbertIsMidpoint Geo F2 B C

  A_on_pi2 :
    S.OnPlane A pi2

  D_on_pi2 :
    S.OnPlane D pi2

  pi3 : S.Plane
  F3 : Geo.Point

  C_off_pi3 :
    Not (S.OnPlane C pi3)

  CD_perp_pi3 :
    PerpendicularToPlaneThrough Geo pi3 F3 C

  F3_mid_CD :
    HilbertIsMidpoint Geo F3 C D

  A_on_pi3 :
    S.OnPlane A pi3

  B_on_pi3 :
    S.OnPlane B pi3


namespace CoxeterA3TetrahedralFrame

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


/--
First A3 generator: reflection in the perpendicular-bisector plane of AB.
-/
noncomputable def r1
    (T : CoxeterA3TetrahedralFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  planeReflectEquiv Geo T.pi1


/--
Second A3 generator: reflection in the perpendicular-bisector plane of BC.
-/
noncomputable def r2
    (T : CoxeterA3TetrahedralFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  planeReflectEquiv Geo T.pi2


/--
Third A3 generator: reflection in the perpendicular-bisector plane of CD.
-/
noncomputable def r3
    (T : CoxeterA3TetrahedralFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  planeReflectEquiv Geo T.pi3


@[simp]
theorem r1_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (P : Geo.Point) :
    r1 (Geo := Geo) T P = planeReflect Geo T.pi1 P := by
  rfl


@[simp]
theorem r2_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (P : Geo.Point) :
    r2 (Geo := Geo) T P = planeReflect Geo T.pi2 P := by
  rfl


@[simp]
theorem r3_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (P : Geo.Point) :
    r3 (Geo := Geo) T P = planeReflect Geo T.pi3 P := by
  rfl


/-!
## Generator r1 = transposition (A B)
-/

@[simp]
theorem r1_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r1 (Geo := Geo) T T.A = T.B := by

  exact
    planeReflect_eq_of_perpendicular_midpoint
      (Geo := Geo)
      T.pi1
      T.A T.F1 T.B
      T.A_off_pi1
      T.AB_perp_pi1
      T.F1_mid_AB


@[simp]
theorem r1_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r1 (Geo := Geo) T T.B = T.A := by

  exact
    planeReflect_swap_of_perpendicular_midpoint
      (Geo := Geo)
      T.pi1
      T.A T.F1 T.B
      T.A_off_pi1
      T.AB_perp_pi1
      T.F1_mid_AB


@[simp]
theorem r1_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r1 (Geo := Geo) T T.C = T.C := by

  exact
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi1 T.C
      T.C_on_pi1


@[simp]
theorem r1_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r1 (Geo := Geo) T T.D = T.D := by

  exact
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi1 T.D
      T.D_on_pi1


/-!
## Generator r2 = transposition (B C)
-/

@[simp]
theorem r2_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r2 (Geo := Geo) T T.A = T.A := by

  exact
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi2 T.A
      T.A_on_pi2


@[simp]
theorem r2_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r2 (Geo := Geo) T T.B = T.C := by

  exact
    planeReflect_eq_of_perpendicular_midpoint
      (Geo := Geo)
      T.pi2
      T.B T.F2 T.C
      T.B_off_pi2
      T.BC_perp_pi2
      T.F2_mid_BC


@[simp]
theorem r2_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r2 (Geo := Geo) T T.C = T.B := by

  exact
    planeReflect_swap_of_perpendicular_midpoint
      (Geo := Geo)
      T.pi2
      T.B T.F2 T.C
      T.B_off_pi2
      T.BC_perp_pi2
      T.F2_mid_BC


@[simp]
theorem r2_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r2 (Geo := Geo) T T.D = T.D := by

  exact
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi2 T.D
      T.D_on_pi2


/-!
## Generator r3 = transposition (C D)
-/

@[simp]
theorem r3_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r3 (Geo := Geo) T T.A = T.A := by

  exact
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi3 T.A
      T.A_on_pi3


@[simp]
theorem r3_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r3 (Geo := Geo) T T.B = T.B := by

  exact
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi3 T.B
      T.B_on_pi3


@[simp]
theorem r3_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r3 (Geo := Geo) T T.C = T.D := by

  exact
    planeReflect_eq_of_perpendicular_midpoint
      (Geo := Geo)
      T.pi3
      T.C T.F3 T.D
      T.C_off_pi3
      T.CD_perp_pi3
      T.F3_mid_CD


@[simp]
theorem r3_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r3 (Geo := Geo) T T.D = T.C := by

  exact
    planeReflect_swap_of_perpendicular_midpoint
      (Geo := Geo)
      T.pi3
      T.C T.F3 T.D
      T.C_off_pi3
      T.CD_perp_pi3
      T.F3_mid_CD


/-!
## Involution relations
-/

theorem r1_sq
    (T : CoxeterA3TetrahedralFrame Geo) :
    (r1 (Geo := Geo) T).trans (r1 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by

  exact
    planeReflectionEquiv_sq
      (Geo := Geo)
      T.pi1


theorem r2_sq
    (T : CoxeterA3TetrahedralFrame Geo) :
    (r2 (Geo := Geo) T).trans (r2 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by

  exact
    planeReflectionEquiv_sq
      (Geo := Geo)
      T.pi2


theorem r3_sq
    (T : CoxeterA3TetrahedralFrame Geo) :
    (r3 (Geo := Geo) T).trans (r3 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by

  exact
    planeReflectionEquiv_sq
      (Geo := Geo)
      T.pi3


/-!
## Adjacent products on the tetrahedral frame

`Equiv.trans` applies the left equivalence first and the right equivalence
second.  Thus `r12 = r1.trans r2` acts on A,B,C as the 3-cycle

    A -> C -> B -> A

and fixes D.
-/

noncomputable def r12
    (T : CoxeterA3TetrahedralFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  (r1 (Geo := Geo) T).trans (r2 (Geo := Geo) T)


noncomputable def r23
    (T : CoxeterA3TetrahedralFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  (r2 (Geo := Geo) T).trans (r3 (Geo := Geo) T)


noncomputable def r13
    (T : CoxeterA3TetrahedralFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  (r1 (Geo := Geo) T).trans (r3 (Geo := Geo) T)


@[simp]
theorem r12_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T T.A = T.C := by
  change
    r2 (Geo := Geo) T
      (r1 (Geo := Geo) T T.A) = T.C
  rw [r1_A, r2_B]


@[simp]
theorem r12_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T T.B = T.A := by
  change
    r2 (Geo := Geo) T
      (r1 (Geo := Geo) T T.B) = T.A
  rw [r1_B, r2_A]


@[simp]
theorem r12_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T T.C = T.B := by
  change
    r2 (Geo := Geo) T
      (r1 (Geo := Geo) T T.C) = T.B
  rw [r1_C, r2_C]


@[simp]
theorem r12_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T T.D = T.D := by
  change
    r2 (Geo := Geo) T
      (r1 (Geo := Geo) T T.D) = T.D
  rw [r1_D, r2_D]


@[simp]
theorem r23_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T T.A = T.A := by
  change
    r3 (Geo := Geo) T
      (r2 (Geo := Geo) T T.A) = T.A
  rw [r2_A, r3_A]


@[simp]
theorem r23_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T T.B = T.D := by
  change
    r3 (Geo := Geo) T
      (r2 (Geo := Geo) T T.B) = T.D
  rw [r2_B, r3_C]


@[simp]
theorem r23_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T T.C = T.B := by
  change
    r3 (Geo := Geo) T
      (r2 (Geo := Geo) T T.C) = T.B
  rw [r2_C, r3_B]


@[simp]
theorem r23_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T T.D = T.C := by
  change
    r3 (Geo := Geo) T
      (r2 (Geo := Geo) T T.D) = T.C
  rw [r2_D, r3_D]


@[simp]
theorem r13_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T T.A = T.B := by
  change
    r3 (Geo := Geo) T
      (r1 (Geo := Geo) T T.A) = T.B
  rw [r1_A, r3_B]


@[simp]
theorem r13_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T T.B = T.A := by
  change
    r3 (Geo := Geo) T
      (r1 (Geo := Geo) T T.B) = T.A
  rw [r1_B, r3_A]


@[simp]
theorem r13_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T T.C = T.D := by
  change
    r3 (Geo := Geo) T
      (r1 (Geo := Geo) T T.C) = T.D
  rw [r1_C, r3_C]


@[simp]
theorem r13_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T T.D = T.C := by
  change
    r3 (Geo := Geo) T
      (r1 (Geo := Geo) T T.D) = T.C
  rw [r1_D, r3_D]


/-!
## Coxeter word relations on the four tetrahedral vertices
-/

theorem r12_cube_on_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T (r12 (Geo := Geo) T (r12 (Geo := Geo) T T.A)) = T.A := by
  simp


theorem r12_cube_on_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T (r12 (Geo := Geo) T (r12 (Geo := Geo) T T.B)) = T.B := by
  simp


theorem r12_cube_on_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T (r12 (Geo := Geo) T (r12 (Geo := Geo) T T.C)) = T.C := by
  simp


theorem r12_cube_on_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r12 (Geo := Geo) T (r12 (Geo := Geo) T (r12 (Geo := Geo) T T.D)) = T.D := by
  simp


theorem r23_cube_on_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T (r23 (Geo := Geo) T (r23 (Geo := Geo) T T.A)) = T.A := by
  simp


theorem r23_cube_on_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T (r23 (Geo := Geo) T (r23 (Geo := Geo) T T.B)) = T.B := by
  simp


theorem r23_cube_on_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T (r23 (Geo := Geo) T (r23 (Geo := Geo) T T.C)) = T.C := by
  simp


theorem r23_cube_on_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r23 (Geo := Geo) T (r23 (Geo := Geo) T (r23 (Geo := Geo) T T.D)) = T.D := by
  simp


theorem r13_sq_on_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T (r13 (Geo := Geo) T T.A) = T.A := by
  simp


theorem r13_sq_on_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T (r13 (Geo := Geo) T T.B) = T.B := by
  simp


theorem r13_sq_on_C
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T (r13 (Geo := Geo) T T.C) = T.C := by
  simp


theorem r13_sq_on_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    r13 (Geo := Geo) T (r13 (Geo := Geo) T T.D) = T.D := by
  simp


end CoxeterA3TetrahedralFrame

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 in 3D: rigidity preparation

The purpose of this file is to isolate the synthetic geometric fact
needed for the final global Coxeter relations.

The key observation is Euclid XI.5:

If several lines through one point are perpendicular to the same line,
then any three of those perpendicular lines are coplanar.

For two distinct points X,Y, let M be their midpoint.  A point P with
PX congruent PY determines, unless P=M, a line MP perpendicular to XY.
Consequently four noncoplanar equidistant points cannot exist.

This file proves the local ingredients of that argument.
-/


/--
Uniqueness of a strict Hilbert midpoint in an arbitrary Hilbert plane.

This is kept as a local reusable theorem because the spatial proof below
will apply it inside an induced `PlaneGeo`.
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


/--
Every nondegenerate ambient segment has a strict midpoint.

The construction is carried out in one induced Hilbert plane containing
the segment, then transported back to the ambient space.
-/
theorem hilbert_space_midpoint_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
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
    ⟨Q, hQl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l Q hQl with
    ⟨sigma, hlsigma, _hQsigma, _hUnique⟩

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hlsigma X hXl⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hlsigma Y hYl⟩

  have hXYp : Ne Xp Yp := by
    intro h
    apply hXY
    exact congrArg Subtype.val h

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
If P is equidistant from X and Y and is different from their midpoint M,
then X,M,P are noncollinear.

The only collinear point equidistant from X and Y is their midpoint.
The proof is reduced to an induced plane containing the line XY and uses
the planar midpoint uniqueness theorem proved above.
-/
theorem hilbert_space_equidistant_noncollinear_of_ne_midpoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (X Y M P : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M X Y)
    (hPX_PY : Geo.Congruent P X P Y)
    (hPM : Ne P M) :
    Not (PrimCollinear Geo X M P) := by

  intro hXMP

  have hMidData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
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
    ⟨Q, hQl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l Q hQl with
    ⟨sigma, hlsigma, _hQsigma, _hUnique⟩

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hlsigma X hXl⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hlsigma Y hYl⟩

  let Mp : PlanePoint Geo sigma :=
    ⟨M, hlsigma M hMl⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hlsigma P hPl⟩

  have hXYp : Ne Xp Yp := by
    intro h
    apply hXY
    exact congrArg Subtype.val h

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
A non-midpoint point equidistant from X and Y determines a right angle
with the midpoint:

    XM? no; precisely angle XMP is right.

The proof is spatial SSS applied to triangles M-X-P and M-Y-P.
-/
theorem hilbert_space_equidistant_rightAngle_at_midpoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (X Y M P : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M X Y)
    (hPX_PY : Geo.Congruent P X P Y)
    (hPM : Ne P M) :
    HilbertRightAngle Geo X M P := by

  have hXMP :
      Not (PrimCollinear Geo X M P) :=
    hilbert_space_equidistant_noncollinear_of_ne_midpoint
      (Geo := Geo)
      X Y M P
      hMid hPX_PY hPM

  have hMidData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X M Y hMid.1

  have hXY : Ne X Y :=
    hMidData.2.2.1

  have hXM : Ne X M :=
    hMidData.1

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

  have hPn : Not (H.OnLine P n) := by
    intro hPn

    exact
      hXMP
        ⟨n, hXn, hMn, hPn⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        n P hPn with
    ⟨sigma, hnsigma, hPsigma, _hUnique⟩

  let Mp : PlanePoint Geo sigma :=
    ⟨M, hnsigma M hMn⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hnsigma Y hYn⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hPsigma⟩

  have hMYP :
      Not (PrimCollinear Geo M Y P) := by
    intro hMYP

    rcases hMYP with
      ⟨k, hMk, hYk, hPk⟩

    have hMY : Ne M Y :=
      hMidData.2.1

    have hnk : n = k :=
      HilbertPlaneIncidence.line_unique
        M Y hMY
        n k
        hMn hYn
        hMk hYk

    apply hPn

    rw [hnk]

    exact hPk

  have hMYPplane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Mp Yp Pp) := by

    intro h

    exact
      hMYP
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma Mp Yp Pp
          h)

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
    hilbert_space_congruent_reflexive_all
      (Geo := Geo)
      M P

  have hAngle :
      Geo.AngleCongruent
        X M P
        Y M P :=
    hilbert_space_sss_angleA_in_plane
      (Geo := Geo)
      sigma
      M X P
      Mp Yp Pp
      (by
        intro h
        exact hXMP
          (PrimCollinearSwap
            Geo M X P h))
      hMYPplane
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
The line XY is perpendicular at M to the line MP whenever P is a
non-midpoint point equidistant from X and Y.
-/
theorem hilbert_space_equidistant_line_perpendicular
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
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
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X M Y hMid.1

  have hXY : Ne X Y :=
    hMidData.2.2.1

  have hXM : Ne X M :=
    hMidData.1

  have hXMP :
      Not (PrimCollinear Geo X M P) :=
    hilbert_space_equidistant_noncollinear_of_ne_midpoint
      (Geo := Geo)
      X Y M P
      hMid hPX_PY hPM

  have hRight :
      HilbertRightAngle Geo X M P :=
    hilbert_space_equidistant_rightAngle_at_midpoint
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


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 in 3D: four-anchor rigidity

This file proves the synthetic point-rigidity statement needed to lift
the A3 relations from the tetrahedral frame to the whole ambient space.

The geometric core is Euclid XI.5.

If X != Y and M is the midpoint of XY, every point P satisfying
PX congruent PY determines a line MP perpendicular to XY, unless P=M.
Four noncoplanar anchor points therefore cannot all be equidistant from
X and Y.
-/


/--
If four points are noncoplanar, the first three are noncollinear.

Indeed, if A,B,C lie on one line, that line together with D lies in
some ambient plane.
-/
theorem hilbert_noncoplanar4_not_collinear_first_three
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (A B C D : Geo.Point)
    (hNoncoplanar :
      Not (HilbertCoplanar4 Geo A B C D)) :
    Not (PrimCollinear Geo A B C) := by

  intro hABC

  rcases hABC with
    ⟨l, hAl, hBl, hCl⟩

  by_cases hDl : H.OnLine D l

  · rcases
        hilbert_point_off_line
          (Geo := Geo) l with
      ⟨Q, hQl⟩

    rcases
        hilbert_plane_through_line_and_external_point
          (Geo := Geo)
          l Q hQl with
      ⟨pi, hlpi, _hQpi, _hUnique⟩

    exact
      hNoncoplanar
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hlpi D hDl⟩

  · rcases
        hilbert_plane_through_line_and_external_point
          (Geo := Geo)
          l D hDl with
      ⟨pi, hlpi, hDpi, _hUnique⟩

    exact
      hNoncoplanar
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hDpi⟩


/--
Fix the line XY.  For every non-midpoint point P equidistant from X,Y,
the line MP can be chosen perpendicular to this fixed line XY.

The preparation theorem from test03 initially returns some line through
X,Y; Hilbert I.2 identifies it with the prescribed one.
-/
theorem hilbert_space_equidistant_perpendicular_to_fixed_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (X Y M P : Geo.Point)
    (l : Geo.Line)
    (hXl : H.OnLine X l)
    (hYl : H.OnLine Y l)
    (hMid : HilbertIsMidpoint Geo M X Y)
    (hPX_PY : Geo.Congruent P X P Y)
    (hPM : Ne P M) :
    exists m : Geo.Line,
      H.OnLine M m /\
      H.OnLine P m /\
      HilbertLinesPerpendicularAt Geo l m M := by

  have hXY :
      Ne X Y :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X M Y hMid.1).2.2.1

  rcases
      hilbert_space_equidistant_line_perpendicular
        (Geo := Geo)
        X Y M P
        hMid hPX_PY hPM with
    ⟨n, m,
     hXn, hYn,
     hMm, hPm,
     hPerp⟩

  have hnl : n = l :=
    HilbertPlaneIncidence.line_unique
      X Y hXY
      n l
      hXn hYn
      hXl hYl

  subst n

  exact
    ⟨m, hMm, hPm, hPerp⟩


/--
XI.5 in a fixed reference plane.

Suppose l is perpendicular at O to three lines m,n,p, with m != n.
If a chosen plane pi already contains m and n, then XI.5 forces p to
lie in the same plane pi.
-/
theorem hilbert_XI5_third_perpendicular_line_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m n p : Geo.Line)
    (O : Geo.Point)
    (pi : S.Plane)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m O)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n O)
    (hPerpP :
      HilbertLinesPerpendicularAt Geo l p O)
    (hmpi : HilbertLineInPlane Geo m pi)
    (hnpi : HilbertLineInPlane Geo n pi) :
    HilbertLineInPlane Geo p pi := by

  rcases
      euclid_proposition_11_5
        (Geo := Geo)
        l m n p O
        hmn
        hPerpM
        hPerpN
        hPerpP with
    ⟨sigma,
     hmsigma,
     hnsigma,
     hpsigma⟩

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        m n hmn
        O
        hPerpM.2.1
        hPerpN.2.1 with
    ⟨tau,
     _hmtau,
     _hntau,
     hUniqueTau⟩

  have hPiTau :
      pi = tau :=
    hUniqueTau
      pi hmpi hnpi

  have hSigmaTau :
      sigma = tau :=
    hUniqueTau
      sigma hmsigma hnsigma

  have hPiSigma :
      pi = sigma :=
    hPiTau.trans
      hSigmaTau.symm

  rw [hPiSigma]

  exact hpsigma


/--
Four noncoplanar anchor points determine a point uniquely by its four
distances.

If A,B,C,D are noncoplanar and each is equidistant from X and Y, then
X=Y.
-/
theorem hilbert_space_four_anchor_distance_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D X Y : Geo.Point)
    (hNoncoplanar :
      Not (HilbertCoplanar4 Geo A B C D))
    (hAX_AY : Geo.Congruent A X A Y)
    (hBX_BY : Geo.Congruent B X B Y)
    (hCX_CY : Geo.Congruent C X C Y)
    (hDX_DY : Geo.Congruent D X D Y) :
    X = Y := by

  by_contra hXY

  rcases
      hilbert_space_midpoint_exists
        (Geo := Geo)
        X Y hXY with
    ⟨M, hMid⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X Y hXY with
    ⟨l, hXl, hYl⟩

  ----------------------------------------------------------------------
  -- Noncollinearity of the anchor triples that will be needed below.
  ----------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      A B C D
      hNoncoplanar

  have hNonABDC :
      Not (HilbertCoplanar4 Geo A B D C) := by
    intro h
    rcases h with
      ⟨pi, hApi, hBpi, hDpi, hCpi⟩
    exact
      hNoncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hABD :
      Not (PrimCollinear Geo A B D) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      A B D C
      hNonABDC

  have hNonACDB :
      Not (HilbertCoplanar4 Geo A C D B) := by
    intro h
    rcases h with
      ⟨pi, hApi, hCpi, hDpi, hBpi⟩
    exact
      hNoncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hACD :
      Not (PrimCollinear Geo A C D) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      A C D B
      hNonACDB

  ----------------------------------------------------------------------
  -- Pairwise distinctness of the four anchors.
  ----------------------------------------------------------------------

  have hAB : Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC : Ne A C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (by
        intro h
        exact hABC
          (PrimCollinearRotate
            Geo A C B h))

  have hBC : Ne B C :=
    hilbert_noncollinear_ne_first
      Geo B C A
      (by
        intro h
        exact hABC
          (PrimCollinearCycle
            Geo C A B
            (PrimCollinearCycle
              Geo B C A h)))

  have hAD : Ne A D :=
    hilbert_noncollinear_ne_first
      Geo A D B
      (by
        intro h
        exact hABD
          (PrimCollinearRotate
            Geo A D B h))

  have hBD : Ne B D :=
    hilbert_noncollinear_ne_first
      Geo B D A
      (by
        intro h
        exact hABD
          (PrimCollinearCycle
            Geo D A B
            (PrimCollinearCycle
              Geo B D A h)))

  have hCD : Ne C D :=
    hilbert_noncollinear_ne_first
      Geo C D A
      (by
        intro h
        exact hACD
          (PrimCollinearCycle
            Geo D A C
            (PrimCollinearCycle
              Geo C D A h)))

  ----------------------------------------------------------------------
  -- Case M = A.
  ----------------------------------------------------------------------

  by_cases hMA : M = A

  · have hBM : Ne B M := by
      simpa [hMA] using hAB.symm

    have hCM : Ne C M := by
      simpa [hMA] using hAC.symm

    have hDM : Ne D M := by
      simpa [hMA] using hAD.symm

    rcases
        hilbert_space_equidistant_perpendicular_to_fixed_line
          (Geo := Geo)
          X Y M B l
          hXl hYl hMid
          hBX_BY hBM with
      ⟨mB, hMmB, hBmB, hPerpB⟩

    rcases
        hilbert_space_equidistant_perpendicular_to_fixed_line
          (Geo := Geo)
          X Y M C l
          hXl hYl hMid
          hCX_CY hCM with
      ⟨mC, hMmC, hCmC, hPerpC⟩

    rcases
        hilbert_space_equidistant_perpendicular_to_fixed_line
          (Geo := Geo)
          X Y M D l
          hXl hYl hMid
          hDX_DY hDM with
      ⟨mD, hMmD, hDmD, hPerpD⟩

    have hmBC : Ne mB mC := by
      intro hEq
      apply hABC
      exact
        ⟨mB,
         by simpa [hMA] using hMmB,
         hBmB,
         by
           rw [hEq]
           exact hCmC⟩

    rcases
        hilbert_plane_through_two_intersecting_lines
          (Geo := Geo)
          mB mC hmBC
          M hMmB hMmC with
      ⟨pi, hmBpi, hmCpi, _hUnique⟩

    have hmDpi :
        HilbertLineInPlane Geo mD pi :=
      hilbert_XI5_third_perpendicular_line_in_plane
        (Geo := Geo)
        l mB mC mD
        M pi
        hmBC
        hPerpB hPerpC hPerpD
        hmBpi hmCpi

    exact
      hNoncoplanar
        ⟨pi,
         hmBpi A
           (by simpa [hMA] using hMmB),
         hmBpi B hBmB,
         hmCpi C hCmC,
         hmDpi D hDmD⟩

  ----------------------------------------------------------------------
  -- Case M = B.
  ----------------------------------------------------------------------

  · by_cases hMB : M = B

    · have hAM : Ne A M := by
        simpa [hMB] using hAB

      have hCM : Ne C M := by
        simpa [hMB] using hBC.symm

      have hDM : Ne D M := by
        simpa [hMB] using hBD.symm

      rcases
          hilbert_space_equidistant_perpendicular_to_fixed_line
            (Geo := Geo)
            X Y M A l
            hXl hYl hMid
            hAX_AY hAM with
        ⟨mA, hMmA, hAmA, hPerpA⟩

      rcases
          hilbert_space_equidistant_perpendicular_to_fixed_line
            (Geo := Geo)
            X Y M C l
            hXl hYl hMid
            hCX_CY hCM with
        ⟨mC, hMmC, hCmC, hPerpC⟩

      rcases
          hilbert_space_equidistant_perpendicular_to_fixed_line
            (Geo := Geo)
            X Y M D l
            hXl hYl hMid
            hDX_DY hDM with
        ⟨mD, hMmD, hDmD, hPerpD⟩

      have hmAC : Ne mA mC := by
        intro hEq
        apply hABC
        exact
          ⟨mA,
           hAmA,
           by simpa [hMB] using hMmA,
           by
             rw [hEq]
             exact hCmC⟩

      rcases
          hilbert_plane_through_two_intersecting_lines
            (Geo := Geo)
            mA mC hmAC
            M hMmA hMmC with
        ⟨pi, hmApi, hmCpi, _hUnique⟩

      have hmDpi :
          HilbertLineInPlane Geo mD pi :=
        hilbert_XI5_third_perpendicular_line_in_plane
          (Geo := Geo)
          l mA mC mD
          M pi
          hmAC
          hPerpA hPerpC hPerpD
          hmApi hmCpi

      exact
        hNoncoplanar
          ⟨pi,
           hmApi A hAmA,
           hmApi B
             (by simpa [hMB] using hMmA),
           hmCpi C hCmC,
           hmDpi D hDmD⟩

    --------------------------------------------------------------------
    -- Case M = C.
    --------------------------------------------------------------------

    · by_cases hMC : M = C

      · have hAM : Ne A M := by
          simpa [hMC] using hAC

        have hBM : Ne B M := by
          simpa [hMC] using hBC

        have hDM : Ne D M := by
          simpa [hMC] using hCD.symm

        rcases
            hilbert_space_equidistant_perpendicular_to_fixed_line
              (Geo := Geo)
              X Y M A l
              hXl hYl hMid
              hAX_AY hAM with
          ⟨mA, hMmA, hAmA, hPerpA⟩

        rcases
            hilbert_space_equidistant_perpendicular_to_fixed_line
              (Geo := Geo)
              X Y M B l
              hXl hYl hMid
              hBX_BY hBM with
          ⟨mB, hMmB, hBmB, hPerpB⟩

        rcases
            hilbert_space_equidistant_perpendicular_to_fixed_line
              (Geo := Geo)
              X Y M D l
              hXl hYl hMid
              hDX_DY hDM with
          ⟨mD, hMmD, hDmD, hPerpD⟩

        have hmAB : Ne mA mB := by
          intro hEq
          apply hABC
          exact
            ⟨mA,
             hAmA,
             by
               rw [hEq]
               exact hBmB,
             by simpa [hMC] using hMmA⟩

        rcases
            hilbert_plane_through_two_intersecting_lines
              (Geo := Geo)
              mA mB hmAB
              M hMmA hMmB with
          ⟨pi, hmApi, hmBpi, _hUnique⟩

        have hmDpi :
            HilbertLineInPlane Geo mD pi :=
          hilbert_XI5_third_perpendicular_line_in_plane
            (Geo := Geo)
            l mA mB mD
            M pi
            hmAB
            hPerpA hPerpB hPerpD
            hmApi hmBpi

        exact
          hNoncoplanar
            ⟨pi,
             hmApi A hAmA,
             hmBpi B hBmB,
             hmApi C
               (by simpa [hMC] using hMmA),
             hmDpi D hDmD⟩

      ------------------------------------------------------------------
      -- Case M = D.
      ------------------------------------------------------------------

      · by_cases hMD : M = D

        · have hAM : Ne A M := by
            simpa [hMD] using hAD

          have hBM : Ne B M := by
            simpa [hMD] using hBD

          have hCM : Ne C M := by
            simpa [hMD] using hCD

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M A l
                hXl hYl hMid
                hAX_AY hAM with
            ⟨mA, hMmA, hAmA, hPerpA⟩

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M B l
                hXl hYl hMid
                hBX_BY hBM with
            ⟨mB, hMmB, hBmB, hPerpB⟩

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M C l
                hXl hYl hMid
                hCX_CY hCM with
            ⟨mC, hMmC, hCmC, hPerpC⟩

          have hmAB : Ne mA mB := by
            intro hEq
            apply hABD
            exact
              ⟨mA,
               hAmA,
               by
                 rw [hEq]
                 exact hBmB,
               by simpa [hMD] using hMmA⟩

          rcases
              hilbert_plane_through_two_intersecting_lines
                (Geo := Geo)
                mA mB hmAB
                M hMmA hMmB with
            ⟨pi, hmApi, hmBpi, _hUnique⟩

          have hmCpi :
              HilbertLineInPlane Geo mC pi :=
            hilbert_XI5_third_perpendicular_line_in_plane
              (Geo := Geo)
              l mA mB mC
              M pi
              hmAB
              hPerpA hPerpB hPerpC
              hmApi hmBpi

          exact
            hNoncoplanar
              ⟨pi,
               hmApi A hAmA,
               hmBpi B hBmB,
               hmCpi C hCmC,
               hmApi D
                 (by simpa [hMD] using hMmA)⟩

        ----------------------------------------------------------------
        -- Generic case: M is none of A,B,C,D.
        ----------------------------------------------------------------

        · have hAM : Ne A M := by
            intro h
            exact hMA h.symm

          have hBM : Ne B M := by
            intro h
            exact hMB h.symm

          have hCM : Ne C M := by
            intro h
            exact hMC h.symm

          have hDM : Ne D M := by
            intro h
            exact hMD h.symm

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M A l
                hXl hYl hMid
                hAX_AY hAM with
            ⟨mA, hMmA, hAmA, hPerpA⟩

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M B l
                hXl hYl hMid
                hBX_BY hBM with
            ⟨mB, hMmB, hBmB, hPerpB⟩

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M C l
                hXl hYl hMid
                hCX_CY hCM with
            ⟨mC, hMmC, hCmC, hPerpC⟩

          rcases
              hilbert_space_equidistant_perpendicular_to_fixed_line
                (Geo := Geo)
                X Y M D l
                hXl hYl hMid
                hDX_DY hDM with
            ⟨mD, hMmD, hDmD, hPerpD⟩

          by_cases hmAB : mA = mB

          --------------------------------------------------------------
          -- mA = mB: use mA and mC as the two distinct reference lines.
          --------------------------------------------------------------

          · have hmAC : Ne mA mC := by
              intro hmACeq
              apply hABC
              exact
                ⟨mA,
                 hAmA,
                 by
                   rw [hmAB]
                   exact hBmB,
                 by
                   rw [hmACeq]
                   exact hCmC⟩

            rcases
                hilbert_plane_through_two_intersecting_lines
                  (Geo := Geo)
                  mA mC hmAC
                  M hMmA hMmC with
              ⟨pi, hmApi, hmCpi, _hUnique⟩

            have hmDpi :
                HilbertLineInPlane Geo mD pi :=
              hilbert_XI5_third_perpendicular_line_in_plane
                (Geo := Geo)
                l mA mC mD
                M pi
                hmAC
                hPerpA hPerpC hPerpD
                hmApi hmCpi

            exact
              hNoncoplanar
                ⟨pi,
                 hmApi A hAmA,
                 hmApi B
                   (by
                     rw [hmAB]
                     exact hBmB),
                 hmCpi C hCmC,
                 hmDpi D hDmD⟩

          --------------------------------------------------------------
          -- mA != mB: both mC and mD are forced into their plane.
          --------------------------------------------------------------

          · rcases
                hilbert_plane_through_two_intersecting_lines
                  (Geo := Geo)
                  mA mB hmAB
                  M hMmA hMmB with
              ⟨pi, hmApi, hmBpi, _hUnique⟩

            have hmCpi :
                HilbertLineInPlane Geo mC pi :=
              hilbert_XI5_third_perpendicular_line_in_plane
                (Geo := Geo)
                l mA mB mC
                M pi
                hmAB
                hPerpA hPerpB hPerpC
                hmApi hmBpi

            have hmDpi :
                HilbertLineInPlane Geo mD pi :=
              hilbert_XI5_third_perpendicular_line_in_plane
                (Geo := Geo)
                l mA mB mD
                M pi
                hmAB
                hPerpA hPerpB hPerpD
                hmApi hmBpi

            exact
              hNoncoplanar
                ⟨pi,
                 hmApi A hAmA,
                 hmBpi B hBmB,
                 hmCpi C hCmC,
                 hmDpi D hDmD⟩


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 in 3D: global rigidity and global relations

The geometric work is now complete.

Test02 proved the Coxeter words on the four vertices of the tetrahedral
frame.  Test04 proved that four noncoplanar anchor points determine any
point uniquely by its four distances.

Therefore a synthetic 3D isometry fixing the four vertices is the
identity on the whole ambient space.
-/


namespace HilbertSpaceIsometry3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]


/--
Synthetic 3D rigidity.

A segment-congruence-preserving equivalence which fixes four
noncoplanar points is the identity on the whole ambient space.
-/
theorem eq_refl_of_fix_noncoplanar4
    (f : HilbertSpaceIsometry3D Geo)
    (A B C D : Geo.Point)
    (hNoncoplanar :
      Not (HilbertCoplanar4 Geo A B C D))
    (hA : f.toEquiv A = A)
    (hB : f.toEquiv B = B)
    (hC : f.toEquiv C = C)
    (hD : f.toEquiv D = D) :
    f.toEquiv = Equiv.refl Geo.Point := by

  apply Equiv.ext
  intro P

  have hAP :
      Geo.Congruent
        A P
        A (f.toEquiv P) := by

    have h :=
      f.preserves_congruence A P

    rw [hA] at h

    exact h

  have hBP :
      Geo.Congruent
        B P
        B (f.toEquiv P) := by

    have h :=
      f.preserves_congruence B P

    rw [hB] at h

    exact h

  have hCP :
      Geo.Congruent
        C P
        C (f.toEquiv P) := by

    have h :=
      f.preserves_congruence C P

    rw [hC] at h

    exact h

  have hDP :
      Geo.Congruent
        D P
        D (f.toEquiv P) := by

    have h :=
      f.preserves_congruence D P

    rw [hD] at h

    exact h

  have hUnique :
      P = f.toEquiv P :=
    hilbert_space_four_anchor_distance_unique
      (Geo := Geo)
      A B C D
      P (f.toEquiv P)
      hNoncoplanar
      hAP hBP hCP hDP

  simpa using hUnique.symm


end HilbertSpaceIsometry3D


namespace CoxeterA3TetrahedralFrame

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
## Packaged generator isometries
-/

/--
The first tetrahedral reflection, packaged as a 3D isometry.
-/
noncomputable def iso1
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  planeReflectionIsometry3D
    (Geo := Geo)
    T.pi1


/--
The second tetrahedral reflection, packaged as a 3D isometry.
-/
noncomputable def iso2
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  planeReflectionIsometry3D
    (Geo := Geo)
    T.pi2


/--
The third tetrahedral reflection, packaged as a 3D isometry.
-/
noncomputable def iso3
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  planeReflectionIsometry3D
    (Geo := Geo)
    T.pi3


@[simp]
theorem iso1_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo) :
    (iso1 (Geo := Geo) T).toEquiv =
      r1 (Geo := Geo) T := by
  rfl


@[simp]
theorem iso2_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo) :
    (iso2 (Geo := Geo) T).toEquiv =
      r2 (Geo := Geo) T := by
  rfl


@[simp]
theorem iso3_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo) :
    (iso3 (Geo := Geo) T).toEquiv =
      r3 (Geo := Geo) T := by
  rfl


/-!
## Pair products as synthetic 3D isometries
-/

/--
The product r1 r2, with the same left-to-right convention as `r12`.
-/
noncomputable def iso12
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  HilbertSpaceIsometry3D.trans
    (Geo := Geo)
    (iso1 (Geo := Geo) T)
    (iso2 (Geo := Geo) T)


/--
The product r2 r3.
-/
noncomputable def iso23
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  HilbertSpaceIsometry3D.trans
    (Geo := Geo)
    (iso2 (Geo := Geo) T)
    (iso3 (Geo := Geo) T)


/--
The product r1 r3.
-/
noncomputable def iso13
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  HilbertSpaceIsometry3D.trans
    (Geo := Geo)
    (iso1 (Geo := Geo) T)
    (iso3 (Geo := Geo) T)


@[simp]
theorem iso12_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo) :
    (iso12 (Geo := Geo) T).toEquiv =
      r12 (Geo := Geo) T := by
  rfl


@[simp]
theorem iso23_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo) :
    (iso23 (Geo := Geo) T).toEquiv =
      r23 (Geo := Geo) T := by
  rfl


@[simp]
theorem iso13_toEquiv
    (T : CoxeterA3TetrahedralFrame Geo) :
    (iso13 (Geo := Geo) T).toEquiv =
      r13 (Geo := Geo) T := by
  rfl


/-!
## Coxeter words as synthetic 3D isometries
-/

/--
The word (r1 r2)^3.
-/
noncomputable def word12cube
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  HilbertSpaceIsometry3D.trans
    (Geo := Geo)
    (HilbertSpaceIsometry3D.trans
      (Geo := Geo)
      (iso12 (Geo := Geo) T)
      (iso12 (Geo := Geo) T))
    (iso12 (Geo := Geo) T)


/--
The word (r2 r3)^3.
-/
noncomputable def word23cube
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  HilbertSpaceIsometry3D.trans
    (Geo := Geo)
    (HilbertSpaceIsometry3D.trans
      (Geo := Geo)
      (iso23 (Geo := Geo) T)
      (iso23 (Geo := Geo) T))
    (iso23 (Geo := Geo) T)


/--
The word (r1 r3)^2.
-/
noncomputable def word13sq
    (T : CoxeterA3TetrahedralFrame Geo) :
    HilbertSpaceIsometry3D Geo :=
  HilbertSpaceIsometry3D.trans
    (Geo := Geo)
    (iso13 (Geo := Geo) T)
    (iso13 (Geo := Geo) T)


@[simp]
theorem word12cube_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (P : Geo.Point) :
    (word12cube
      (Geo := Geo) T).toEquiv P =
      r12 (Geo := Geo) T
        (r12 (Geo := Geo) T
          (r12 (Geo := Geo) T P)) := by
  rfl


@[simp]
theorem word23cube_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (P : Geo.Point) :
    (word23cube
      (Geo := Geo) T).toEquiv P =
      r23 (Geo := Geo) T
        (r23 (Geo := Geo) T
          (r23 (Geo := Geo) T P)) := by
  rfl


@[simp]
theorem word13sq_apply
    (T : CoxeterA3TetrahedralFrame Geo)
    (P : Geo.Point) :
    (word13sq
      (Geo := Geo) T).toEquiv P =
      r13 (Geo := Geo) T
        (r13 (Geo := Geo) T P) := by
  rfl


/-!
## The three nontrivial global A3 relations
-/

/--
Global relation (r1 r2)^3 = 1.
-/
theorem word12cube_eq_refl
    (T : CoxeterA3TetrahedralFrame Geo) :
    (word12cube
      (Geo := Geo) T).toEquiv =
      Equiv.refl Geo.Point := by

  apply
    HilbertSpaceIsometry3D.eq_refl_of_fix_noncoplanar4
      (Geo := Geo)
      (word12cube (Geo := Geo) T)
      T.A T.B T.C T.D
      T.noncoplanar

  · rw [word12cube_apply]
    exact r12_cube_on_A
      (Geo := Geo) T

  · rw [word12cube_apply]
    exact r12_cube_on_B
      (Geo := Geo) T

  · rw [word12cube_apply]
    exact r12_cube_on_C
      (Geo := Geo) T

  · rw [word12cube_apply]
    exact r12_cube_on_D
      (Geo := Geo) T


/--
Global relation (r2 r3)^3 = 1.
-/
theorem word23cube_eq_refl
    (T : CoxeterA3TetrahedralFrame Geo) :
    (word23cube
      (Geo := Geo) T).toEquiv =
      Equiv.refl Geo.Point := by

  apply
    HilbertSpaceIsometry3D.eq_refl_of_fix_noncoplanar4
      (Geo := Geo)
      (word23cube (Geo := Geo) T)
      T.A T.B T.C T.D
      T.noncoplanar

  · rw [word23cube_apply]
    exact r23_cube_on_A
      (Geo := Geo) T

  · rw [word23cube_apply]
    exact r23_cube_on_B
      (Geo := Geo) T

  · rw [word23cube_apply]
    exact r23_cube_on_C
      (Geo := Geo) T

  · rw [word23cube_apply]
    exact r23_cube_on_D
      (Geo := Geo) T


/--
Global relation (r1 r3)^2 = 1.
-/
theorem word13sq_eq_refl
    (T : CoxeterA3TetrahedralFrame Geo) :
    (word13sq
      (Geo := Geo) T).toEquiv =
      Equiv.refl Geo.Point := by

  apply
    HilbertSpaceIsometry3D.eq_refl_of_fix_noncoplanar4
      (Geo := Geo)
      (word13sq (Geo := Geo) T)
      T.A T.B T.C T.D
      T.noncoplanar

  · rw [word13sq_apply]
    exact r13_sq_on_A
      (Geo := Geo) T

  · rw [word13sq_apply]
    exact r13_sq_on_B
      (Geo := Geo) T

  · rw [word13sq_apply]
    exact r13_sq_on_C
      (Geo := Geo) T

  · rw [word13sq_apply]
    exact r13_sq_on_D
      (Geo := Geo) T


/-!
## Literal Equiv forms of the global Coxeter relations
-/

/--
Literal transformation equation for (r1 r2)^3 = 1.
-/
theorem r12_cube_eq_refl
    (T : CoxeterA3TetrahedralFrame Geo) :
    ((r12 (Geo := Geo) T).trans
      (r12 (Geo := Geo) T)).trans
      (r12 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by

  exact
    word12cube_eq_refl
      (Geo := Geo) T


/--
Literal transformation equation for (r2 r3)^3 = 1.
-/
theorem r23_cube_eq_refl
    (T : CoxeterA3TetrahedralFrame Geo) :
    ((r23 (Geo := Geo) T).trans
      (r23 (Geo := Geo) T)).trans
      (r23 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by

  exact
    word23cube_eq_refl
      (Geo := Geo) T


/--
Literal transformation equation for (r1 r3)^2 = 1.
-/
theorem r13_sq_eq_refl
    (T : CoxeterA3TetrahedralFrame Geo) :
    (r13 (Geo := Geo) T).trans
      (r13 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by

  exact
    word13sq_eq_refl
      (Geo := Geo) T


/-!
## Complete A3 relation package
-/

/--
All Coxeter relations of type A3 for the tetrahedral mirror frame.
-/
theorem coxeter_A3_relations
    (T : CoxeterA3TetrahedralFrame Geo) :
    (r1 (Geo := Geo) T).trans
        (r1 (Geo := Geo) T) =
        Equiv.refl Geo.Point
    /\
    (r2 (Geo := Geo) T).trans
        (r2 (Geo := Geo) T) =
        Equiv.refl Geo.Point
    /\
    (r3 (Geo := Geo) T).trans
        (r3 (Geo := Geo) T) =
        Equiv.refl Geo.Point
    /\
    ((r12 (Geo := Geo) T).trans
        (r12 (Geo := Geo) T)).trans
        (r12 (Geo := Geo) T) =
        Equiv.refl Geo.Point
    /\
    ((r23 (Geo := Geo) T).trans
        (r23 (Geo := Geo) T)).trans
        (r23 (Geo := Geo) T) =
        Equiv.refl Geo.Point
    /\
    (r13 (Geo := Geo) T).trans
        (r13 (Geo := Geo) T) =
        Equiv.refl Geo.Point := by

  exact
    ⟨r1_sq (Geo := Geo) T,
     r2_sq (Geo := Geo) T,
     r3_sq (Geo := Geo) T,
     r12_cube_eq_refl (Geo := Geo) T,
     r23_cube_eq_refl (Geo := Geo) T,
     r13_sq_eq_refl (Geo := Geo) T⟩


end CoxeterA3TetrahedralFrame

end Geometry

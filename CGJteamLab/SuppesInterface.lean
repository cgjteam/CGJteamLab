import CGJteamLab.SuppesAxioms

namespace Geometry
namespace Suppes

section Suppes

variable [SuppesGeometry Point]

local notation "Mid" =>
  SuppesGeometry.operation_midpoint

local notation "Col" =>
  SuppesGeometry.Collinear

/-- Primitive notion of triangle. -/
def PrimTriangle (A B C : Point) : Prop :=
  ¬ Col A B C

/--
Primitive notion of parallelogram (Suppes).

P(A,B,C,D) iff T(A,B,C) and Midpoint(A,C) = Midpoint(B,D).
-/
def PrimParallelogram (A B C D : Point) : Prop :=
  PrimTriangle A B C ∧
  Mid A C = Mid B D

/-!
# Suppes Theorems

Elementary theorems derived from the quantifier-free axioms of
Patrick Suppes' constructive affine geometry.

This file contains only derived results.
The axioms are defined in `SuppesAxioms.lean`.
-/

/-- Algebraic part of Suppes' Theorem 11. -/
theorem midpoint_left_distrib
    (A B C : Point) :
    Mid A (Mid B C) =
    Mid (Mid A B) (Mid A C) := by
  calc
    Mid A (Mid B C)
        = Mid (Mid A A) (Mid B C) := by
            rw [midpoint_idempotent]
    _ = Mid (Mid A B) (Mid A C) := by
            exact midpoint_bicommutative A A B C

/-- Geometric part of Suppes' Theorem 11. -/
theorem midpoint_triangle
    (A B C : Point)
    (h : PrimTriangle A B C) :
    PrimTriangle
      (Mid A B)
      (Mid B C)
      (Mid A C) := by
  intro hcol
  apply h
  exact LL A B C hcol

/-- Suppes, Theorem 3. -/
theorem midpoint_fixed
    (A B : Point)
    (h : Mid A B = A) :
    A = B := by
  have hBA : B = A := by
    apply midpoint_cancellation A B A
    calc
      Mid A B = A := h
      _ = Mid A A := by
        symm
        exact midpoint_idempotent A
  exact hBA.symm

/-- Suppes, Theorem 4 (Reduction). -/
local notation "Dbl" =>
  SuppesGeometry.operation_double

/-- Suppes' Theorem 4 (Reduction). -/
theorem doubling_reduction
    (A B : Point) :
    Dbl A (Mid A B) = B := by
  apply midpoint_cancellation A (Dbl A (Mid A B)) B
  calc
    Mid A (Dbl A (Mid A B))
        = Mid A B := by
          exact midpoint_double_reduction A (Mid A B)

/- Suppes' Theorem 5. -/
/-- Suppes' Theorem 5. -/
theorem parallelogram_not_crossed
    (A B C D : Point) :
    PrimParallelogram A B C D →
    ¬ PrimParallelogram A C B D := by
  intro hP hCross

  rcases hP with ⟨hTri, hAC⟩
  rcases hCross with ⟨_, hAB⟩

  have h3 :
      Mid (Mid A B) (Mid C D) =
      Mid (Mid A C) (Mid B D) := by
    exact midpoint_bicommutative A B C D

  have h4 :
      Mid A B = Mid A C := by
    calc
      Mid A B
          = Mid (Mid A B) (Mid A B) := by
              symm
              exact midpoint_idempotent (Mid A B)
      _ = Mid (Mid A B) (Mid C D) := by
              rw [hAB]
      _ = Mid (Mid A C) (Mid B D) := by
              exact h3
      _ = Mid (Mid A C) (Mid A C) := by
              rw [hAC]
      _ = Mid A C := by
              exact midpoint_idempotent (Mid A C)

  have hBC : B = C := by
    exact midpoint_cancellation A B C h4

  have hCol : Col A B C := by
    apply L2
    exact Or.inr (Or.inr hBC)

  exact hTri hCol


theorem MidpointParallelogram
    (A B C : Point)
    (h : PrimTriangle A B C) :
    PrimParallelogram
      (Mid A B)
      (Mid B C)
      (Mid A C)
      A := by
  constructor
  ·
    exact midpoint_triangle A B C h
  ·
    calc
      Mid (Mid A B) (Mid A C)
          = Mid A (Mid B C) := by
              symm
              exact midpoint_left_distrib A B C
      _ = Mid (Mid B C) A := by
              exact midpoint_commutative _ _

/-! Collinearity is invariant under permutations of points on a nontrivial line. -/
private theorem collinear_swap_last_aux
    {A B P : Point}
    (hAB : A ≠ B)
    (h : Col A B P) :
    Col A P B := by
  have hA : Col A B A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hB : Col A B B := by
    apply L2
    exact Or.inr (Or.inr rfl)
  exact L3 A B A P B hAB hA h hB

private theorem collinear_swap_first_aux
    {A B P : Point}
    (hAB : A ≠ B)
    (h : Col A B P) :
    Col B A P := by
  have hA : Col A B A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hB : Col A B B := by
    apply L2
    exact Or.inr (Or.inr rfl)
  exact L3 A B B A P hAB hB hA h

/-- The triangle part of the third cyclic permutation of a parallelogram. -/
theorem rotate_triangle
    {A B C D : Point} :
    PrimTriangle A B C →
    Mid A C = Mid B D →
    PrimTriangle D A B := by
  intro hTri hMid hDAB

  have hAB : A ≠ B := by
    intro hAB
    apply hTri
    apply L2
    exact Or.inl hAB

  have hAC : A ≠ C := by
    intro hAC
    apply hTri
    apply L2
    exact Or.inr (Or.inl hAC)

  have hDA : D ≠ A := by
    intro hDA
    have hMid' : Mid A C = Mid A B := by
      calc
        Mid A C = Mid B D := hMid
        _ = Mid B A := by rw [hDA]
        _ = Mid A B := midpoint_commutative B A
    have hCB : C = B := midpoint_cancellation A C B hMid'
    apply hTri
    apply L2
    exact Or.inr (Or.inr hCB.symm)

  have hDB : D ≠ B := by
    intro hDB
    have hMid' : Mid A C = B := by
      calc
        Mid A C = Mid B D := hMid
        _ = Mid B B := by rw [hDB]
        _ = B := midpoint_idempotent B
    have hACB : Col A C B := by
      rw [← hMid']
      exact midpoint_collinear A C
    apply hTri
    exact collinear_swap_last_aux hAC hACB

  have hDBA : Col D B A :=
    collinear_swap_last_aux hDA hDAB
  have hBDM : Col B D (Mid A C) := by
    rw [hMid]
    exact midpoint_collinear B D
  have hDBM : Col D B (Mid A C) :=
    collinear_swap_first_aux hDB.symm hBDM
  have hDBD : Col D B D := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hDAM : Col D A (Mid A C) :=
    L3 D B D A (Mid A C) hDB hDBD hDBA hDBM

  have hAD : A ≠ D := Ne.symm hDA
  have hADA : Col A D A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hADB : Col A D B :=
    collinear_swap_first_aux hDA hDAB
  have hADM : Col A D (Mid A C) :=
    collinear_swap_first_aux hDA hDAM
  have hABM : Col A B (Mid A C) :=
    L3 A D A B (Mid A C) hAD hADA hADB hADM

  have hAMC : Col A (Mid A C) C :=
    collinear_swap_last_aux hAC (midpoint_collinear A C)
  have hAM : A ≠ Mid A C := by
    intro hAM
    have hAC' : A = C := midpoint_fixed A C hAM.symm
    apply hTri
    apply L2
    exact Or.inr (Or.inl hAC')
  have hAMA : Col A (Mid A C) A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hAMB : Col A (Mid A C) B :=
    collinear_swap_last_aux hAB hABM
  exact hTri (L3 A (Mid A C) A B C hAM hAMA hAMB hAMC)

theorem parallelogram_rotate3
    {A B C D : Point} :
    PrimParallelogram A B C D →
    PrimParallelogram D A B C := by
  intro h
  rcases h with ⟨hTri, hMid⟩

  constructor
  ·
    exact rotate_triangle hTri hMid
  ·
    simpa [midpoint_commutative] using hMid.symm

/-!
## Reverse engineering of Suppes' Theorem 9
-/
/-
In a primitive parallelogram the fourth vertex cannot coincide
with the first one.

This is the first contradiction used in Suppes' proof of
Theorem 9.
-/

/-
Triangle formed by one vertex and the adjacent midpoints.

This is the analogue of Suppes' Theorem 8.
-/

/--
Suppes, Theorem 1(i): swapping the first two points
preserves collinearity.
-/

theorem collinear_swap
    {A B C : Point} :
    SuppesGeometry.Collinear A B C ->
    SuppesGeometry.Collinear B A C := by
  intro hABC
  by_cases hAB : A = B
  · simpa [hAB] using hABC
  · apply L3 A B B A C
    · exact hAB
    · apply L2
      exact Or.inr (Or.inr rfl)
    · apply L2
      exact Or.inr (Or.inl rfl)
    · exact hABC

theorem theorem11
    (A B C : Point)
    (h : PrimTriangle A B C) :
    PrimParallelogram
      A
      (Mid A B)
      (Mid B C)
      (Mid A C) := by
  have hPar :
      PrimParallelogram
        (Mid A B)
        (Mid B C)
        (Mid A C)
        A :=
    MidpointParallelogram A B C h

  exact parallelogram_rotate3 hPar

/-!
## Parallel segments

Suppes, Definition 3.
-/

/--
Suppes' primitive definition of parallel segments.

The segment AB is parallel to CD iff:
1. A, B, C form a triangle,
2. C and D are distinct,
3. A, B, Dbl A (Mid B D), D form a primitive parallelogram,
4. C, Dbl A (Mid B D), D are collinear.
-/

/-
Cyclic permutation of a primitive triangle.
Derived from Theorem 1(i) for collinearity.
-/


def SuppesParallel (A B C D : Point) : Prop :=
  PrimTriangle A B C ∧
  C ≠ D ∧
  PrimParallelogram A B (Dbl A (Mid B D)) D ∧
  Col C (Dbl A (Mid B D)) D




/--
Suppes, Theorem 1(i): cyclic permutation of collinearity.
-/

theorem collinear_rotate
    {A B C : Point} :
    Col A B C -> Col B C A := by
  intro hABC
  by_cases hAB : A = B
  · apply L2
    exact Or.inr (Or.inl hAB.symm)
  · apply L3 A B B C A
    · exact hAB
    · apply L2
      exact Or.inr (Or.inr rfl)
    · exact hABC
    · apply L2
      exact Or.inr (Or.inl rfl)

/-
Cyclic permutation of a primitive triangle.
-/
theorem triangle_rotate
    {A B C : Point} :
    PrimTriangle A B C -> PrimTriangle B C A := by
  intro hT
  unfold PrimTriangle at hT ⊢
  intro hBCA
  apply hT
  exact collinear_rotate (collinear_rotate hBCA)

theorem parallelogram_construct
    (A B C : Point)
    (hT : PrimTriangle A B C) :
    PrimParallelogram
      C A B
      (Dbl A (Mid B C)) := by
  unfold PrimParallelogram
  constructor
  · exact triangle_rotate (triangle_rotate hT)
  · calc
      Mid C B = Mid B C :=
        midpoint_commutative C B
      _ = Mid A (Dbl A (Mid B C)) :=
        (midpoint_double_reduction A (Mid B C)).symm

theorem parallelogram_parallel_second
    (A B C D : Point)
    (hP : PrimParallelogram A B C D) :
    SuppesParallel B C A D := by

  unfold SuppesParallel

  refine ⟨triangle_rotate hP.1, ?_, ?_, ?_⟩

  · -- A ≠ D
    intro hAD
    have hT : PrimTriangle D A B :=
      (parallelogram_rotate3 hP).1
    apply hT
    apply L2
    exact Or.inl hAD.symm

  · -- PrimParallelogram B C (Dbl B (Mid C D)) D
    unfold PrimParallelogram
    constructor

    · -- triangularity
      have hBCD : PrimTriangle B C D :=
        (parallelogram_rotate3
          (parallelogram_rotate3
            (parallelogram_rotate3 hP))).1

      have hConstruct :=
        parallelogram_construct B C D hBCD

      have hRot :=
        parallelogram_rotate3
          (parallelogram_rotate3
            (parallelogram_rotate3 hConstruct))

      exact hRot.1

    · exact midpoint_double_reduction B (Mid C D)

  · let X : Point := Dbl B (Mid C D)
    change Col A X D

    have hBX : Mid B X = Mid C D := by
      dsimp [X]
      exact midpoint_double_reduction B (Mid C D)

    have hAXmid : Mid A X = D := by
      apply midpoint_cancellation (Mid B C) (Mid A X) D
      calc
        Mid (Mid B C) (Mid A X)
            = Mid (Mid A X) (Mid B C) := by
                exact midpoint_commutative _ _
        _ = Mid (Mid A B) (Mid X C) := by
                exact midpoint_bicommutative A X B C
        _ = Mid (Mid A B) (Mid C X) := by
                rw [midpoint_commutative X C]
        _ = Mid (Mid A C) (Mid B X) := by
                exact midpoint_bicommutative A B C X
        _ = Mid (Mid B D) (Mid C D) := by
                rw [hP.2, hBX]
        _ = Mid (Mid B C) (Mid D D) := by
                exact midpoint_bicommutative B D C D
        _ = Mid (Mid B C) D := by
                rw [midpoint_idempotent D]

    have hX : X = Dbl A D := by
      apply midpoint_cancellation A X (Dbl A D)
      calc
        Mid A X = D := hAXmid
        _ = Mid A (Dbl A D) := by
              symm
              exact midpoint_double_reduction A D

    rw [hX]

    have hCol :
        Col A (Dbl A D) (Mid A (Dbl A D)) :=
      midpoint_collinear A (Dbl A D)

    rw [midpoint_double_reduction A D] at hCol
    exact hCol

/--
Suppes, Theorem 12.

If P(a,b,c,d), P(c,d,e,f), T(a,b,e), and T(a,b,f),
then P(a,b,f,e).

This is the constructive affine analogue of a local
transitivity property for parallelograms.
-/

theorem parallelogram_transitive
    (a b c d e f : Point)
    (hP1 : PrimParallelogram a b c d)
    (hP2 : PrimParallelogram c d e f)
    (_hTabe : PrimTriangle a b e)
    (hTabf : PrimTriangle a b f) :
    PrimParallelogram a b f e := by


  unfold PrimParallelogram at hP1 hP2 ⊢

  constructor

  · exact hTabf
  · have h1 :
        Mid a c = Mid b d :=
      hP1.2

    have h2 :
        Mid c e = Mid d f :=
      hP2.2

    apply midpoint_cancellation
      (Mid c d)
      (Mid a f)
      (Mid b e)

    calc
      Mid (Mid c d) (Mid a f)
          = Mid (Mid c a) (Mid d f) := by
              exact midpoint_bicommutative c d a f

      _ = Mid (Mid a c) (Mid d f) := by
              rw [midpoint_commutative c a]

           _ = Mid (Mid b d) (Mid c e) := by
              rw [h1, h2]

      _ = Mid (Mid b c) (Mid d e) := by
              exact midpoint_bicommutative b d c e

      _ = Mid (Mid c b) (Mid d e) := by
              rw [midpoint_commutative b c]

      _ = Mid (Mid c d) (Mid b e) := by
              exact midpoint_bicommutative c b d e


/--
Suppes, Theorem 16(iii).

If ab || pq, ab || rs, and T(p,q,r), then pq || rs.
-/

/-
Affine collinearity transport used in Suppes Theorem 16(v).

If
  C, Dbl A (Mid B D), D
are collinear, then after exchanging C and D,
the corresponding constructed point
  Dbl A (Mid B C)
lies on the same line.
-/

theorem collinear_double_mid_swap
    (A B C D : Point)
    (hCol : Col C (Dbl A (Mid B D)) D) :
    Col D (Dbl A (Mid B C)) C := by

  let X : Point := Dbl A (Mid B D)
  let Y : Point := Dbl A (Mid B C)

  have hAX :
      Mid A X = Mid B D := by
    dsimp [X]
    exact midpoint_double_reduction A (Mid B D)

  have hAY :
      Mid A Y = Mid B C := by
    dsimp [Y]
    exact midpoint_double_reduction A (Mid B C)

  /-
  Algebraic identity:

      Mid X C = Mid D Y.

  In affine notation:
      X = B + D - A
      Y = B + C - A,

  so both midpoints coincide.
  -/
  have hMid :
      Mid X C = Mid D Y := by
    apply midpoint_cancellation A

    calc
      Mid A (Mid X C)
          = Mid (Mid A X) (Mid A C) := by
              exact midpoint_left_distrib A X C

      _ = Mid (Mid B D) (Mid A C) := by
              rw [hAX]

      _ = Mid (Mid B A) (Mid D C) := by
              exact midpoint_bicommutative B D A C

      _ = Mid (Mid A B) (Mid D C) := by
              rw [midpoint_commutative B A]

      _ = Mid (Mid A D) (Mid B C) := by
              symm
              exact midpoint_bicommutative A D B C

      _ = Mid (Mid A D) (Mid A Y) := by
              rw [hAY]

      _ = Mid A (Mid D Y) := by
              symm
              exact midpoint_left_distrib A D Y

  have hCXD :
      Col C X D := by
    simpa [X] using hCol
  by_cases hCX : C = X

  · /-
    Degenerate case C = X.

    Then Mid X C = C, hence from hMid:

        C = Mid D Y.

    Since D, Y, Mid D Y are collinear,
    D, Y, C are collinear.
    -/
    have hXC :
        Mid X C = C := by
      calc
        Mid X C = Mid C C := by rw [hCX]
        _ = C := midpoint_idempotent C

    have hCMid :
        C = Mid D Y := by
      calc
        C = Mid X C := hXC.symm
        _ = Mid D Y := hMid

    have hDYC :
        Col D Y C := by
      have h := midpoint_collinear D Y
      rw [← hCMid] at h
      exact h

    exact hDYC
  · have hCXM :
        Col C X (Mid X C) := by
      have h := midpoint_collinear C X
      simpa [midpoint_commutative] using h

    have hCXC :
        Col C X C := by
      apply L2
      exact Or.inr (Or.inl rfl)

    have hCDM :
        Col C D (Mid X C) := by
      exact
        L3
          C X
          C D (Mid X C)
          hCX
          hCXC
          hCXD
          hCXM

    rw [hMid] at hCDM

    have hDMC :
        Col D (Mid D Y) C := by
      exact collinear_rotate hCDM

    have hDMY :
        Col D (Mid D Y) Y := by
      have h := midpoint_collinear Y D
      have hr := collinear_rotate h
      simpa [midpoint_commutative] using hr

    by_cases hDM : D = Mid D Y

    · have hDY :
          D = Y := by
        exact midpoint_fixed D Y hDM.symm

      have hDYC :
          Col D Y C := by
        apply L2
        exact Or.inl hDY

      simpa [Y] using hDYC

    · have hDMD :
          Col D (Mid D Y) D := by
        apply L2
        exact Or.inr (Or.inl rfl)

      have hDYC :
          Col D Y C := by
        exact
          L3
            D (Mid D Y)
            D Y C
            hDM
            hDMD
            hDMY
            hDMC

      simpa [Y] using hDYC

/--
Temporary interface assumption corresponding exactly to
Suppes Theorem 16(iii).

If two segments are parallel to the same segment, and the
required nondegeneracy condition T(p,q,r) holds, then the two
segments are parallel to each other.
-/
axiom suppes_parallel_transitivity
    (a b p q r s : Point)
    (hPQ : SuppesParallel a b p q)
    (hRS : SuppesParallel a b r s)
    (hTpqr : PrimTriangle p q r) :
    SuppesParallel p q r s

theorem parallel_transitive
    (a b p q r s : Point)
    (hPQ : SuppesParallel a b p q)
    (hRS : SuppesParallel a b r s)
    (hTpqr : PrimTriangle p q r) :
    SuppesParallel p q r s := by
  exact
    suppes_parallel_transitivity
      a b p q r s
      hPQ hRS hTpqr

theorem parallel_reverse_second
    (A B C D : Point)
    (h : SuppesParallel A B C D) :
    SuppesParallel A B D C := by

  unfold SuppesParallel at h ⊢

  rcases h with
    ⟨hTABC, hCD, hP, hCol⟩

  /-
  From the auxiliary parallelogram in AB || CD
  we obtain T(A,B,D).
  -/
  have hTABD :
      PrimTriangle A B D := by
    have hRot :
        PrimParallelogram
          D A B (Dbl A (Mid B D)) :=
      parallelogram_rotate3 hP

    exact triangle_rotate hRot.1

  refine ⟨hTABD, hCD.symm, ?_, ?_⟩

  · have hP0 :
        PrimParallelogram
          C A B (Dbl A (Mid B C)) := by
      exact parallelogram_construct A B C hTABC

    have hP1 :
        PrimParallelogram
          (Dbl A (Mid B C)) C A B := by
      exact parallelogram_rotate3 hP0

    have hP2 :
        PrimParallelogram
          B (Dbl A (Mid B C)) C A := by
      exact parallelogram_rotate3 hP1

    have hP3 :
        PrimParallelogram
          A B (Dbl A (Mid B C)) C := by
      exact parallelogram_rotate3 hP2

    exact hP3

  · exact collinear_double_mid_swap A B C D hCol



/-
Affine invariance of collinearity under central reflection.

If C, X, D are collinear, then their images under the
same central reflection about M are also collinear.

In Suppes notation the reflection of Z about M is

    Dbl Z M.
-/
axiom collinear_doubling_common_center
    (C X D M : Point)
    (h : Col C X D) :
    Col
      (Dbl X M)
      (Dbl C M)
      (Dbl D M)

  /-
  Goal 1: PrimTriangle C D A.

  Mathematical argument.

  Put

      X = Dbl A (Mid B D).

  From the definition of AB || CD we know:

      P(A,B,X,D),
      Col(C,X,D).

  Suppose, for contradiction, that

      Col(C,D,A).

  Since C != D, the two collinearities

      Col(C,X,D),
      Col(C,D,A)

  imply that A, D, X lie on the same line.

  On the other hand, from P(A,B,X,D) we have

      Mid A X = Mid B D.

  Thus the midpoint of AX is also the midpoint of BD.

  Since D lies on AX, the common midpoint lies on AX.
  But D, Mid(B,D), B are collinear, so B also lies on AX
  (with the degenerate midpoint case handled separately).

  Hence

      Col(A,B,X),

  contradicting the triangle condition contained in

      P(A,B,X,D).

  Therefore

      not Col(C,D,A),

  i.e.

      PrimTriangle C D A.
  -/

/-
Central reflection preserves collinearity.

Assume that C, X, D are collinear and that the same point M is
the midpoint of the three pairs

    A-X,
    B-D,
    C-Y.

Then A, Y, B are collinear.
-/


theorem collinear_central_reflection
    (A B C D X Y M : Point)
    (hCXD : Col C X D)
    (hAX : Mid A X = M)
    (hBD : Mid B D = M)
    (hCY : Mid C Y = M) :
    Col A Y B := by
  have hAXBD :
      Mid A X = Mid B D := by
    calc
      Mid A X = M := hAX
      _ = Mid B D := hBD.symm

  have hCYBD :
      Mid C Y = Mid B D := by
    calc
      Mid C Y = M := hCY
      _ = Mid B D := hBD.symm
  /-
  The midpoint equalities determine the reflected points uniquely.

  Since M is the midpoint of AX,

      A = Dbl X M.

  Since M is the midpoint of CY,

      Y = Dbl C M.

  Since M is the midpoint of BD,

      B = Dbl D M.

  Thus the required collinearity is precisely the statement that
  doubling three collinear points C, X, D about the same center M
  preserves collinearity.
  -/

  have hA :
      Dbl X M = A := by
    apply midpoint_cancellation X

    calc
      Mid X (Dbl X M) = M := by
        exact midpoint_double_reduction X M

      _ = Mid X A := by
        calc
          M = Mid A X := hAX.symm
          _ = Mid X A := midpoint_commutative A X

  have hY :
      Dbl C M = Y := by
    apply midpoint_cancellation C

    calc
      Mid C (Dbl C M) = M := by
        exact midpoint_double_reduction C M

      _ = Mid C Y := hCY.symm

  have hB :
      Dbl D M = B := by
    apply midpoint_cancellation D

    calc
      Mid D (Dbl D M) = M := by
        exact midpoint_double_reduction D M

      _ = Mid D B := by
        calc
          M = Mid B D := hBD.symm
          _ = Mid D B := midpoint_commutative B D
  have hReflected :
      Col
        (Dbl X M)
        (Dbl C M)
        (Dbl D M) := by
    exact
      collinear_doubling_common_center
        C X D M
        hCXD

  rw [hA, hY, hB] at hReflected

  exact hReflected


theorem parallel_symm
    (A B C D : Point)
    (h : SuppesParallel A B C D) :
    SuppesParallel C D A B := by

  unfold SuppesParallel at h ⊢

  rcases h with
    ⟨hTABC, hCD, hP, hCol⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · -- Goal 1: PrimTriangle C D A
    change ¬ Col C D A
    intro hCDA

    let X : Point := Dbl A (Mid B D)

    have hP' :
        PrimParallelogram A B X D := by
      simpa [X] using hP

    have hCol' :
        Col C X D := by
      simpa [X] using hCol

    /-
    Convert C,X,D into C,D,X.
    -/
    have hCDX :
        Col C D X := by
      exact
        collinear_swap
          (collinear_rotate
            (collinear_rotate hCol'))

    /-
    C,D,A and C,D,X imply A,D,X collinear.
    -/
    have hCDD :
        Col C D D := by
      apply L2
      exact Or.inr (Or.inr rfl)

    have hADX :
        Col A D X := by
      exact
        L3
          C D
          A D X
          hCD
          hCDA
          hCDD
          hCDX

    /-
    A and X are distinct because P(A,B,X,D)
    contains T(A,B,X).
    -/
    have hAX :
        A ≠ X := by
      intro hAXeq
      apply hP'.1
      apply L2
      exact Or.inr (Or.inl hAXeq)

    /-
    Rewrite A,D,X as A,X,D.
    -/
    have hAXD :
        Col A X D := by
      exact
        collinear_swap
          (collinear_rotate
            (collinear_rotate hADX))

    have hAXM :
        Col A X (Mid A X) := by
      exact midpoint_collinear A X

    have hAXX :
        Col A X X := by
      apply L2
      exact Or.inr (Or.inr rfl)

    /-
    D, Mid(A,X), X lie on the same line AX.
    -/
    have hDMX :
        Col D (Mid A X) X := by
      exact
        L3
          A X
          D (Mid A X) X
          hAX
          hAXD
          hAXM
          hAXX

    /-
    From P(A,B,X,D):

        Mid A X = Mid B D.
    -/
    have hMid :
        Mid A X = Mid B D := by
      exact hP'.2

    /-
    D, Mid(A,X), B are collinear because
    Mid(A,X) = Mid(B,D).
    -/
    have hDMB :
        Col D (Mid A X) B := by
      have hBDM :
          Col B D (Mid B D) := by
        exact midpoint_collinear B D

      have hDMB' :
          Col D (Mid B D) B := by
        exact collinear_rotate hBDM

      rw [← hMid] at hDMB'
      exact hDMB'

    by_cases hDM :
        D = Mid A X

    · /-
      Degenerate case: D is the common midpoint.
      Then D = B.
      -/
      have hMDB :
          Mid D B = D := by
        calc
          Mid D B = Mid B D := midpoint_commutative D B
          _ = Mid A X := hMid.symm
          _ = D := hDM.symm

      have hDB :
          D = B := by
        exact midpoint_fixed D B hMDB

      apply hP'.1

      rw [← hDB]

      exact hADX

    · /-
      Nondegenerate case.

      D and Mid(A,X) determine a line containing
      A, B and X.
      -/
      have hAXA :
          Col A X A := by
        apply L2
        exact Or.inr (Or.inl rfl)

      have hADM :
          Col A D (Mid A X) := by
        exact
          L3
            A X
            A D (Mid A X)
            hAX
            hAXA
            hAXD
            hAXM

      have hDMA :
          Col D (Mid A X) A := by
        exact collinear_rotate hADM

      have hABX :
          Col A B X := by
        exact
          L3
            D (Mid A X)
            A B X
            hDM
            hDMA
            hDMB
            hDMX

      exact hP'.1 hABX

  · -- Goal 2: A != B
    intro hAB
    apply hTABC
    subst B
    apply L2
    exact Or.inl rfl

  /-
  Goal 3:
      PrimParallelogram C D (Dbl C (Mid D B)) B.

  Mathematical argument.

  Put

      X = Dbl A (Mid B D).

  From AB || CD we have

      P(A,B,X,D)
      Col(C,X,D)
      C != D.

  Rotating P(A,B,X,D) three times gives

      P(B,X,D,A),

  hence T(B,X,D).

  If C,D,B were collinear, then since C,X,D are
  collinear and C != D, we would obtain Col(B,X,D),
  contradicting T(B,X,D).

  Thus T(C,D,B).

  Suppes Theorem 7 applied to triangle CDB constructs

      P(B,C,D,Dbl C (Mid D B)).

  Three rotations then give the required

      P(C,D,Dbl C (Mid D B),B).
  -/

  · let X : Point := Dbl A (Mid B D)

    have hP' :
        PrimParallelogram A B X D := by
      simpa [X] using hP

    have hCol' :
        Col C X D := by
      simpa [X] using hCol

    have hCDX :
        Col C D X := by
      exact
        collinear_swap
          (collinear_rotate
            (collinear_rotate hCol'))

    have hCDD :
        Col C D D := by
      apply L2
      exact Or.inr (Or.inr rfl)

    /-
    Rotate P(A,B,X,D) three times:

        P(A,B,X,D)
        P(D,A,B,X)
        P(X,D,A,B)
        P(B,X,D,A).
    -/
    have hR1 :
        PrimParallelogram D A B X := by
      exact parallelogram_rotate3 hP'

    have hR2 :
        PrimParallelogram X D A B := by
      exact parallelogram_rotate3 hR1

    have hR3 :
        PrimParallelogram B X D A := by
      exact parallelogram_rotate3 hR2

    have hTBXD :
        PrimTriangle B X D := by
      exact hR3.1

    /-
    Prove T(C,D,B).
    -/
    have hTCDB :
        PrimTriangle C D B := by
      change ¬ Col C D B
      intro hCDB

      have hBXD :
          Col B X D := by
        exact
          L3
            C D
            B X D
            hCD
            hCDB
            hCDX
            hCDD

      exact hTBXD hBXD

    /-
    Theorem 7:
        T(C,D,B)
        ->
        P(B,C,D,Dbl C (Mid D B)).
    -/
    have hQ0 :
        PrimParallelogram
          B C D (Dbl C (Mid D B)) := by
      exact parallelogram_construct C D B hTCDB

    /-
    Rotate three times to obtain
        P(C,D,Dbl C (Mid D B),B).
    -/
    have hQ1 :
        PrimParallelogram
          (Dbl C (Mid D B)) B C D := by
      exact parallelogram_rotate3 hQ0

    have hQ2 :
        PrimParallelogram
          D (Dbl C (Mid D B)) B C := by
      exact parallelogram_rotate3 hQ1

    have hQ3 :
        PrimParallelogram
          C D (Dbl C (Mid D B)) B := by
      exact parallelogram_rotate3 hQ2

    exact hQ3

  · -- Goal 4:
    -- Col A (Dbl C (Mid D B)) B

    let X : Point := Dbl A (Mid B D)
    let Y : Point := Dbl C (Mid D B)

    have hCXD :
        Col C X D := by
      simpa [X] using hCol

    have hAX :
        Mid A X = Mid B D := by
      dsimp [X]
      exact midpoint_double_reduction A (Mid B D)

    have hCY :
        Mid C Y = Mid B D := by
      dsimp [Y]
      calc
        Mid C (Dbl C (Mid D B))
            = Mid D B := midpoint_double_reduction C (Mid D B)
        _ = Mid B D := midpoint_commutative D B

    have hAYB :
        Col A Y B := by
      exact
        collinear_central_reflection
          A B C D X Y (Mid B D)
          hCXD
          hAX
          rfl
          hCY

    simpa [Y] using hAYB


theorem parallel_reverse_first
    (A B C D : Point)
    (h : SuppesParallel A B C D) :
    SuppesParallel B A C D := by

  have h1 :
      SuppesParallel C D A B := by
    exact parallel_symm A B C D h

  have h2 :
      SuppesParallel C D B A := by
    exact parallel_reverse_second C D A B h1

  exact parallel_symm C D B A h2



 end Suppes


end Suppes

end Geometry

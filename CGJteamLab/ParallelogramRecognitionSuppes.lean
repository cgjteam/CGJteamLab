import CGJteamLab.SuppesInterface

namespace Geometry.Suppes

variable {Point : Type*}
variable [SuppesGeometry Point]

local notation "Mid" =>
  SuppesGeometry.operation_midpoint

local notation "Dbl" =>
  SuppesGeometry.operation_double


/-
Temporary affine axiom.

The fourth vertex determined by two pairs of opposite
parallel sides is unique.

If both D and H satisfy

    AB || CD
    BC || AD

and

    AB || CH
    BC || AH

then D = H.
-/
axiom parallel_vertex_unique
    (A B C D H : Point)
    (hAB_CD : SuppesParallel A B C D)
    (hBC_AD : SuppesParallel B C A D)
    (hAB_CH : SuppesParallel A B C H)
    (hBC_AH : SuppesParallel B C A H) :
    D = H


/-
Recognition of a parallelogram from two pairs
of opposite parallel sides.

AB || CD
BC || AD

implies that ABCD is a Suppes parallelogram.
-/
theorem parallelogram_of_opposite_sides_parallel
    (A B C D : Point)
    (hAB_CD : SuppesParallel A B C D)
    (hBC_AD : SuppesParallel B C A D) :
    PrimParallelogram A B C D := by

  /-
  From BC || AD we obtain T(B,C,A).
  -/
  have hT_BCA :
      PrimTriangle B C A := by
    exact hBC_AD.1

  /-
  Suppes Theorem 7 applied to triangle BCA.

  Construct H such that

      P(A,B,C,H).

  Here

      H = Dbl B (Mid C A).
  -/
  let H : Point :=
    Dbl B (Mid C A)

  have hABCH :
      PrimParallelogram A B C H := by
    exact
      parallelogram_construct
        B C A
        hT_BCA

  /-
  From P(A,B,C,H), Suppes Theorem 16(vi) gives

      BC || AH.
  -/
  have hBC_AH :
      SuppesParallel B C A H := by
    exact
      parallelogram_parallel_second
        A B C H
        hABCH

  /-
  Rotate the parallelogram:

      P(A,B,C,H)
          ->
      P(H,A,B,C).
  -/
  have hRot :
      PrimParallelogram H A B C := by
    exact
      parallelogram_rotate3
        hABCH

  /-
  From P(H,A,B,C) obtain

      AB || HC.
  -/
  have hAB_HC :
      SuppesParallel A B H C := by
    exact
      parallelogram_parallel_second
        H A B C
        hRot

  /-
  Suppes Theorem 16(v):

      AB || HC
          ->
      AB || CH.
  -/
  have hAB_CH :
      SuppesParallel A B C H := by
    exact
      parallel_reverse_second
        A B H C
        hAB_HC

  /-
  D and H satisfy the same two parallel conditions:

      AB || CD
      BC || AD

      AB || CH
      BC || AH.

  Hence D = H.
  -/
  have hDH :
      D = H := by
    exact
      parallel_vertex_unique
        A B C D H
        hAB_CD
        hBC_AD
        hAB_CH
        hBC_AH

  /-
  Replace D by H.

  We already know P(A,B,C,H).
  -/
  rw [hDH]

  exact hABCH


end Geometry.Suppes

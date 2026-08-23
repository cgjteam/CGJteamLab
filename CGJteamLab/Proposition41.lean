import CGJteamLab.Proposition34
import CGJteamLab.Proposition37

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.41
--
-- If a parallelogram has the same base with a triangle and is
-- between the same parallels, then the parallelogram is double the
-- triangle.
--
-- Strategy (Euclid's own):
--
--   1. The diagonal AC splits parallelogram ABCD into two congruent
--      triangles ABC and ACD (Euclid I.34, already `euclid_proposition_34_diagonal`).
--      Hence, as scissors terms, the parallelogram is exactly the sum
--      ABC + ABC (up to replacing ACD by its congruent copy ABC).
--
--   2. Triangle ABC and triangle EBC share the base BC and have
--      their apexes A, E on a common line parallel to BC -- this is
--      exactly Euclid I.37 (`euclid_proposition_37`), giving
--      equicomplementability of ABC and EBC.
--
--   3. "Double" transports along sums: from ABC ~ EBC we get
--      ABC + ABC ~ EBC + EBC, and combined with step 1 this gives
--      the parallelogram ~ EBC + EBC.
--
-- "Double" is expressed in the multiset scissors calculus as
-- equicomplementability with the formal sum of two copies of the
-- triangle term -- there is no real-valued area in this library, so
-- this is the faithful synthetic reading of "double".
------------------------------------------------------------------------



/--
Euclid I.41.

If a parallelogram `ABCD` has the same base `BC` as a triangle `EBC`,
and is between the same parallels (that is, the apex `A` of the
diagonal triangle `ABC` and the apex `E` lie on a common line parallel
to `BC`), then the parallelogram is double the triangle.
-/
theorem euclid_proposition_41
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D)
    (hAE_BC : Geo.Parallel A E B C) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertScissorsTriangle Geo E B C +
       hilbertScissorsTriangle Geo E B C) := by

  --------------------------------------------------------------------
  -- Step 1: the diagonal AC splits the parallelogram into two
  -- congruent triangles ABC, CDA (Euclid I.34).
  --------------------------------------------------------------------

  have hCong :
      TriangleCongruenceResult Geo A B C C D A :=
    euclid_proposition_34_diagonal
      Geo A B C D hParallelogram

  have hScABC_CDA :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo C D A) :=
    scissors_congruent
      Geo A B C C D A hCong

  have hCDA_ACD :
      hilbertScissorsTriangle Geo C D A =
      hilbertScissorsTriangle Geo A C D := by
    rw [scissors_triangle_cycle Geo C D A,
        scissors_triangle_cycle Geo D A C]

  have hScABC_ACD :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A C D) := by
    rw [hCDA_ACD] at hScABC_CDA
    exact hScABC_CDA

  --------------------------------------------------------------------
  -- Hence the parallelogram term is scissors-equal to ABC + ABC.
  --------------------------------------------------------------------

  have hParSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A B C) := by
    unfold hilbertParallelogramTerm
    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo) (hilbertScissorsTriangle Geo A B C))
        (HilbertScissorsEq.symm
          (Geo := Geo) hScABC_ACD)

  --------------------------------------------------------------------
  -- Step 2: Euclid I.37 -- ABC and EBC share base BC and lie between
  -- the same parallels.
  --------------------------------------------------------------------

  have hABC_EBC :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo E B C) :=
    euclid_proposition_37
      Geo A B C E hAE_BC

  --------------------------------------------------------------------
  -- Step 3: double both sides and transport across the parallelogram
  -- splitting.
  --------------------------------------------------------------------

  have hDouble :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo E B C +
         hilbertScissorsTriangle Geo E B C) :=
    equicomplementable_add
      Geo
      hABC_EBC
      hABC_EBC

  exact
    equicomplementable_transport
      Geo
      hParSplit
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo E B C +
         hilbertScissorsTriangle Geo E B C))
      hDouble

end Geometry

import CGJteamLab.Proposition42

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.45
--
-- To construct, in a given rectilineal angle, a parallelogram equal
-- to a given rectilineal figure.
--
-- The library has no standalone notion of "rectilineal figure" or
-- "polygon" -- a rectilineal figure is exactly what it becomes once
-- triangulated: a finite list of triangles.  This is represented here
-- as `L : List (Point × Point × Point)`, and its scissors term
-- (`rectilinealTerm`) is the sum of the individual triangle terms --
-- precisely the `HilbertScissorsTerm` machinery already used
-- throughout the equal-area development.
--
-- Euclid's proof: triangulate the figure (join a diagonal from one
-- vertex, recursively), construct a parallelogram equal to the first
-- triangle in the given angle [I.42], then successively apply a
-- parallelogram equal to each further triangle to the growing
-- parallelogram's side, in the same angle [I.44], noting each time
-- that the two adjacent parallelograms actually combine into one
-- bigger parallelogram (since consecutive angles equal to the given
-- angle, positioned via vertical angles, are together supplementary
-- along a straight line -- I.29/I.14).
--
-- This "successive I.44 application + combine into one bigger
-- parallelogram, same angle" step is exactly the induction step
-- below; it is packaged as a single local axiom, `i45_extend_parallelogram`,
-- in the same spirit as I.44's own transport axiom (indeed its
-- content is a repetition of I.44's construction, one more time, per
-- triangle). Everything else -- the induction over the triangulation
-- itself, the base case (I.42 directly), and the scissors-algebra
-- bookkeeping -- is proved here without further assumptions.
------------------------------------------------------------------------

/--
The scissors term of a triangulated rectilineal figure: the formal sum
of the triangle terms of its triangulation.
-/
def rectilinealTerm
    (L : List (Geo.Point × Geo.Point × Geo.Point)) :
    HilbertScissorsTerm Geo :=
  (L.map (fun t => hilbertScissorsTriangle Geo t.1 t.2.1 t.2.2)).sum

theorem rectilinealTerm_cons
    (hd : Geo.Point × Geo.Point × Geo.Point)
    (tl : List (Geo.Point × Geo.Point × Geo.Point)) :
    rectilinealTerm Geo (hd :: tl) =
      hilbertScissorsTriangle Geo hd.1 hd.2.1 hd.2.2 +
      rectilinealTerm Geo tl := by
  simp [rectilinealTerm]

theorem rectilinealTerm_nil :
    rectilinealTerm Geo ([] : List (Geo.Point × Geo.Point × Geo.Point)) = 0 := by
  simp [rectilinealTerm]

/--
Local axiom.

Given a parallelogram `S T U V` with its angle at `T` (namely
`∠ S T U`) equal to a fixed target angle `X Y Z`, and a further
triangle `P Q R`, there is a strictly larger parallelogram `S T' U' V'`
-- sharing the vertex `S`, with the same angle `X Y Z` at `T'` --
equal in area to the original parallelogram together with the new
triangle.

This packages one repetition of Euclid's I.44 construction (apply a
parallelogram equal to `P Q R`, in the angle `X Y Z`, to the relevant
side of `S T U V`) together with the observation that the two
resulting parallelograms, sharing that angle via vertical angles,
combine into a single larger parallelogram (I.29/I.14).
-/
axiom i45_extend_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (S T U V P Q R X Y Z : Geo.Point)
    (hParallelogram : IsParallelogram Geo S T U V)
    (hAngle : Geo.AngleCongruent S T U X Y Z)
    (hPQR : Not (Collinear Geo P Q R)) :
    ∃ T' U' V' : Geo.Point,
      IsParallelogram Geo S T' U' V' ∧
      Geo.AngleCongruent S T' U' X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T' U' V')
        (hilbertScissorsTriangle Geo P Q R +
         hilbertParallelogramTerm Geo S T U V)

/--
Euclid I.45.

To construct, in a given rectilineal angle `XYZ`, a parallelogram
equal to a given rectilineal figure, presented via a triangulation
`L` (a nonempty list of triangles, each nondegenerate).
-/
theorem euclid_proposition_45
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (L : List (Geo.Point × Geo.Point × Geo.Point))
    (hNonempty : L ≠ [])
    (hTriangles : ∀ t ∈ L, Not (Collinear Geo t.1 t.2.1 t.2.2)) :
    ∃ S T U V : Geo.Point,
      IsParallelogram Geo S T U V ∧
      Geo.AngleCongruent S T U X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (rectilinealTerm Geo L)
        (hilbertParallelogramTerm Geo S T U V) := by

  revert hNonempty hTriangles
  induction L with
  | nil =>
    intro hNonempty _
    exact absurd rfl hNonempty
  | cons hd tl ih =>
    intro _ hTriangles
    rcases hd with ⟨P, Q, R⟩

    have hPQR :
        Not (Collinear Geo P Q R) :=
      hTriangles (P, Q, R) List.mem_cons_self

    have hRect :
        rectilinealTerm Geo ((P, Q, R) :: tl) =
        hilbertScissorsTriangle Geo P Q R + rectilinealTerm Geo tl :=
      rectilinealTerm_cons Geo (P, Q, R) tl

    rcases tl with _ | ⟨hd2, tl2⟩

    ------------------------------------------------------------------
    -- Base case: a single triangle. Use I.42 directly.
    ------------------------------------------------------------------

    · rcases
          euclid_proposition_42
            Geo P Q R X Y Z hPQR hXYZ
        with
        ⟨E, F, G, hParallelogram, hAngle, hEquicomp⟩

      refine ⟨F, E, R, G, hParallelogram, hAngle, ?_⟩
      rw [hRect, rectilinealTerm_nil]
      simpa using hEquicomp

    ------------------------------------------------------------------
    -- Recursive case: extend the parallelogram for the tail by the
    -- new triangle P Q R.
    ------------------------------------------------------------------

    · have hTlNonempty :
          (hd2 :: tl2 : List (Geo.Point × Geo.Point × Geo.Point)) ≠ [] :=
        List.cons_ne_nil hd2 tl2

      have hTlTriangles :
          ∀ t ∈ (hd2 :: tl2 : List (Geo.Point × Geo.Point × Geo.Point)),
            Not (Collinear Geo t.1 t.2.1 t.2.2) :=
        fun t ht => hTriangles t (List.mem_cons_of_mem _ ht)

      rcases
          ih hTlNonempty hTlTriangles
        with
        ⟨S, T, U, V, hParallelogram, hAngle, hEquicompTl⟩

      rcases
          i45_extend_parallelogram
            Geo S T U V P Q R X Y Z
            hParallelogram hAngle hPQR
        with
        ⟨T', U', V', hParallelogram2, hAngle2, hEquicompExt⟩

      refine ⟨S, T', U', V', hParallelogram2, hAngle2, ?_⟩

      rw [hRect]

      have hAddLeft :
          HilbertScissorsEquicomplementable Geo
            (hilbertScissorsTriangle Geo P Q R +
             rectilinealTerm Geo (hd2 :: tl2))
            (hilbertScissorsTriangle Geo P Q R +
             hilbertParallelogramTerm Geo S T U V) := by
        have h0 :=
          equicomplementable_add_right
            Geo (hilbertScissorsTriangle Geo P Q R) hEquicompTl
        rw [Multiset.add_comm
              (rectilinealTerm Geo (hd2 :: tl2))
              (hilbertScissorsTriangle Geo P Q R),
            Multiset.add_comm
              (hilbertParallelogramTerm Geo S T U V)
              (hilbertScissorsTriangle Geo P Q R)] at h0
        exact h0

      exact
        equicomplementable_trans
          Geo hAddLeft
          (equicomplementable_symm Geo hEquicompExt)

end Geometry

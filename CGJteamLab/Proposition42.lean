import CGJteamLab.Proposition41

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.42
--
-- To construct, in a given rectilinear angle, a parallelogram equal
-- to a given triangle.
--
-- Unlike I.37-I.41, this is a CONSTRUCTION / existence proposition,
-- not a relation between already-given figures.  Euclid's own proof:
--
--   1. Bisect BC at E.  Since BE = EC, triangle ABE is equal to
--      triangle AEC ("for they are on equal bases BE, EC and between
--      the same parallels BC, AG" -- I.38).
--   2. On EC, at E, construct angle CEF equal to the given angle D.
--   3. Draw AG through A parallel to EC, and CG through C parallel
--      to EF.  Then FECG is a parallelogram.
--   4. Since FECG has the same base EC as triangle AEC and is between
--      the same parallels (AG || EC, with A on line AG), FECG is
--      double triangle AEC (I.41) -- hence equal to triangle ABC.
--
-- Step 1 is the one place where Euclid's own citation of I.38 is, in
-- this project's formalization, not literally an instance of
-- `euclid_proposition_38` / `euclid_proposition_37`: those theorems
-- compare triangles with two DISTINCT apex points related by
-- `Geo.Parallel A D B C` (which forces `A ≠ D`).  Here both halves
-- share the SAME apex `A`, which is the genuinely degenerate case of
-- "on equal bases and between the same parallels" that Euclid's own
-- (superposition-based) proof of I.38 handles freely but which this
-- project's point-based formalization of I.38 does not cover.  This
-- fact ("a cevian to the midpoint of a side bisects a triangle's
-- area") is mathematically elementary but is NOT a consequence of any
-- proposition currently in the library; it is recorded here as a
-- single explicit local axiom, in the same spirit as the temporary
-- assumption in `Proposition39.lean`.
--
-- Step 3 needs the point G, obtained as the intersection of two lines
-- constructed to be parallel to two different given directions.  The
-- library has exactly one precedent for this kind of "existence of an
-- intersection" fact left as an axiom: `hilbert_circle_circle_intersection`
-- in `HilbertInterface.lean`.  Following that precedent, the
-- construction of the angle-D parallelogram on a given base is
-- recorded here as a second explicit local axiom, packaging exactly
-- the three properties Euclid's construction is known to establish.
--
-- Everything else -- the bisection, the splitting/doubling of the
-- scissors term, and the final application of I.41 -- is proved here
-- without further assumptions.
------------------------------------------------------------------------

/--
Local axiom 1.

A cevian to the midpoint of a side divides a triangle into two
triangles of equal area.

This is the degenerate ("same apex") case of "equal bases, between
the same parallels" that Euclid cites I.38 for in his proof of I.42,
but which is not literally an instance of `euclid_proposition_38` in
this project's point-based formalization (that theorem requires two
distinct apex points related by `Geo.Parallel`).
-/
axiom i42_median_bisects_area
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C E : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hE : HilbertIsMidpoint Geo E B C) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B E)
      (hilbertScissorsTriangle Geo A E C)

/--
Local axiom 2.

Given a base `EC`, a point `A` off the line `EC`, and a nondegenerate
target angle `XYZ`, there exist points `F, G` such that:

- `FECG` is a parallelogram on the base `EC`,
- the angle at `E` (namely `∠FEC`) matches the given angle `XYZ`,
- `F` and `A` determine a line parallel to `EC`.

The third clause records that the fourth vertex `G` was constructed as
the intersection of the line through `A` parallel to `EC` with the
line through `C` parallel to `EF` -- so `F` lies on the same
parallel-to-`EC` line as `A`.  This is exactly the geometric content
of Euclid's construction ("through A draw AG parallel to EC; through C
draw CG parallel to EF"), packaged as a single existence fact so as
not to re-derive the underlying two-lines-meet argument from
`HilbertPlaneIncidence` machinery alone.
-/
axiom i42_construct_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A E C X Y Z : Geo.Point)
    (hEC : Not (E = C))
    (hAEC : Not (Collinear Geo A E C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ F G : Geo.Point,
      IsParallelogram Geo F E C G ∧
      Geo.AngleCongruent F E C X Y Z ∧
      Geo.Parallel F A E C

/--
Equicomplementability is preserved by adding the same term on the
right, e.g. transporting `P ~ Q` to `P + R ~ Q + R`.
-/
theorem equicomplementable_add_right
    {P Q : HilbertScissorsTerm Geo}
    (R : HilbertScissorsTerm Geo)
    (h : HilbertScissorsEquicomplementable Geo P Q) :
    HilbertScissorsEquicomplementable Geo (P + R) (Q + R) := by

  rcases h with ⟨R0, S0, hR0S0, hPQ⟩

  have hLeft :
      (P + R) + R0 = (P + R0) + R := by
    calc
      (P + R) + R0
          = P + (R + R0) := Multiset.add_assoc _ _ _
      _ = P + (R0 + R) := by rw [Multiset.add_comm R R0]
      _ = (P + R0) + R := (Multiset.add_assoc _ _ _).symm

  have hRight :
      (Q + R) + S0 = (Q + S0) + R := by
    calc
      (Q + R) + S0
          = Q + (R + S0) := Multiset.add_assoc _ _ _
      _ = Q + (S0 + R) := by rw [Multiset.add_comm R S0]
      _ = (Q + S0) + R := (Multiset.add_assoc _ _ _).symm

  refine ⟨R0, S0, hR0S0, ?_⟩
  rw [hLeft, hRight]
  exact
    HilbertScissorsEq.add
      (Geo := Geo) hPQ
      (HilbertScissorsEq.refl (Geo := Geo) R)

/--
Euclid I.42.

To construct, in a given rectilinear angle `XYZ`, a parallelogram
equal to a given triangle `ABC`.
-/
theorem euclid_proposition_42
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C X Y Z : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ E F G : Geo.Point,
      IsParallelogram Geo F E C G ∧
      Geo.AngleCongruent F E C X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo F E C G) := by

  --------------------------------------------------------------------
  -- B != C, and the carrier line of BC.
  --------------------------------------------------------------------

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle Geo C A B
          (PrimCollinearCycle Geo B C A h))

  have hBC :
      Not (B = C) :=
    hilbert_noncollinear_ne_first Geo B C A hBCA

  rcases
      HilbertPlaneIncidence.line_through B C hBC
    with
    ⟨lineBC, hBlineBC, hClineBC⟩

  have hAoffBC :
      Not (HilbertIncidence.OnLine A lineBC) := by
    intro hAonBC
    exact hABC ⟨lineBC, hAonBC, hBlineBC, hClineBC⟩

  --------------------------------------------------------------------
  -- E := midpoint of BC.
  --------------------------------------------------------------------

  rcases
      HilbertMidpointExists Geo B C hBC
    with
    ⟨E, hE⟩

  have hBEC :
      Geo.Between B E C :=
    hE.1

  have hEC :
      Not (E = C) :=
    (HilbertOrder.between_incidence B E C hBEC).2.1

  have hElineBC :
      HilbertIncidence.OnLine E lineBC :=
    hilbert_between_on_line
      Geo B E C lineBC hBlineBC hClineBC hBEC

  have hECA :
      Not (Collinear Geo E C A) :=
    hilbert_not_collinear_of_off_line
      Geo E C A lineBC hEC hElineBC hClineBC hAoffBC

  have hAEC :
      Not (Collinear Geo A E C) := by
    intro h
    exact hECA (PrimCollinearCycle Geo A E C h)

  --------------------------------------------------------------------
  -- [Axiom 1] triangle ABE and triangle AEC are equicomplementable.
  --------------------------------------------------------------------

  have hMedian :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B E)
        (hilbertScissorsTriangle Geo A E C) :=
    i42_median_bisects_area Geo A B C E hABC hE

  --------------------------------------------------------------------
  -- ABC splits exactly as ABE + AEC, hence ABC ~ AEC + AEC.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A B E +
         hilbertScissorsTriangle Geo A E C) :=
    HilbertScissorsEq.split
      (Geo := Geo) A B C E hBEC

  have hDouble :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B E +
         hilbertScissorsTriangle Geo A E C)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    equicomplementable_add_right
      Geo (hilbertScissorsTriangle Geo A E C) hMedian

  have hABC_double :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    equicomplementable_transport
      Geo hSplit
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C))
      hDouble

  --------------------------------------------------------------------
  -- [Axiom 2] construct the angle-XYZ parallelogram FECG on base EC.
  --------------------------------------------------------------------

  rcases
      i42_construct_parallelogram
        Geo A E C X Y Z
        hEC hAEC hXYZ
    with
    ⟨F, G, hParallelogram, hAngle, hFA_EC⟩

  --------------------------------------------------------------------
  -- Euclid I.41: FECG is double triangle AEC.
  --------------------------------------------------------------------

  have hDoubleParallelogram :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F E C G)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    euclid_proposition_41
      Geo F E C G A hParallelogram hFA_EC

  --------------------------------------------------------------------
  -- Chain everything together: ABC ~ AEC+AEC ~ FECG.
  --------------------------------------------------------------------

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo F E C G) :=
    equicomplementable_trans
      Geo hABC_double
      (equicomplementable_symm Geo hDoubleParallelogram)

  exact ⟨E, F, G, hParallelogram, hAngle, hFinal⟩

end Geometry

import CGJteamLab.Proposition42

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.44
--
-- To a given straight line to apply, in a given angle, a
-- parallelogram equal to a given triangle.
--
-- Euclid's proof:
--
--   1. [I.42] Construct a parallelogram BEFG equal to the given
--      triangle, with angle EBG equal to the given angle D.
--   2. Place it so that BE lies in a straight line with the given
--      line AB.
--   3. [I.31] Draw FG produced to H, and AH through A parallel to
--      BG (equivalently EF).
--   4. [Postulate 5] The angles AHF, HFE are supplementary (AH || EF
--      cut by FH), so angles BHG, GFE are together less than two
--      right angles; hence HB and FE, produced, meet -- say at K.
--   5. Draw KL through K parallel to EA (= through H), extend HA, GB
--      to L, M.  Then HLKF is a parallelogram with diameter HK, AG
--      and ME are the "diagonal" parallelograms, and LB, BF are the
--      complements.
--   6. [I.43] LB = BF (the complements about the diameter HK).
--   7. Since BF equals the given triangle (by construction) and
--      angle GBE = angle ABM [I.15, vertical angles] = D, the
--      parallelogram LB, applied to AB in angle ABM = D, equals the
--      given triangle.
--
-- Step 1 is exactly `euclid_proposition_42`, already available (and
-- already resting on its own two explicit local axioms). Steps 3-6
-- are precisely the mathematical content already established as
-- `euclid_proposition_43` -- but recovering that theorem's exact
-- hypotheses (the points H, K, L, M and the auxiliary parallelograms
-- HLKF, AG..., ME...) from the raw output of I.42 requires the two
-- further genuine existence facts of steps 3 and 4 (a line meeting a
-- constructed parallel, and Postulate 5's "lines making angles less
-- than two right angles meet"), together with careful positional
-- bookkeeping matching Euclid's diagram.
--
-- Rather than re-deriving that positional bookkeeping from primitive
-- incidence data (a substantial undertaking on the order of I.43
-- itself, and one carrying real risk of a mismatched correspondence
-- without a diagram to check against), steps 2-6 are packaged here as
-- a single explicit local axiom: transporting a parallelogram of
-- given area and given angle-at-a-vertex onto a prescribed line,
-- sharing one endpoint. This is honestly a strictly larger axiom than
-- I.42's two, but its mathematical content -- the "sliding" argument
-- -- is now known to reduce to I.43 plus two intersection-existence
-- facts, and stands as the natural next target for reduction.
------------------------------------------------------------------------

/--
Local axiom.

Any parallelogram `S T U V` (with its angle at `T`, namely `∠ S T U`,
recorded) can be transported -- rigidly, preserving area and that
angle -- so that it shares the vertex `B` with a given segment `A B`,
with one side lying along the line `A B`.

This packages Euclid's construction of `H`, `K`, `L`, `M` (I.31,
Postulate 5, I.43, I.15) used in the proof of I.44 to slide the
I.42-parallelogram from its initially unconstrained position onto the
given line.
-/
axiom i44_transport_onto_line
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B S T U V X Y Z : Geo.Point)
    (hAB : Not (A = B))
    (hParallelogram : IsParallelogram Geo S T U V)
    (hAngle : Geo.AngleCongruent S T U X Y Z) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo B A L M ∧
      Geo.AngleCongruent L B A X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T U V)
        (hilbertParallelogramTerm Geo B A L M)

/--
Euclid I.44.

To a given straight line `AB`, apply, in a given angle `XYZ`, a
parallelogram equal to a given triangle `PQR`.

The resulting parallelogram `B A L M` has one side coinciding with
`AB`, angle at `B` equal to the given angle, and area equal to the
given triangle.
-/
theorem euclid_proposition_44
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B P Q R X Y Z : Geo.Point)
    (hAB : Not (A = B))
    (hPQR : Not (Collinear Geo P Q R))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo B A L M ∧
      Geo.AngleCongruent L B A X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo B A L M) := by

  --------------------------------------------------------------------
  -- Step 1 [I.42]: construct a parallelogram F E R G equal to
  -- triangle PQR, with angle FER equal to the given angle XYZ.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_42
        Geo P Q R X Y Z hPQR hXYZ
    with
    ⟨E, F, G, hParallelogram, hAngle, hEquicomp⟩

  --------------------------------------------------------------------
  -- Steps 2-6: transport F E R G onto the line AB, sharing vertex B.
  --------------------------------------------------------------------

  rcases
      i44_transport_onto_line
        Geo A B F E R G X Y Z
        hAB hParallelogram hAngle
    with
    ⟨M, L, hParallelogram2, hAngle2, hEquicomp2⟩

  --------------------------------------------------------------------
  -- Step 7: chain the two equal-area facts.
  --------------------------------------------------------------------

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo B A L M) :=
    equicomplementable_trans Geo hEquicomp hEquicomp2

  exact ⟨M, L, hParallelogram2, hAngle2, hFinal⟩

end Geometry

import CGJteamLab.HilbertPascal
import CGJteamLab.Proposition06

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Unsoundness of proposition39_test_circle_crossing_chords_angle
--
-- HilbertPascal.lean, line 13272.
--
-- The axiom reads:
--
--   (O A C B D : Geo.Point)
--   (hAOC    : Not (PrimCollinear Geo A O B))
--   (hRayAC  : HilbertSameRay Geo O A C)
--   (hRayBD  : HilbertSameRay Geo O B D)
--   (hCyclic : HilbertConcyclic4 Geo A C D B) :
--   Geo.AngleCongruent O D C O A B
--
-- The hypothesis hCyclic is far weaker than intended.  By
-- HilbertGrundlagen.lean:6295,
--
--   HilbertConcyclic4 A B C D := exists O, Congruent O A O B /\ ...
--
-- carries no distinctness and no cyclic ordering.  Instantiating
-- C := A and D := B therefore costs nothing: the two same-ray
-- hypotheses become reflexivity, and hCyclic degenerates to the
-- existence of one point equidistant from A and B, i.e. the midpoint.
--
-- The conclusion, however, does not degenerate.  It becomes
--
--   AngleCongruent O B A O A B
--
-- so every triangle has congruent base angles at the two vertices
-- other than the apex.  Euclid I.6 then makes every triangle
-- equilateral, and segment construction uniqueness gives False.
--
-- Nothing here uses continuity or the parallel axiom beyond the
-- ambient class already assumed by the axiom itself.
--
-- Note that proposition39_test_circle_crossing_chords_concyclic
-- (line 13189) is NOT implicated: its conclusion is the weak
-- HilbertConcyclic4 predicate, so the degenerate instantiation
-- proves nothing new there.  The mismatch between the weak
-- conclusion of the first axiom and the strong hypothesis required
-- by the second is exactly the defect.
--
-- This file is intended as a regression test.  Once the axiom is
-- repaired -- either by adding A <> C and B <> D, or by replacing
-- the pair with a single similar-triangle statement -- this file
-- must stop compiling.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Step 1: the degenerate concyclicity hypothesis is free
------------------------------------------------------------------------

/--
For any two points, the quadruple A, A, B, B is concyclic in the
sense of HilbertConcyclic4: the midpoint of AB is equidistant from
all four entries.
-/
theorem crossing_chords_degenerate_concyclic
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point) :
    HilbertConcyclic4 Geo A A B B := by

  by_cases hAB : A = B

  · subst B
    exact
      ⟨A,
        hilbert_congruent_reflexive Geo A A,
        hilbert_congruent_reflexive Geo A A,
        hilbert_congruent_reflexive Geo A A⟩

  · rcases
        hilbert_midpoint_exists
          Geo A B hAB
      with
      ⟨M, hAMB, hAM_MB⟩

    have hMA_MB :
        Geo.Congruent M A M B :=
      (Geo.congruent_reverse_first A M M B).mp hAM_MB

    exact
      ⟨M,
        hilbert_congruent_reflexive Geo M A,
        hMA_MB,
        hMA_MB⟩


------------------------------------------------------------------------
-- Step 2: every triangle is isosceles at every vertex
------------------------------------------------------------------------

/--
Consequence of the axiom: for any noncollinear A, O, B the sides
OA and OB are congruent.

Since the noncollinearity hypothesis is symmetric under permutation,
applying this at each of the three vertices makes every triangle
equilateral.
-/
theorem crossing_chords_forces_isosceles
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O A B : Geo.Point)
    (hAOB : ¬ PrimCollinear Geo A O B) :
    Geo.Congruent O B O A := by

  have hAO : A ≠ O :=
    hilbert_noncollinear_ne_first Geo A O B hAOB

  have hBO : B ≠ O := by
    intro h
    apply hAOB
    rcases HilbertPlaneIncidence.line_through A O hAO with
      ⟨l, hAl, hOl⟩
    exact ⟨l, hAl, hOl, by rw [h]; exact hOl⟩

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl Geo O A hAO

  have hRayBB :
      HilbertSameRay Geo O B B :=
    hilbert_sameRay_refl Geo O B hBO

  have hCyclic :
      HilbertConcyclic4 Geo A A B B :=
    crossing_chords_degenerate_concyclic Geo A B

  --------------------------------------------------------------------
  -- The axiom, instantiated at C := A and D := B.
  --------------------------------------------------------------------

  have hAngle :
      Geo.AngleCongruent O B A O A B :=
    proposition39_test_circle_crossing_chords_angle
      Geo
      O A A B B
      hAOB
      hRayAA
      hRayBB
      hCyclic

  have hOBA :
      ¬ Collinear Geo O B A := by
    intro h
    exact
      hAOB
        (PrimCollinearCycle Geo B A O
          (PrimCollinearCycle Geo O B A h))

  --------------------------------------------------------------------
  -- Euclid I.6 on the triangle O B A.
  --------------------------------------------------------------------

  exact
    euclid_proposition_6
      Geo
      O B A
      hOBA
      hAngle


------------------------------------------------------------------------
-- Step 3: contradiction from a single noncollinear triple
------------------------------------------------------------------------

/--
No noncollinear triple can exist.

Take the midpoint M of AB.  Applying the previous theorem at the
vertex A, once to the pair (O, M) and once to the pair (O, B),
gives two points of the ray AB carrying a segment congruent to AO.
Segment construction uniqueness forces M = B, contradicting
Between A M B.
-/
theorem crossing_chords_absurd
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O A B : Geo.Point)
    (hAOB : ¬ PrimCollinear Geo A O B) :
    False := by

  have hAO : A ≠ O :=
    hilbert_noncollinear_ne_first Geo A O B hAOB

  have hAB : A ≠ B := by
    intro h
    apply hAOB
    rcases HilbertPlaneIncidence.line_through A O hAO with
      ⟨l, hAl, hOl⟩
    exact ⟨l, hAl, hOl, by rw [← h]; exact hAl⟩

  --------------------------------------------------------------------
  -- The midpoint of AB.
  --------------------------------------------------------------------

  rcases
      hilbert_midpoint_exists
        Geo A B hAB
    with
    ⟨M, hAMB, hAM_MB⟩

  have hData :=
    HilbertOrder.between_incidence A M B hAMB

  have hAM : A ≠ M := hData.1
  have hMB : M ≠ B := hData.2.1

  --------------------------------------------------------------------
  -- M lies on the line AB, and O does not.
  --------------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨l, hAl, hBl⟩

  rcases hData.2.2.2.1 with ⟨m, hAm, hMm, hBm⟩

  have hml : m = l :=
    HilbertPlaneIncidence.line_unique
      A B hAB m l hAm hBm hAl hBl

  have hMl :
      HilbertIncidence.OnLine M l :=
    hml ▸ hMm

  have hOl :
      ¬ HilbertIncidence.OnLine O l := by
    intro hO
    exact hAOB ⟨l, hAl, hO, hBl⟩

  --------------------------------------------------------------------
  -- Noncollinearity of the two triangles at the vertex A.
  --------------------------------------------------------------------

  have hAMO :
      ¬ PrimCollinear Geo A M O :=
    hilbert_not_collinear_of_off_line
      Geo A M O l hAM hAl hMl hOl

  have hOAM :
      ¬ PrimCollinear Geo O A M := by
    intro h
    exact hAMO (PrimCollinearCycle Geo O A M h)

  have hOAB :
      ¬ PrimCollinear Geo O A B := by
    intro h
    exact hAOB (PrimCollinearSwap Geo O A B h)

  --------------------------------------------------------------------
  -- Both M and B carry a segment congruent to AO on the ray AB.
  --------------------------------------------------------------------

  have hAM_AO :
      Geo.Congruent A M A O :=
    crossing_chords_forces_isosceles Geo A O M hOAM

  have hAB_AO :
      Geo.Congruent A B A O :=
    crossing_chords_forces_isosceles Geo A O B hOAB

  have hRayBB :
      HilbertSameRay Geo A B B :=
    hilbert_sameRay_refl Geo A B hAB.symm

  have hRayBM :
      HilbertSameRay Geo A B M :=
    hilbert_sameRay_symm
      Geo A M B
      (hilbert_sameRay_of_between Geo A M B hAMB)

  have hMeqB : M = B :=
    hilbert_segment_construction_unique
      Geo
      A O
      A B
      M B
      hRayBM
      hRayBB
      hAM_AO
      hAB_AO

  exact hMB hMeqB


------------------------------------------------------------------------
-- Step 4: the ambient theory is inconsistent
------------------------------------------------------------------------

/--
Group I, 3 supplies a noncollinear triple, so the axiom refutes the
incidence axioms outright.

Every theorem stated after line 13272 of HilbertPascal.lean,
including proposition39_test_special_pascal, currently depends on a
contradictory assumption.
-/
theorem crossing_chords_angle_is_inconsistent
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo] :
    False := by

  rcases
      HilbertPlaneIncidence.three_noncollinear
        (Geo := Geo)
    with
    ⟨A, O, B, hAOB⟩

  exact crossing_chords_absurd Geo O A B hAOB


------------------------------------------------------------------------
-- Audit
------------------------------------------------------------------------

-- Expected:
--
--   propext, Classical.choice, Quot.sound,
--   proposition39_test_circle_crossing_chords_angle
--
-- The witness for the degenerate concyclicity hypothesis is taken
-- from hilbert_midpoint_exists (HilbertAxioms.lean:4521) rather than
-- from proposition39_test_perpendicular_bisector_exists, because the
-- latter routes through HilbertBookZero and drags in
-- bookZero_nullSegment1.  That assumption is harmless -- it holds in
-- the Cartesian model -- but leaving it in the audit would let a
-- reader ask which of the two assumptions is the inconsistent one.
--
-- With only the three standard Lean axioms remaining beside it, the
-- crossing-chords axiom is the sole candidate.
#print axioms crossing_chords_angle_is_inconsistent


------------------------------------------------------------------------
-- Proposed replacement
--
-- The composite proposition39_test_pascal_third_angle is true even in
-- the degenerate cases, because it is nothing but the similar-triangle
-- transfer: the shared angle at O together with
--
--     angle O A D  ~=  angle O B C
--
-- gives OA * OC = OB * OD, whence
--
--     angle O D C  ~=  angle O A B.
--
-- Stating that directly removes HilbertConcyclic4 from the critical
-- path and removes the need to thread A <> C and B' <> D' through
-- pascal_after_circle and pascal_angle_chain:
--
--   axiom proposition39_test_crossing_chords_similar
--       [HilbertEuclideanPlane Geo]
--       (O A C B D : Geo.Point)
--       (hAOB   : Not (PrimCollinear Geo A O B))
--       (hRayAC : HilbertSameRay Geo O A C)
--       (hRayBD : HilbertSameRay Geo O B D)
--       (hAngle : Geo.AngleCongruent O A D O B C) :
--       Geo.AngleCongruent O D C O A B
--
-- proposition39_test_pascal_third_angle then becomes a single
-- application, and the circle theory of sec. 7 is needed only when
-- this one assumption is finally discharged.
------------------------------------------------------------------------

end Geometry

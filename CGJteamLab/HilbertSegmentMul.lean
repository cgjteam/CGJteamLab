/-
HilbertSegmentMul.lean -- SKELETON

Every declaration below is stated but not proved.  The file is not
meant to be reachable from the build root until the `sorry`s are
discharged; add it to CGJteamLab.lean only at that point.

Purpose: close the last assumption of Euclid I.39,

    hilbert_scissors_triangle_positive
      (HilbertScissorsPositivity.lean)

by constructing the area valuation of Hilbert, Foundations sec. 20,
equivalently Hartshorne, Theorem 23.2.

Each block is tagged

    [ELEM]    provable from Groups I-III, the parallel axiom, and the
              segment arithmetic already in HilbertSegmentArithmetic
    [PASCAL]  needs proposition39_test_special_pascal
              (HilbertPascal.lean:15745), i.e. Hilbert sec. 14

The tags are the point of this file: only four statements are
[PASCAL], and all four are about multiplication, none about the
geometry of triangles.
-/

import CGJteamLab.HilbertSegmentArithmetic
import CGJteamLab.HilbertScissorsInvariant
import CGJteamLab.Proposition16
import CGJteamLab.Proposition29
import CGJteamLab.Proposition32

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Part 0.  A unit segment
------------------------------------------------------------------------

/--
An arbitrary but fixed positive segment class, used as the unit of
multiplication.

Nothing depends on the choice: a different unit rescales every area by
a fixed factor, and positivity is unaffected.
-/
noncomputable def hilbertUnitSegment
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    HilbertPositiveSegmentClass Geo := by

  let h :=
    HilbertPlaneIncidence.two_points_on_line
      (Geo := Geo)

  let l : Geo.Line :=
    Classical.choose h

  have hl :
      ∃ A B : Geo.Point,
        A ≠ B ∧
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l :=
    Classical.choose_spec h

  let A : Geo.Point :=
    Classical.choose hl

  have hA :
      ∃ B : Geo.Point,
        A ≠ B ∧
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l :=
    Classical.choose_spec hl

  let B : Geo.Point :=
    Classical.choose hA

  have hB :
      A ≠ B ∧
      HilbertIncidence.OnLine A l ∧
      HilbertIncidence.OnLine B l :=
    Classical.choose_spec hA

  exact
    hilbertPositiveSegmentClassOf
      Geo A B hB.1


------------------------------------------------------------------------
-- Part 1.  Multiplication
--
-- Hilbert sec. 15.  In the language of the ratio witnesses already
-- present in HilbertSegmentArithmetic, the product a * b is the unique
-- x with
--
--     1 : a  =  b : x.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Part 0a-bis.  Angle subtraction and the right-triangle third angle
--
-- Isolated for Case 2 of `hilbertPositiveSegmentProportion_fourth_exists`
-- below.  `hilbert_angle_subtract` is Euclid's third common notion for
-- angles ("equals subtracted from equals are equal"); it is a standard,
-- believable fact but is not yet proved here.  Everything else in this
-- block (`hilbert_right_triangle_third_angle_congruent`) is a real
-- proof built on top of it and on already-verified library lemmas
-- (`euclid_proposition_32_exterior`, `hilbert_adjacent_angles_congruent`,
-- `hilbert_all_right_angles_congruent`).
------------------------------------------------------------------------

/--
Right-angle-ness transports along an angle congruence.
-/
theorem hilbert_right_angle_of_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B A' O' B' : Geo.Point)
    (hNoncol : ¬ PrimCollinear Geo A O B)
    (hNoncol' : ¬ PrimCollinear Geo A' O' B')
    (hCong : Geo.AngleCongruent A O B A' O' B')
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A' O' B' := by

  rcases hRight with ⟨C, hAOC, hRightCong⟩

  have hA'O' : A' ≠ O' := hilbert_noncollinear_ne_first Geo A' O' B' hNoncol'

  obtain ⟨C', hA'O'C'⟩ := HilbertOrder.between_extension A' O' hA'O'

  have hSupp : Geo.AngleCongruent B O C B' O' C' :=
    hilbert_adjacent_angles_congruent
      Geo A O B C A' O' B' C'
      hAOC hA'O'C' hNoncol hNoncol' hCong

  refine ⟨C', hA'O'C', ?_⟩

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo A' O' B' A O B B' O' C'
      (Geometry.Geo.angle_congruent_symmetry Geo A O B A' O' B' hCong)
      (Geometry.Geo.angle_congruent_transitivity
        Geo A O B B O C B' O' C' hRightCong hSupp)

/--
Angle subtraction (Euclid, Common Notion 3, for angles).

If `∠A O B ≅ ∠A' O' B'`, and a ray `O R` lying strictly inside `∠A O B`
(in the sense that it meets the open segment `A B`) has `∠A O R ≅ ∠A'
O' R'` for a correspondingly-inside ray `O' R'`, then the remaining
parts agree too: `∠R O B ≅ ∠R' O' B'`.
-/
theorem hilbert_angle_subtract
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B R A' O' B' R' : Geo.Point)
    (hAOB : ¬ PrimCollinear Geo A O B)
    (hA'O'B' : ¬ PrimCollinear Geo A' O' B')
    (hRInside : HilbertRayMeetsSegment Geo O R A B)
    (hR'Inside : HilbertRayMeetsSegment Geo O' R' A' B')
    (hWhole : Geo.AngleCongruent A O B A' O' B')
    (hPart : Geo.AngleCongruent A O R A' O' R') :
    Geo.AngleCongruent R O B R' O' B' :=
  sorry

/--
Two right triangles sharing a second angle share the third angle too.

`hRight`/`hRight'` are the right angles at `O`/`O'`; `hAngleB` says the
angles at `B`/`B'` agree; the conclusion is that the angles at `A`/`A'`
agree.  This is the elementary (angle-sum) form of AA similarity for
right triangles specifically -- see Hartshorne, *Geometry: Euclid and
Beyond*, the argument used for the multiplicative inverse (19.2(5)):
"let β be the other acute angle [of the first triangle]... since the
other angle [of the second triangle] is β (I.32), ab = 1" -- and does
NOT need Hartshorne's general (arbitrary-triangle) Prop. 20.1, which
goes via the incenter and angle bisectors of both triangles.
-/
theorem hilbert_right_triangle_third_angle_congruent
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O A B O' A' B' : Geo.Point)
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B')
    (hNoncol : ¬ PrimCollinear Geo O A B)
    (hNoncol' : ¬ PrimCollinear Geo O' A' B')
    (hAngleB : Geo.AngleCongruent A B O A' B' O') :
    Geo.AngleCongruent O A B O' A' B' := by

  ----------------------------------------------------------------
  -- Extend `A–O` beyond `O` to `C`, and `A'–O'` beyond `O'` to `C'`.
  ----------------------------------------------------------------

  have hAO : A ≠ O := (hilbert_noncollinear_ne_first Geo O A B hNoncol).symm
  have hA'O' : A' ≠ O' := (hilbert_noncollinear_ne_first Geo O' A' B' hNoncol').symm

  obtain ⟨C, hAOC⟩ := HilbertOrder.between_extension A O hAO
  obtain ⟨C', hA'O'C'⟩ := HilbertOrder.between_extension A' O' hA'O'

  have hBAO : ¬ PrimCollinear Geo B A O := by
    intro h
    exact hNoncol
      (PrimCollinearRotate Geo O B A
        (PrimCollinearSwap Geo B O A
          (PrimCollinearRotate Geo B A O h)))

  have hB'A'O' : ¬ PrimCollinear Geo B' A' O' := by
    intro h
    exact hNoncol'
      (PrimCollinearRotate Geo O' B' A'
        (PrimCollinearSwap Geo B' O' A'
          (PrimCollinearRotate Geo B' A' O' h)))

  ----------------------------------------------------------------
  -- I.32 (exterior angle), applied to `(B, A, O)` extending `A–O`
  -- through `O` to `C`, and to `(B', A', O')` extending `A'–O'`
  -- through `O'` to `C'`.
  ----------------------------------------------------------------

  obtain ⟨R, hBRC, hPart1, hPart2⟩ :=
    euclid_proposition_32_exterior B A O C hBAO hAOC

  obtain ⟨R', hB'R'C', hPart1', hPart2'⟩ :=
    euclid_proposition_32_exterior B' A' O' C' hB'A'O' hA'O'C'

  -- `hPart1 : AngleCongruent A B O B O R`  (∠ABO ≅ ∠BOR)
  -- `hPart2 : AngleCongruent B A O R O C`  (∠BAO ≅ ∠ROC)   -- this is the target, at O/C.

  ----------------------------------------------------------------
  -- The two right angles' `C`-supplements are congruent.
  ----------------------------------------------------------------

  have hNoncolAOB : ¬ PrimCollinear Geo A O B := fun h =>
    hNoncol (PrimCollinearSwap Geo A O B h)

  have hNoncolA'O'B' : ¬ PrimCollinear Geo A' O' B' := fun h =>
    hNoncol' (PrimCollinearSwap Geo A' O' B' h)

  have hRightCong : Geo.AngleCongruent A O B A' O' B' :=
    hilbert_all_right_angles_congruent
      Geo A O B A' O' B' hNoncolAOB hNoncolA'O'B' hRight hRight'

  have hSupp : Geo.AngleCongruent B O C B' O' C' :=
    hilbert_adjacent_angles_congruent
      Geo A O B C A' O' B' C'
      hAOC hA'O'C' hNoncolAOB hNoncolA'O'B' hRightCong

  ----------------------------------------------------------------
  -- `∠BOR ≅ ∠B'O'R'` (both ≅ `∠ABO ≅ ∠A'B'O'` by `hAngleB`).
  ----------------------------------------------------------------

  have hBOR_ABO : Geo.AngleCongruent B O R A B O :=
    Geometry.Geo.angle_congruent_symmetry Geo A B O B O R hPart1

  have hBOR_AngleB : Geo.AngleCongruent B O R A' B' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo B O R A B O A' B' O' hBOR_ABO hAngleB

  have hB'O'R'_ABO' : Geo.AngleCongruent B' O' R' A' B' O' :=
    Geometry.Geo.angle_congruent_symmetry Geo A' B' O' B' O' R' hPart1'

  have hBOR_B'O'R' : Geo.AngleCongruent B O R B' O' R' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo B O R A' B' O' B' O' R' hBOR_AngleB
      (Geometry.Geo.angle_congruent_symmetry
        Geo B' O' R' A' B' O' hB'O'R'_ABO')

  ----------------------------------------------------------------
  -- Noncollinearity of `(B, O, C)` / `(B', O', C')`, and `R`, `R'`
  -- lying on the respective open segments `B C`, `B' C'` (hence
  -- inside the angles, giving `HilbertRayMeetsSegment`).
  ----------------------------------------------------------------

  have hOC : O ≠ C := (HilbertOrder.between_incidence A O C hAOC).2.1
  have hACO : PrimCollinear Geo A C O :=
    PrimCollinearRotate Geo A O C
      (HilbertOrder.between_incidence A O C hAOC).2.2.2.1

  have hBOC : ¬ PrimCollinear Geo B O C := by
    intro h
    rcases h with ⟨l, hBl, hOl, hCl⟩
    rcases hACO with ⟨m, hAm, hCm, hOm⟩
    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique O C hOC l m hOl hCl hOm hCm
    exact hNoncol ⟨m, hOm, hAm, hlm ▸ hBl⟩

  have hO'C' : O' ≠ C' := (HilbertOrder.between_incidence A' O' C' hA'O'C').2.1
  have hA'C'O' : PrimCollinear Geo A' C' O' :=
    PrimCollinearRotate Geo A' O' C'
      (HilbertOrder.between_incidence A' O' C' hA'O'C').2.2.2.1

  have hB'O'C' : ¬ PrimCollinear Geo B' O' C' := by
    intro h
    rcases h with ⟨l, hB'l, hO'l, hC'l⟩
    rcases hA'C'O' with ⟨m, hA'm, hC'm, hO'm⟩
    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique O' C' hO'C' l m hO'l hC'l hO'm hC'm
    exact hNoncol' ⟨m, hO'm, hA'm, hlm ▸ hB'l⟩

  have hRO : R ≠ O := by
    intro h
    apply hBOC
    have hPrim : PrimCollinear Geo B R C :=
      (HilbertOrder.between_incidence B R C hBRC).2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hR'O' : R' ≠ O' := by
    intro h
    apply hB'O'C'
    have hPrim : PrimCollinear Geo B' R' C' :=
      (HilbertOrder.between_incidence B' R' C' hB'R'C').2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hRInside : HilbertRayMeetsSegment Geo O R B C :=
    ⟨R, hBRC, hilbert_sameRay_refl Geo O R hRO⟩

  have hR'Inside : HilbertRayMeetsSegment Geo O' R' B' C' :=
    ⟨R', hB'R'C', hilbert_sameRay_refl Geo O' R' hR'O'⟩

  ----------------------------------------------------------------
  -- Subtract `∠BOR ≅ ∠B'O'R'` from `∠BOC ≅ ∠B'O'C'`.
  ----------------------------------------------------------------

  have hROC_R'O'C' : Geo.AngleCongruent R O C R' O' C' :=
    hilbert_angle_subtract
      Geo B O C R B' O' C' R'
      hBOC hB'O'C' hRInside hR'Inside hSupp hBOR_B'O'R'

  ----------------------------------------------------------------
  -- Assemble the target angle congruence.
  ----------------------------------------------------------------

  have hFinal1 : Geo.AngleCongruent B A O R' O' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo B A O R O C R' O' C' hPart2 hROC_R'O'C'

  have hFinal2 : Geo.AngleCongruent B A O B' A' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo B A O R' O' C' B' A' O' hFinal1
      (Geometry.Geo.angle_congruent_symmetry Geo B' A' O' R' O' C' hPart2')

  have hFinal3 : Geo.AngleCongruent O A B B' A' O' :=
    (Geometry.Geo.angle_congruent_reverse_first Geo B A O B' A' O').mp hFinal2

  exact
    (Geometry.Geo.angle_congruent_reverse_second Geo O A B B' A' O').mp hFinal3

------------------------------------------------------------------------
-- Part 0b.  The fourth proportional
--
-- Hilbert sec. 15 / Euclid VI.12.  `hilbertPositiveSegmentRatioWitness_exists`
-- (HilbertSegmentArithmetic.lean) already builds, for *any* pair
-- `(a,b)`, a right triangle realizing that ratio.  What is missing is
-- the *matching* triangle for a prescribed third segment `c`: given
-- the witness `(O,A,B)` for `a:b`, lay a representative of `c` off on
-- the ray `O → B`, obtaining `B2`, and find `A2` on the ray `O → A`
-- with `A2 B2 ∥ A B` (Thales/intercept configuration, sharing the
-- right angle at `O` as a fixed pair of perpendicular axes).  Then
-- `(O,A2,B2)` is a witness for `(c,d)` with `d := class(O,A2)`, and
-- the parallel makes its defining angle at `A2` congruent to the
-- defining angle at `A`, by Euclid I.29 (`euclid_proposition_29_corresponding`,
-- Proposition29.lean).
--
-- This is genuinely [ELEM]: only Groups I-III, the parallel axiom,
-- and Pasch are used, exactly as in `hilbert_parallelogram_fourth_vertex_exists`
-- (HilbertIntersectionTest.lean) and `i42_angle_parallel_oriented_intersection`
-- (Proposition42.lean), whose techniques this reuses.
------------------------------------------------------------------------

/--
If Q and R are both on the opposite side of a line from P,
and P,Q,R are noncollinear, then Q and R are on the same side.
-/
theorem hilbert_two_oppositeSides_sameSide
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P Q R : Geo.Point)
    (l : Geo.Line)
    (hPQR : ¬ PrimCollinear Geo P Q R)
    (hPQ : HilbertOppositeSide Geo P Q l)
    (hPR : HilbertOppositeSide Geo P R l) :
    HilbertSameSide Geo Q R l := by

  rcases hPQ.2.2 with ⟨X, hPXQ, hXl⟩
  rcases hPR.2.2 with ⟨Y, hPYR, hYl⟩

  exact
    hilbert_third_side_endpoints_sameSide
      Geo P Q R X Y l
      hPQR hPXQ hPYR hXl hYl

theorem hilbert_between_of_collinear_oppositeSide
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O P Q : Geo.Point)
    (base carrier : Geo.Line)
    (hObase : HilbertIncidence.OnLine O base)
    (hOcarrier : HilbertIncidence.OnLine O carrier)
    (hPcarrier : HilbertIncidence.OnLine P carrier)
    (hQcarrier : HilbertIncidence.OnLine Q carrier)
    (hOpp : HilbertOppositeSide Geo P Q base) :
    Geo.Between P O Q := by

  rcases hOpp.2.2 with ⟨X, hPXQ, hXbase⟩

  have hXcarrier :
      HilbertIncidence.OnLine X carrier :=
    hilbert_between_on_line
      Geo P X Q carrier
      hPcarrier hQcarrier hPXQ

  have hXO : X = O := by
    by_contra hXO

    have hEq : base = carrier :=
      HilbertPlaneIncidence.line_unique
        O X (Ne.symm hXO)
        base carrier
        hObase hXbase
        hOcarrier hXcarrier

    have hPbase :
        HilbertIncidence.OnLine P base := by
      rw [hEq]
      exact hPcarrier

    exact hOpp.1 hPbase

  simpa [hXO] using hPXQ

/--
[ELEM] The fourth proportional exists: given `a, b, c` there is `d`
with `a : b = c : d`.

Split by `hilbert_between_trichotomy` on `O1, B1, B2`.  The degenerate
case reuses the original witness.  The shrinking case uses Pasch to
intersect the inner parallel with `O1 A1`.  The growing case intersects
that parallel directly with `O1 A1`; parallel uniqueness proves the
intersection, and side separation proves the order `O1-A1-A2`.
Euclid I.29 supplies the defining angle in both genuine cases.
-/
theorem hilbertPositiveSegmentProportion_fourth_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    ∃ d : HilbertPositiveSegmentClass Geo,
      HilbertPositiveSegmentProportion Geo a b c d := by

  obtain ⟨w1⟩ := hilbertPositiveSegmentRatioWitness_exists Geo a b

  refine Quotient.inductionOn c (fun sc => ?_)
  rcases sc with ⟨⟨U, V⟩, hUV⟩
  change Ne U V at hUV

  ------------------------------------------------------------------
  -- Lay a representative of `c` off on the ray `O1 → B1`.
  ------------------------------------------------------------------

  obtain ⟨B2, hRayB1B2, hO1B2_UV⟩ :=
    HilbertCongruence.segment_construction U V w1.O w1.B w1.hOB

  have hO1B2 : w1.O ≠ B2 := hRayB1B2.2.1.symm
  have hCollO1B1B2 : PrimCollinear Geo w1.O w1.B B2 := hRayB1B2.2.2.1

  by_cases hB1B2 : w1.B = B2

  ------------------------------------------------------------------
  -- Degenerate case: `B2 = B1`, hence `c = a`.  Reuse `w1` itself,
  -- with `d := b` and the trivial (reflexive) angle match.
  ------------------------------------------------------------------

  · have hcClass :
        hilbertPositiveSegmentClassOf Geo w1.O w1.B w1.hOB =
          hilbertPositiveSegmentClassOf Geo U V hUV := by
      apply Quotient.sound
      show Geo.Congruent w1.O w1.B U V
      rw [hB1B2]
      exact hO1B2_UV

    refine
      ⟨b, w1,
        { O := w1.O
          A := w1.A
          B := w1.B
          hOA := w1.hOA
          hOB := w1.hOB
          hNoncol := w1.hNoncol
          hRight := w1.hRight
          hFirst := hcClass
          hSecond := w1.hSecond },
        ?_⟩

    exact
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) w1.O w1.A w1.B w1.hNoncol

  ------------------------------------------------------------------
  -- Genuine case: `B1 ≠ B2`.
  ------------------------------------------------------------------

  · have hA1B1 : w1.A ≠ w1.B := by
      intro h
      apply w1.hNoncol
      rcases HilbertPlaneIncidence.line_through w1.O w1.A w1.hOA with
        ⟨l, hOl, hAl⟩
      have hBl : HilbertIncidence.OnLine w1.B l := h ▸ hAl
      exact ⟨l, hOl, hAl, hBl⟩

    have hB1A1B2 : ¬ Collinear Geo w1.B w1.A B2 := by
      intro hCol
      rcases hCol with ⟨l, hB1l, hA1l, hB2l⟩
      rcases hCollO1B1B2 with ⟨m, hO1m, hB1m, hB2m⟩
      have hlm : l = m :=
        HilbertPlaneIncidence.line_unique
          w1.B B2 hB1B2 l m hB1l hB2l hB1m hB2m
      exact w1.hNoncol ⟨m, hO1m, hlm ▸ hA1l, hB1m⟩

    -- The line through `B2` parallel to `A1 B1` (Hilbert I.31).
    obtain ⟨Qp, hB2Qp, hParallel⟩ :=
      hilbert_parallel_through_point_exists
        Geo w1.B w1.A B2 hA1B1.symm hB1A1B2

    rcases
        hilbert_between_trichotomy
          Geo w1.O w1.B B2 w1.hOB hB1B2 hO1B2 hCollO1B1B2 with
      hCase2 | hImpossible | hCase1

    ----------------------------------------------------------------
    -- Goal 1, `hCase2 : Between w1.O w1.B B2` (c > a, growing case).
    -- Intersect OA with the line through B2 parallel to BA.  Parallel
    -- uniqueness gives the intersection, and side separation gives
    -- the required order O-A-A2.  Euclid I.29 then transfers the
    -- defining angle directly, without angle subtraction.
    ----------------------------------------------------------------

    · have hABO : ¬ PrimCollinear Geo w1.A w1.B w1.O := fun h =>
        w1.hNoncol
          (PrimCollinearCycle Geo w1.B w1.O w1.A
            (PrimCollinearCycle Geo w1.A w1.B w1.O h))
      have hBAO : ¬ PrimCollinear Geo w1.B w1.A w1.O := fun h =>
        hABO (PrimCollinearSwap Geo w1.B w1.A w1.O h)

      obtain ⟨n, hOn, hAn⟩ :=
        HilbertPlaneIncidence.line_through w1.O w1.A w1.hOA
      obtain ⟨l, hB2l, hQpl⟩ :=
        HilbertPlaneIncidence.line_through B2 Qp hB2Qp
      obtain ⟨bl, hB1bl, hAbl⟩ :=
        HilbertPlaneIncidence.line_through w1.B w1.A hA1B1.symm

      have hDistinct :
          Geo.PointLine w1.O w1.A ≠ Geo.PointLine w1.B w1.A := by
        intro hEq
        have hO_BA : w1.O ∈ Geo.PointLine w1.B w1.A := by
          rw [← hEq]
          exact intersection_test_left_mem Geo w1.O w1.A
        have hObl : HilbertIncidence.OnLine w1.O bl :=
          (hilbert_mem_pointLine_iff_onLine
            Geo w1.B w1.A w1.O bl hA1B1.symm hB1bl hAbl).mp hO_BA
        exact hBAO ⟨bl, hB1bl, hAbl, hObl⟩

      have hMeet : HilbertLinesMeet Geo n l := by
        by_contra hDisjoint
        have hOA_B2Qp : Geo.Parallel w1.O w1.A B2 Qp :=
          intersection_test_parallel_of_lines_disjoint
            Geo w1.O w1.A B2 Qp n l
            w1.hOA hB2Qp hOn hAn hB2l hQpl hDisjoint
        have hOA_BA : Geo.Parallel w1.O w1.A w1.B w1.A :=
          hilbert_parallel_transitive_distinct
            Geo w1.O w1.A w1.B w1.A B2 Qp
            hOA_B2Qp hParallel hDistinct
        exact
          intersection_test_not_parallel_of_common_point
            Geo w1.O w1.A w1.B w1.A w1.A
            (intersection_test_right_mem Geo w1.O w1.A)
            (intersection_test_right_mem Geo w1.B w1.A)
            hOA_BA

      rcases hMeet with ⟨A2, hA2n, hA2l⟩

      have hA2O : A2 ≠ w1.O := by
        intro hA2O
        have hOl : HilbertIncidence.OnLine w1.O l := by
          rw [← hA2O]
          exact hA2l
        rcases hCollO1B1B2 with ⟨ob, hOob, hB1ob, hB2ob⟩
        have hobl : ob = l :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2 ob l hOob hB2ob hOl hB2l
        have hB1l : HilbertIncidence.OnLine w1.B l := by
          rw [← hobl]
          exact hB1ob
        have hB1_B2Qp : w1.B ∈ Geo.PointLine B2 Qp :=
          (hilbert_mem_pointLine_iff_onLine
            Geo B2 Qp w1.B l hB2Qp hB2l hQpl).mpr hB1l
        exact
          intersection_test_not_parallel_of_common_point
            Geo w1.B w1.A B2 Qp w1.B
            (intersection_test_left_mem Geo w1.B w1.A)
            hB1_B2Qp hParallel

      have hA2B2 : A2 ≠ B2 := by
        intro hA2B2
        have hB2n : HilbertIncidence.OnLine B2 n := by
          rw [← hA2B2]
          exact hA2n
        rcases hCollO1B1B2 with ⟨ob, hOob, hB1ob, hB2ob⟩
        have hnob : n = ob :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2 n ob hOn hB2n hOob hB2ob
        have hB1n : HilbertIncidence.OnLine w1.B n := by
          rw [hnob]
          exact hB1ob
        exact w1.hNoncol ⟨n, hOn, hAn, hB1n⟩

      have hCollB2A2Qp : Collinear Geo B2 A2 Qp :=
        ⟨l, hB2l, hA2l, hQpl⟩
      have hB2Qp_BA : Geo.Parallel B2 Qp w1.B w1.A :=
        ParallelSymmetry Geo w1.B w1.A B2 Qp hParallel
      have hB2A2_BA : Geo.Parallel B2 A2 w1.B w1.A :=
        collinear_parallel_trans
          Geo B2 A2 Qp w1.B w1.A hA2B2.symm hCollB2A2Qp hB2Qp_BA
      have hBA_B2A2 : Geo.Parallel w1.B w1.A B2 A2 :=
        ParallelSymmetry Geo B2 A2 w1.B w1.A hB2A2_BA

      rcases
          hilbert_parallel_second_endpoints_sameSide
            Geo w1.B w1.A B2 A2 hBA_B2A2 with
        ⟨base, hB1base, hAbase, hSameBase⟩
      have hBaseEq : base = bl :=
        HilbertPlaneIncidence.line_unique
          w1.B w1.A hA1B1.symm
          base bl hB1base hAbase hB1bl hAbl
      have hSameB2A2 : HilbertSameSide Geo B2 A2 bl := by
        simpa [hBaseEq] using hSameBase

      have hObl : ¬ HilbertIncidence.OnLine w1.O bl := by
        intro h
        exact hBAO ⟨bl, hB1bl, hAbl, h⟩
      have hOppOB2 : HilbertOppositeSide Geo w1.O B2 bl :=
        ⟨hObl, hSameB2A2.1, ⟨w1.B, hCase2, hB1bl⟩⟩
      have hOppOA2 : HilbertOppositeSide Geo w1.O A2 bl :=
        hilbert_oppositeSide_transport_right
          Geo w1.O B2 A2 bl hOppOB2 hSameB2A2
      have hOA1A2 : Geo.Between w1.O w1.A A2 :=
        hilbert_between_of_collinear_oppositeSide
          Geo w1.A w1.O A2 bl n hAbl hAn hOn hA2n hOppOA2

      have hOA1A2Data :=
        HilbertOrder.between_incidence w1.O w1.A A2 hOA1A2
      have hA1A2 : w1.A ≠ A2 := hOA1A2Data.2.1
      have hRayA1A2 : HilbertSameRay Geo w1.O w1.A A2 :=
        hilbert_sameRay_of_between Geo w1.O w1.A A2 hOA1A2

      obtain ⟨Aext, hB2A2Aext⟩ :=
        HilbertOrder.between_extension B2 A2 hA2B2.symm
      obtain ⟨Cext, hB1A1Cext⟩ :=
        HilbertOrder.between_extension w1.B w1.A hA1B1.symm

      have hAextData :=
        HilbertOrder.between_incidence B2 A2 Aext hB2A2Aext
      have hB2Aext : B2 ≠ Aext := hAextData.2.2.1
      have hCextData :=
        HilbertOrder.between_incidence w1.B w1.A Cext hB1A1Cext
      have hB1Cext : w1.B ≠ Cext := hCextData.2.2.1

      have hAextl : HilbertIncidence.OnLine Aext l := by
        rcases hAextData.2.2.2.1 with ⟨q, hB2q, hA2q, hAextq⟩
        have hql : q = l :=
          HilbertPlaneIncidence.line_unique
            B2 A2 hAextData.1 q l hB2q hA2q hB2l hA2l
        exact hql ▸ hAextq

      have hCextbl : HilbertIncidence.OnLine Cext bl := by
        rcases hCextData.2.2.2.1 with ⟨q, hB1q, hA1q, hCextq⟩
        have hqbl : q = bl :=
          HilbertPlaneIncidence.line_unique
            w1.B w1.A hA1B1.symm q bl hB1q hA1q hB1bl hAbl
        exact hqbl ▸ hCextq

      have hCollB2AextQp : Collinear Geo B2 Aext Qp :=
        ⟨l, hB2l, hAextl, hQpl⟩
      have hCollB1CextA1 : Collinear Geo w1.B Cext w1.A :=
        ⟨bl, hB1bl, hCextbl, hAbl⟩
      have hB2Aext_BA : Geo.Parallel B2 Aext w1.B w1.A :=
        collinear_parallel_trans
          Geo B2 Aext Qp w1.B w1.A hB2Aext hCollB2AextQp hB2Qp_BA
      have hBA_B2Aext : Geo.Parallel w1.B w1.A B2 Aext :=
        ParallelSymmetry Geo B2 Aext w1.B w1.A hB2Aext_BA
      have hB1Cext_B2Aext : Geo.Parallel w1.B Cext B2 Aext :=
        collinear_parallel_trans
          Geo w1.B Cext w1.A B2 Aext
          hB1Cext hCollB1CextA1 hBA_B2Aext
      have hB2Aext_B1Cext : Geo.Parallel B2 Aext w1.B Cext :=
        ParallelSymmetry Geo w1.B Cext B2 Aext hB1Cext_B2Aext
      have hAextB2_B1Cext : Geo.Parallel Aext B2 w1.B Cext :=
        ParallelSwapFirstLine Geo B2 Aext w1.B Cext hB2Aext_B1Cext
      have hAextB2_CextB1 : Geo.Parallel Aext B2 Cext w1.B :=
        ParallelSwapSecondLine Geo Aext B2 w1.B Cext hAextB2_B1Cext
      have hCextB1_AextB2 : Geo.Parallel Cext w1.B Aext B2 :=
        ParallelSymmetry Geo Aext B2 Cext w1.B hAextB2_CextB1

      have hB1n : ¬ HilbertIncidence.OnLine w1.B n := by
        intro h
        exact w1.hNoncol ⟨n, hOn, hAn, h⟩
      have hB2n : ¬ HilbertIncidence.OnLine B2 n := by
        intro h
        rcases hCollO1B1B2 with ⟨ob, hOob, hB1ob, hB2ob⟩
        have hnob : n = ob :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2 n ob hOn h hOob hB2ob
        exact hB1n (hnob ▸ hB1ob)

      have hB2B1O : Geo.Between B2 w1.B w1.O :=
        (HilbertOrder.between_incidence w1.O w1.B B2 hCase2).2.2.2.2
      have hSameB2B1 : HilbertSameSide Geo B2 w1.B n :=
        hilbert_between_sameSide_of_endpoint_on_line
          Geo B2 w1.B w1.O n hB2B1O hOn hB2n
      have hSameB1B2 : HilbertSameSide Geo w1.B B2 n :=
        hilbert_sameSide_symm Geo B2 w1.B n hSameB2B1

      have hCextn : ¬ HilbertIncidence.OnLine Cext n := by
        intro h
        have hnbl : n = bl :=
          HilbertPlaneIncidence.line_unique
            w1.A Cext hCextData.2.1 n bl hAn h hAbl hCextbl
        exact hB1n (hnbl ▸ hB1bl)

      have hCextA1B1 : Geo.Between Cext w1.A w1.B :=
        hCextData.2.2.2.2
      have hOppCextB1 : HilbertOppositeSide Geo Cext w1.B n :=
        ⟨hCextn, hB1n, ⟨w1.A, hCextA1B1, hAn⟩⟩
      have hOppCextB2 : HilbertOppositeSide Geo Cext B2 n :=
        hilbert_oppositeSide_transport_right
          Geo Cext w1.B B2 n hOppCextB1 hSameB1B2

      have hAextA2B2 : Geo.Between Aext A2 B2 :=
        hAextData.2.2.2.2
      have hCorresponding :
          Geo.AngleCongruent w1.O w1.A w1.B w1.A A2 B2 :=
        euclid_proposition_29_corresponding
          Cext w1.B Aext B2 w1.O w1.A A2
          n
          hCextA1B1 hAextA2B2 hOA1A2 hA1A2 hAn hA2n
          hOppCextB2 hCextB1_AextB2

      have hA2A1O : Geo.Between A2 w1.A w1.O :=
        hOA1A2Data.2.2.2.2
      have hRayA2A1O : HilbertSameRay Geo A2 w1.A w1.O :=
        hilbert_sameRay_of_between Geo A2 w1.A w1.O hA2A1O
      have hAngleAtA2 :
          Geo.Angle w1.A A2 B2 = Geo.Angle w1.O A2 B2 :=
        hilbert_angle_eq_of_sameRay_first
          Geo A2 w1.A w1.O B2 hRayA2A1O
      have hFinalAngle :
          Geo.AngleCongruent w1.O w1.A w1.B w1.O A2 B2 := by
        unfold Geometry.Geo.AngleCongruent at hCorresponding ⊢
        rw [hAngleAtA2] at hCorresponding
        exact hCorresponding

      have hRightA2B2 : HilbertRightAngle Geo A2 w1.O B2 := by
        rcases w1.hRight with ⟨C, hAOC, hRightCong⟩
        have hCO1 : C ≠ w1.O :=
          (HilbertOrder.between_incidence w1.A w1.O C hAOC).2.1.symm
        have hA2OC : Geo.Between A2 w1.O C :=
          hilbert_between_transport_sameRays
            Geo w1.A w1.O C A2 C
            hAOC hRayA1A2 (hilbert_sameRay_refl Geo w1.O C hCO1)
        have hAngleLeft1 :
            Geo.Angle w1.A w1.O w1.B = Geo.Angle A2 w1.O w1.B :=
          hilbert_angle_eq_of_sameRay_first
            Geo w1.O w1.A A2 w1.B hRayA1A2
        have hAngleLeft2 :
            Geo.Angle A2 w1.O w1.B = Geo.Angle A2 w1.O B2 :=
          hilbert_angle_eq_of_sameRay_second
            Geo w1.O A2 w1.B B2 hRayB1B2
        have hAngleRight1 :
            Geo.Angle w1.B w1.O C = Geo.Angle B2 w1.O C :=
          hilbert_angle_eq_of_sameRay_first
            Geo w1.O w1.B B2 C hRayB1B2
        refine ⟨C, hA2OC, ?_⟩
        unfold Geometry.Geo.AngleCongruent at hRightCong ⊢
        rw [← hAngleLeft2, ← hAngleLeft1, ← hAngleRight1]
        exact hRightCong

      have hAOBswap : ¬ PrimCollinear Geo w1.A w1.O w1.B := fun h =>
        w1.hNoncol (PrimCollinearSwap Geo w1.A w1.O w1.B h)
      have hNoncolOA2B2 : ¬ PrimCollinear Geo w1.O A2 B2 := by
        intro h
        exact
          (hilbert_noncollinear_of_sameRays
            Geo w1.A w1.O w1.B A2 B2
            hAOBswap hRayA1A2 hRayB1B2)
            (PrimCollinearSwap Geo w1.O A2 B2 h)

      have hFirstD :
          hilbertPositiveSegmentClassOf Geo w1.O B2 hO1B2 =
            hilbertPositiveSegmentClassOf Geo U V hUV :=
        Quotient.sound hO1B2_UV

      exact
        ⟨hilbertPositiveSegmentClassOf Geo w1.O A2 hA2O.symm, w1,
          { O := w1.O
            A := A2
            B := B2
            hOA := hA2O.symm
            hOB := hO1B2
            hNoncol := hNoncolOA2B2
            hRight := hRightA2B2
            hFirst := hFirstD
            hSecond := rfl },
          hFinalAngle⟩

    ----------------------------------------------------------------
    -- Goal 2, `hImpossible : Between w1.B w1.O B2` cannot happen: it
    -- contradicts `hRayB1B2` (`B1, B2` are on the *same* ray from
    -- `O1`, so `O1` is never between them).
    ----------------------------------------------------------------

    · exact absurd hImpossible hRayB1B2.2.2.2

    ----------------------------------------------------------------
    -- Goal 3, `hCase1 : Between w1.O B2 w1.B`  (c ≤ a, "shrinking"
    -- case).  Pasch on the triangle `(O1, B1, A1)`, entering through
    -- the line `l` through `B2` parallel to `A1 B1`, forces `l` to
    -- cross the open segment `O1 A1` at a point `A2`; corresponding
    -- angles (`euclid_proposition_29_corresponding`) then transfer
    -- the defining angle from `A1` to `A2`, and the right angle at
    -- `O1` transports along the two `SameRay` facts exactly as in
    -- `hilbertPositiveSegmentRatioWitness_exists`.
    ----------------------------------------------------------------

    · obtain ⟨n, hOn, hAn⟩ :=
        HilbertPlaneIncidence.line_through w1.O w1.A w1.hOA
      obtain ⟨l, hB2l, hQpl⟩ :=
        HilbertPlaneIncidence.line_through B2 Qp hB2Qp
      obtain ⟨bl, hB1bl, hAbl⟩ :=
        HilbertPlaneIncidence.line_through w1.B w1.A hA1B1.symm

      have hA1l : ¬ HilbertIncidence.OnLine w1.A l := by
        intro h
        have hA1_B2Qp : w1.A ∈ Geo.PointLine B2 Qp :=
          (hilbert_mem_pointLine_iff_onLine
            Geo B2 Qp w1.A l hB2Qp hB2l hQpl).mpr h
        exact
          intersection_test_not_parallel_of_common_point
            Geo w1.B w1.A B2 Qp w1.A
            (intersection_test_right_mem Geo w1.B w1.A)
            hA1_B2Qp hParallel

      have hB1l : ¬ HilbertIncidence.OnLine w1.B l := by
        intro h
        have hB1_B2Qp : w1.B ∈ Geo.PointLine B2 Qp :=
          (hilbert_mem_pointLine_iff_onLine
            Geo B2 Qp w1.B l hB2Qp hB2l hQpl).mpr h
        exact
          intersection_test_not_parallel_of_common_point
            Geo w1.B w1.A B2 Qp w1.B
            (intersection_test_left_mem Geo w1.B w1.A)
            hB1_B2Qp hParallel

      have hO1l : ¬ HilbertIncidence.OnLine w1.O l := by
        intro h
        rcases hCollO1B1B2 with ⟨m, hO1m, hB1m, hB2m⟩
        have hlm : l = m :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2 l m h hB2l hO1m hB2m
        exact hB1l (hlm ▸ hB1m)

      have hNoncolOBA : ¬ PrimCollinear Geo w1.O w1.B w1.A := by
        intro h
        exact w1.hNoncol (PrimCollinearRotate Geo w1.O w1.B w1.A h)

      have hMeetOB : HilbertSegmentMeetsLine Geo w1.O w1.B l :=
        ⟨B2, hCase1, hB2l⟩

      rcases
          HilbertOrder.pasch
            w1.O w1.B w1.A hNoncolOBA l hO1l hB1l hA1l hMeetOB with
        hMeetOA | hMeetBA

      · rcases hMeetOA with ⟨A2, hOA2A1, hA2l⟩

        have hA2n : HilbertIncidence.OnLine A2 n := by
          have hData := HilbertOrder.between_incidence w1.O A2 w1.A hOA2A1
          rcases hData.2.2.2.1 with ⟨p, hOp, hA2p, hAp⟩
          have hpn : p = n :=
            HilbertPlaneIncidence.line_unique
              w1.O w1.A w1.hOA p n hOp hAp hOn hAn
          exact hpn ▸ hA2p

        have hOA2Data := HilbertOrder.between_incidence w1.O A2 w1.A hOA2A1
        have hA2A1 : A2 ≠ w1.A := hOA2Data.2.1
        have hOA2 : w1.O ≠ A2 := hOA2Data.1

        have hRaySameA1A2 : HilbertSameRay Geo w1.O w1.A A2 := by
          refine ⟨w1.hOA.symm, hOA2.symm,
            PrimCollinearRotate Geo w1.O A2 w1.A hOA2Data.2.2.2.1, ?_⟩
          intro hContra
          have hRev : Geo.Between A2 w1.O w1.A :=
            (HilbertOrder.between_incidence w1.A w1.O A2 hContra).2.2.2.2
          exact
            (HilbertOrder.between_unique
              w1.O A2 w1.A hOA2Data.2.2.2.1 hOA2A1).1 hRev

        --------------------------------------------------------
        -- `B2, B1` are on the same side of `n`.
        --------------------------------------------------------
        have hB1n : ¬ HilbertIncidence.OnLine w1.B n := by
          intro h
          exact w1.hNoncol ⟨n, hOn, hAn, h⟩

        have hB2n : ¬ HilbertIncidence.OnLine B2 n := by
          intro h
          rcases hCollO1B1B2 with ⟨m, hO1m, hB1m, hB2m⟩
          have hnm : n = m :=
            HilbertPlaneIncidence.line_unique
              w1.O B2 hO1B2 n m hOn h hO1m hB2m
          exact hB1n (hnm ▸ hB1m)

        have hNoMeetB1B2n : ¬ HilbertSegmentMeetsLine Geo w1.B B2 n := by
          rintro ⟨X, hBXB2, hXn⟩
          by_cases hXO : X = w1.O
          · have hBOB2 : Geo.Between w1.B w1.O B2 := hXO ▸ hBXB2
            have hB2OB1 : Geo.Between B2 w1.O w1.B :=
              (HilbertOrder.between_incidence
                w1.B w1.O B2 hBOB2).2.2.2.2
            have hPrimO1B2B1 : PrimCollinear Geo w1.O B2 w1.B :=
              (HilbertOrder.between_incidence
                w1.O B2 w1.B hCase1).2.2.2.1
            exact
              (HilbertOrder.between_unique
                w1.O B2 w1.B hPrimO1B2B1 hCase1).1 hB2OB1
          · rcases hCollO1B1B2 with ⟨m, hO1m, hB1m, hB2m⟩
            have hXm : HilbertIncidence.OnLine X m := by
              have hData := HilbertOrder.between_incidence w1.B X B2 hBXB2
              rcases hData.2.2.2.1 with ⟨q, hBq, hXq, hB2q⟩
              have hqm : q = m :=
                HilbertPlaneIncidence.line_unique
                  w1.B B2 hB1B2 q m hBq hB2q hB1m hB2m
              exact hqm ▸ hXq
            have hnm : n = m :=
              HilbertPlaneIncidence.line_unique
                w1.O X (Ne.symm hXO) n m hOn hXn hO1m hXm
            exact hB1n (hnm ▸ hB1m)

        have hNoMeetB2B1n : ¬ HilbertSegmentMeetsLine Geo B2 w1.B n := by
          rintro ⟨X, hB2XB1, hXn⟩
          exact
            hNoMeetB1B2n
              ⟨X,
                (HilbertOrder.between_incidence B2 X w1.B hB2XB1).2.2.2.2,
                hXn⟩

        have hSameSideB2B1 : HilbertSameSide Geo B2 w1.B n :=
          ⟨hB2n, hB1n,
            Relation.ReflTransGen.single ⟨hB2n, hB1n, hNoMeetB2B1n⟩⟩

        --------------------------------------------------------
        -- Extend `B2–A2` beyond `A2`, and `B1–A1` beyond `A1`.
        --------------------------------------------------------
        have hB2neA2 : B2 ≠ A2 := by
          intro h
          rw [h] at hB2n
          exact hB2n hA2n

        obtain ⟨Aext, hB2A2Aext⟩ :=
          HilbertOrder.between_extension B2 A2 hB2neA2
        obtain ⟨Cext, hB1A1Cext⟩ :=
          HilbertOrder.between_extension w1.B w1.A hA1B1.symm

        have hAextData := HilbertOrder.between_incidence B2 A2 Aext hB2A2Aext
        have hB2Aext : B2 ≠ Aext := hAextData.2.2.1
        have hCextData := HilbertOrder.between_incidence w1.B w1.A Cext hB1A1Cext
        have hB1Cext : w1.B ≠ Cext := hCextData.2.2.1

        have hAextl : HilbertIncidence.OnLine Aext l := by
          rcases hAextData.2.2.2.1 with ⟨q, hB2q, hA2q, hAextq⟩
          have hql : q = l :=
            HilbertPlaneIncidence.line_unique
              B2 A2 hAextData.1 q l hB2q hA2q hB2l hA2l
          exact hql ▸ hAextq

        have hCextbl : HilbertIncidence.OnLine Cext bl := by
          rcases hCextData.2.2.2.1 with ⟨q, hB1q, hA1q, hCextq⟩
          have hqbl : q = bl :=
            HilbertPlaneIncidence.line_unique
              w1.B w1.A hA1B1.symm q bl hB1q hA1q hB1bl hAbl
          exact hqbl ▸ hCextq

        have hOppAextB2 : HilbertOppositeSide Geo Aext B2 n := by
          refine ⟨?_, hB2n,
            ⟨A2,
              (HilbertOrder.between_incidence
                B2 A2 Aext hB2A2Aext).2.2.2.2,
              hA2n⟩⟩
          intro h
          apply hB2n
          have hnl : n = l :=
            HilbertPlaneIncidence.line_unique
              A2 Aext hAextData.2.1 n l hA2n h hA2l hAextl
          rw [hnl]
          exact hB2l

        have hOppAextB1 : HilbertOppositeSide Geo Aext w1.B n :=
          hilbert_oppositeSide_transport_right
            Geo Aext B2 w1.B n hOppAextB2 hSameSideB2B1

        --------------------------------------------------------
        -- Re-describe the parallel through the extension points.
        --------------------------------------------------------
        have hCollB2AextQp : Collinear Geo B2 Aext Qp :=
          ⟨l, hB2l, hAextl, hQpl⟩
        have hCollB1CextA1 : Collinear Geo w1.B Cext w1.A :=
          ⟨bl, hB1bl, hCextbl, hAbl⟩

        have hStep1 : Geo.Parallel B2 Qp w1.B w1.A :=
          ParallelSymmetry Geo w1.B w1.A B2 Qp hParallel
        have hStep2 : Geo.Parallel B2 Aext w1.B w1.A :=
          collinear_parallel_trans
            Geo B2 Aext Qp w1.B w1.A hB2Aext hCollB2AextQp hStep1
        have hStep2Sym : Geo.Parallel w1.B w1.A B2 Aext :=
          ParallelSymmetry Geo B2 Aext w1.B w1.A hStep2
        have hStep3 : Geo.Parallel w1.B Cext B2 Aext :=
          collinear_parallel_trans
            Geo w1.B Cext w1.A B2 Aext hB1Cext hCollB1CextA1 hStep2Sym
        have hStep3Sym : Geo.Parallel B2 Aext w1.B Cext :=
          ParallelSymmetry Geo w1.B Cext B2 Aext hStep3
        have hStep4 : Geo.Parallel Aext B2 w1.B Cext :=
          ParallelSwapFirstLine Geo B2 Aext w1.B Cext hStep3Sym
        have hParallelExt : Geo.Parallel Aext B2 Cext w1.B :=
          ParallelSwapSecondLine Geo Aext B2 w1.B Cext hStep4

        --------------------------------------------------------
        -- Corresponding angles (Euclid I.29).
        --------------------------------------------------------
        have hAGB : Geo.Between Aext A2 B2 :=
          (HilbertOrder.between_incidence B2 A2 Aext hB2A2Aext).2.2.2.2
        have hCHD : Geo.Between Cext w1.A w1.B :=
          (HilbertOrder.between_incidence w1.B w1.A Cext hB1A1Cext).2.2.2.2

        have hCorresponding :
            Geo.AngleCongruent w1.O A2 B2 A2 w1.A w1.B :=
          euclid_proposition_29_corresponding
            Aext B2 Cext w1.B w1.O A2 w1.A
            n
            hAGB hCHD hOA2A1 hA2A1 hA2n hAn hOppAextB1 hParallelExt

        have hRaySameO1A2 : HilbertSameRay Geo w1.A A2 w1.O :=
          hilbert_sameRay_of_between
            Geo w1.A A2 w1.O
            ((HilbertOrder.between_incidence
              w1.O A2 w1.A hOA2A1).2.2.2.2)

        have hFinalAngle :
            Geo.AngleCongruent w1.O A2 B2 w1.O w1.A w1.B := by
          unfold Geometry.Geo.AngleCongruent at hCorresponding ⊢
          rw [hilbert_angle_eq_of_sameRay_first
            Geo w1.A A2 w1.O w1.B hRaySameO1A2] at hCorresponding
          exact hCorresponding

        --------------------------------------------------------
        -- Right angle at `O1` transports to `(A2, B2)`.
        --------------------------------------------------------
        have hRightA2B2 : HilbertRightAngle Geo A2 w1.O B2 := by
          rcases w1.hRight with ⟨C, hAOC, hRightCong⟩
          have hCO1 : C ≠ w1.O :=
            (HilbertOrder.between_incidence w1.A w1.O C hAOC).2.1.symm
          have hA2OC : Geo.Between A2 w1.O C :=
            hilbert_between_transport_sameRays
              Geo w1.A w1.O C A2 C
              hAOC hRaySameA1A2 (hilbert_sameRay_refl Geo w1.O C hCO1)
          have hAngleLeft1 :
              Geo.Angle w1.A w1.O w1.B = Geo.Angle A2 w1.O w1.B :=
            hilbert_angle_eq_of_sameRay_first
              Geo w1.O w1.A A2 w1.B hRaySameA1A2
          have hAngleLeft2 :
              Geo.Angle A2 w1.O w1.B = Geo.Angle A2 w1.O B2 :=
            hilbert_angle_eq_of_sameRay_second
              Geo w1.O A2 w1.B B2 hRayB1B2
          have hAngleRight1 :
              Geo.Angle w1.B w1.O C = Geo.Angle B2 w1.O C :=
            hilbert_angle_eq_of_sameRay_first
              Geo w1.O w1.B B2 C hRayB1B2
          refine ⟨C, hA2OC, ?_⟩
          unfold Geometry.Geo.AngleCongruent at hRightCong ⊢
          rw [← hAngleLeft2, ← hAngleLeft1, ← hAngleRight1]
          exact hRightCong

        have hAOBswap : ¬ PrimCollinear Geo w1.A w1.O w1.B := fun h =>
          w1.hNoncol (PrimCollinearSwap Geo w1.A w1.O w1.B h)

        have hNoncolOA2B2 : ¬ PrimCollinear Geo w1.O A2 B2 := by
          intro h
          exact
            (hilbert_noncollinear_of_sameRays
              Geo w1.A w1.O w1.B A2 B2 hAOBswap hRaySameA1A2 hRayB1B2)
              (PrimCollinearSwap Geo w1.O A2 B2 h)

        have hFirstD :
            hilbertPositiveSegmentClassOf Geo w1.O B2 hO1B2 =
              hilbertPositiveSegmentClassOf Geo U V hUV :=
          Quotient.sound hO1B2_UV

        refine
          ⟨hilbertPositiveSegmentClassOf Geo w1.O A2 hOA2, w1,
            { O := w1.O
              A := A2
              B := B2
              hOA := hOA2
              hOB := hO1B2
              hNoncol := hNoncolOA2B2
              hRight := hRightA2B2
              hFirst := hFirstD
              hSecond := rfl },
            Geometry.Geo.angle_congruent_symmetry
              Geo w1.O A2 B2 w1.O w1.A w1.B hFinalAngle⟩

      · exfalso
        rcases hMeetBA with ⟨X, hBXA, hXl⟩
        have hXbl : HilbertIncidence.OnLine X bl := by
          have hData := HilbertOrder.between_incidence w1.B X w1.A hBXA
          rcases hData.2.2.2.1 with ⟨q, hBq, hXq, hAq⟩
          have hqbl : q = bl :=
            HilbertPlaneIncidence.line_unique
              w1.B w1.A hA1B1.symm q bl hBq hAq hB1bl hAbl
          exact hqbl ▸ hXq
        have hX_B1A1 : X ∈ Geo.PointLine w1.B w1.A :=
          (hilbert_mem_pointLine_iff_onLine
            Geo w1.B w1.A X bl hA1B1.symm hB1bl hAbl).mpr hXbl
        have hX_B2Qp : X ∈ Geo.PointLine B2 Qp :=
          (hilbert_mem_pointLine_iff_onLine
            Geo B2 Qp X l hB2Qp hB2l hQpl).mpr hXl
        exact
          intersection_test_not_parallel_of_common_point
            Geo w1.B w1.A B2 Qp X hX_B1A1 hX_B2Qp hParallel

/-- [ELEM] The fourth proportional exists. -/
theorem hilbertPositiveSegmentMul_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    ∃ x : HilbertPositiveSegmentClass Geo,
      HilbertPositiveSegmentProportion Geo
        (hilbertUnitSegment Geo) a b x :=
  hilbertPositiveSegmentProportion_fourth_exists
    Geo (hilbertUnitSegment Geo) a b

/--
[ELEM] The fourth proportional is unique.

Two right triangles with congruent acute angles and congruent adjacent
legs are congruent, so the opposite leg is determined.  This is
segment-construction uniqueness plus ASA, not proportion theory.
-/
theorem hilbertPositiveSegmentMul_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b x y : HilbertPositiveSegmentClass Geo)
    (hx : HilbertPositiveSegmentProportion Geo
            (hilbertUnitSegment Geo) a b x)
    (hy : HilbertPositiveSegmentProportion Geo
            (hilbertUnitSegment Geo) a b y) :
    x = y :=
  sorry

/-- The product of two positive segment classes. -/
noncomputable def hilbertPositiveSegmentMul
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentClass Geo :=
  Classical.choose
    (hilbertPositiveSegmentMul_exists Geo a b)

theorem hilbertPositiveSegmentMul_spec
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentProportion Geo
      (hilbertUnitSegment Geo) a b
      (hilbertPositiveSegmentMul Geo a b) :=
  Classical.choose_spec
    (hilbertPositiveSegmentMul_exists Geo a b)

------------------------------------------------------------------------
-- Part 2.  The laws
------------------------------------------------------------------------

/-- [ELEM] -/
theorem hilbertPositiveSegmentMul_one
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo a (hilbertUnitSegment Geo) = a :=
  sorry

/--
[PASCAL] Commutativity.

Hilbert, Theorem 42.  This is the point where sec. 14 is consumed:
the two right triangles realizing a * b and b * a share a vertex, and
special Pascal supplies the missing parallel.
-/
theorem hilbertPositiveSegmentMul_comm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo a b =
      hilbertPositiveSegmentMul Geo b a :=
  sorry

/-- [PASCAL] Associativity.  Hilbert, Theorem 42. -/
theorem hilbertPositiveSegmentMul_assoc
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo
        (hilbertPositiveSegmentMul Geo a b) c =
      hilbertPositiveSegmentMul Geo a
        (hilbertPositiveSegmentMul Geo b c) :=
  sorry

/--
[ELEM] Distributivity.

Laying off b and c consecutively on one leg and cutting by parallels.
No Pascal: only the parallel axiom and additivity of segment laying
off.  This is the law the `split` field of HilbertTriangleWeight needs.
-/
theorem hilbertPositiveSegmentMul_add
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo a
        (hilbertPositiveSegmentAdd Geo b c) =
      hilbertPositiveSegmentAdd Geo
        (hilbertPositiveSegmentMul Geo a b)
        (hilbertPositiveSegmentMul Geo a c) :=
  sorry

/-- [PASCAL] Cancellation, via commutativity and the order on segments. -/
theorem hilbertPositiveSegmentMul_left_cancel
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (h : hilbertPositiveSegmentMul Geo a b =
           hilbertPositiveSegmentMul Geo a c) :
    b = c :=
  sorry

------------------------------------------------------------------------
-- Part 3.  The valuation target
--
-- HilbertScissorsValuation needs an AddCommMonoid, and
-- eq_of_equicomplementable needs cancellation.  Positive segment
-- classes have no zero, so one is adjoined.  The empty scissors term
-- maps to `none`.
------------------------------------------------------------------------

/-- Positive segment classes with a formal zero. -/
abbrev HilbertArea
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :=
  Option (HilbertPositiveSegmentClass Geo)

/--
[ELEM] The three laws are already available:
`hilbertPositiveSegmentAdd_comm`, `hilbertPositiveSegment_add_assoc`,
`hilbertPositiveSegment_add_right_cancel`.  Only the plumbing through
`Option` is new.
-/
noncomputable instance
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    AddCancelCommMonoid (HilbertArea Geo) :=
  sorry

------------------------------------------------------------------------
-- Part 4.  Base and altitude
------------------------------------------------------------------------

/--
`b` is the class of the side `B C` and `h` the class of the
perpendicular dropped from `A` to the line `B C`.
-/
def HilbertTriangleBaseAltitude
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (b h : HilbertPositiveSegmentClass Geo) : Prop :=
  sorry

/-- [ELEM] Every nondegenerate triangle has a base and an altitude. -/
theorem hilbertTriangleBaseAltitude_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    ∃ b h : HilbertPositiveSegmentClass Geo,
      HilbertTriangleBaseAltitude Geo A B C b h :=
  sorry

/--
[PASCAL] The product of a base and its altitude does not depend on
which side is taken as base.

Hilbert, sec. 20, from the similarity of the two triangles cut off by
the altitudes, i.e. Theorem 41.  This is the second and last essential
use of proportion theory.
-/
theorem hilbertTriangleBaseAltitude_independent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (b h b' h' : HilbertPositiveSegmentClass Geo)
    (hbh : HilbertTriangleBaseAltitude Geo A B C b h)
    (hbh' : HilbertTriangleBaseAltitude Geo B C A b' h') :
    hilbertPositiveSegmentMul Geo b h =
      hilbertPositiveSegmentMul Geo b' h' :=
  sorry

------------------------------------------------------------------------
-- Part 5.  The area weight
--
-- Note: no halving.  Hilbert's 1/2 is needed only to compare triangles
-- with rectangles; for I.39 the product itself is enough.
------------------------------------------------------------------------

/--
The area of a formal triangle term: the product of a base and the
corresponding altitude, and `none` on degenerate terms.
-/
noncomputable def hilbertAreaOfTriangleTerm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (T : HilbertTriangleTerm Geo) :
    HilbertArea Geo :=
  sorry

/--
The area weight.

`split` reduces to `hilbertPositiveSegmentMul_add`, because the three
triangles share the altitude from `A` to the line `B C`.

`congruent` reduces to congruence of bases together with uniqueness of
the perpendicular, so congruent triangles have congruent altitudes.

Neither field needs Pascal directly; both consume Part 2.
-/
noncomputable def hilbertAreaWeight
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo] :
    HilbertTriangleWeight Geo (HilbertArea Geo) :=
  sorry

/-- [ELEM] A nondegenerate triangle has nonzero area. -/
theorem hilbertAreaWeight_pos
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    (hilbertAreaWeight Geo).weight
        (hilbertTriangleTerm Geo A B C) ≠ 0 :=
  sorry

------------------------------------------------------------------------
-- Part 6.  Discharge
--
-- Replaces the axiom in HilbertScissorsPositivity.lean.  Once Parts
-- 1-5 are in place this proof is complete as written; nothing further
-- about triangles is required.
------------------------------------------------------------------------

theorem hilbert_scissors_triangle_positive'
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (P : HilbertScissorsTerm Geo)
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    ¬ HilbertScissorsEquicomplementable Geo
        (P + hilbertScissorsTriangle Geo A B C)
        P := by

  intro hEq

  have hVal :=
    HilbertScissorsValuation.eq_of_equicomplementable
      Geo
      (HilbertTriangleWeight.toValuation Geo (hilbertAreaWeight Geo))
      hEq

  rw [(HilbertTriangleWeight.toValuation
        Geo (hilbertAreaWeight Geo)).map_add] at hVal

  have hZero :
      (HilbertTriangleWeight.toValuation
          Geo (hilbertAreaWeight Geo)).value
        (hilbertScissorsTriangle Geo A B C) = 0 := by
    have := hVal.trans (add_zero _).symm
    exact add_left_cancel this

  exact
    hilbertAreaWeight_pos Geo A B C hNoncol
      (by simpa [HilbertTriangleWeight.toValuation,
                 hilbertScissorsTriangle] using hZero)

#print axioms hilbert_scissors_triangle_positive'

end Geometry

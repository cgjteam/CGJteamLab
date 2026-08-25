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

Split by `hilbert_between_trichotomy` on `O1, B1, B2`: the degenerate
case `c = a` (`B2 = B1`, `d := b`) and the "shrinking" case `c ≤ a`
(`B2` between `O1, B1`, via Pasch + Euclid I.29 corresponding angles)
are both discharged in full below.  The remaining "growing" case
`c > a` (`B1` between `O1, B2`) is recorded as a single `sorry`; see
the comment at that point -- it is *not* just a missing transcription,
it needs a genuinely different ("exterior Pasch") construction that
has not yet been found.
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
    -- Goal 1, `hCase2 : Between w1.O w1.B B2`  (c > a, "growing"
    -- case).  Construction after Hartshorne / Hilbert (see the
    -- comment on `hilbert_right_triangle_third_angle_congruent`
    -- above): copy `β := ∠(w1.A, w1.B, w1.O)` onto `B2`, on the side
    -- opposite `w1.A`; the copied ray's line meets `line(w1.O, w1.A)`
    -- (else `β` would be congruent to a right angle, contradicting
    -- `β < right angle`); call the meeting point `A2`.  The right
    -- angle at `w1.O` transports to `(A2, B2)` since `A2, w1.O, w1.A`
    -- are collinear, and the third-angle lemma then gives the needed
    -- angle match at `A2`.
    ----------------------------------------------------------------

    · have hABO : ¬ PrimCollinear Geo w1.A w1.B w1.O := fun h =>
        w1.hNoncol
          (PrimCollinearCycle Geo w1.B w1.O w1.A
            (PrimCollinearCycle Geo w1.A w1.B w1.O h))

      have hBAO : ¬ PrimCollinear Geo w1.B w1.A w1.O := fun h =>
        hABO (PrimCollinearSwap Geo w1.B w1.A w1.O h)

      have hNoncolAOB : ¬ PrimCollinear Geo w1.A w1.O w1.B := fun h =>
        w1.hNoncol (PrimCollinearSwap Geo w1.A w1.O w1.B h)

      rcases w1.hRight with ⟨Cext, hAOCext, hRightCongOrig⟩

      ----------------------------------------------------------------
      -- `β` is strictly less than a right angle.
      ----------------------------------------------------------------

      have hβLess :
          HilbertAngleLess Geo w1.A w1.B w1.O w1.A w1.O w1.B := by
        have hRaw :
            HilbertAngleLess Geo w1.A w1.B w1.O w1.B w1.O Cext :=
          euclid_proposition_16_first Geo w1.B w1.A w1.O Cext hBAO hAOCext
        exact
          hilbert_angleLess_transport_right
            Geo w1.A w1.B w1.O w1.B w1.O Cext w1.A w1.O w1.B
            hRaw hNoncolAOB
            (Geometry.Geo.angle_congruent_symmetry
              Geo w1.A w1.O w1.B w1.B w1.O Cext hRightCongOrig)

      ----------------------------------------------------------------
      -- Copy `β` onto vertex `B2`, arm preserved towards `w1.O`, on
      -- the side of `legB := line(w1.O, B2)` opposite `w1.A` (i.e.
      -- the side of `Cext`, since `A1, O1, Cext` are collinear with
      -- `O1` between them, `Cext` is on the opposite ray of
      -- `line(w1.O, w1.A)` from `w1.A`, hence the opposite side of
      -- `legB`).
      ----------------------------------------------------------------

      obtain ⟨legB, hO1legB, hB2legB⟩ :=
        HilbertPlaneIncidence.line_through w1.O B2 hO1B2

      have hA1legB : ¬ HilbertIncidence.OnLine w1.A legB := by
        intro h
        rcases hCollO1B1B2 with ⟨m, hO1m, hB1m, hB2m⟩
        have hlm : legB = m :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2 legB m hO1legB hB2legB hO1m hB2m
        exact w1.hNoncol ⟨m, hO1m, hlm ▸ h, hB1m⟩

      have hCextO : Cext ≠ w1.O :=
        (HilbertOrder.between_incidence w1.A w1.O Cext hAOCext).2.1.symm

      have hCextlegB : ¬ HilbertIncidence.OnLine Cext legB := by
        intro h
        obtain ⟨p, hAp, hOp⟩ :=
          HilbertPlaneIncidence.line_through w1.A w1.O w1.hOA.symm
        have hCextp : HilbertIncidence.OnLine Cext p := by
          have hData := HilbertOrder.between_incidence w1.A w1.O Cext hAOCext
          rcases hData.2.2.2.1 with ⟨q, hAq, hOq, hCextq⟩
          have hqp : q = p :=
            HilbertPlaneIncidence.line_unique
              w1.A w1.O w1.hOA.symm q p hAq hOq hAp hOp
          exact hqp ▸ hCextq
        have hplegB : p = legB :=
          HilbertPlaneIncidence.line_unique
            w1.O Cext hCextO.symm p legB hOp hCextp hO1legB h
        exact hA1legB (hplegB ▸ hAp)

      obtain ⟨D2, hD2Side, hAngleD2, _⟩ :=
        HilbertCongruence.angle_construction
          w1.A w1.B w1.O w1.O B2 Cext
          hABO hO1B2 legB hO1legB hB2legB hCextlegB

      have hOppAC : HilbertOppositeSide Geo w1.A Cext legB :=
        ⟨hA1legB, hCextlegB, ⟨w1.O, hAOCext, hO1legB⟩⟩

      have hOppositeD2 : HilbertOppositeSide Geo w1.A D2 legB :=
        hilbert_oppositeSide_transport_right Geo w1.A Cext D2 legB hOppAC
          (hilbert_sameSide_symm Geo D2 Cext legB hD2Side)

      ----------------------------------------------------------------
      -- The carrier `m` of ray `B2 → D2` is not parallel to
      -- `n := line(w1.O, w1.A)`: otherwise alternate angles for the
      -- transversal `legB` would force `β ≅` a right angle,
      -- contradicting `hβLess`.
      ----------------------------------------------------------------

      obtain ⟨n, hOn, hAn⟩ :=
        HilbertPlaneIncidence.line_through w1.O w1.A w1.hOA

      have hB2D2 : B2 ≠ D2 := by
        intro h
        exact hOppositeD2.2.1 (h ▸ hB2legB)

      obtain ⟨m, hB2m, hD2m⟩ :=
        HilbertPlaneIncidence.line_through B2 D2 hB2D2

      have hE : ∃ E, Geo.Between w1.O E B2 :=
        hilbert_between_exists Geo w1.O B2 hO1B2

      obtain ⟨E, hOEB2⟩ := hE

      have hMeet : HilbertLinesMeet Geo n m := by
        by_contra hDisjoint
        have hParallel_nm : Geo.Parallel w1.O w1.A B2 D2 :=
          intersection_test_parallel_of_lines_disjoint
            Geo w1.O w1.A B2 D2 n m
            w1.hOA hB2D2 hOn hAn hB2m hD2m hDisjoint
        have hEn2 : Geo.AngleCongruent E w1.O w1.A E B2 D2 :=
          hilbert_alternate_angles_of_parallel_oppositeSide_lines
            Geo w1.O w1.A B2 E D2 legB
            hOEB2 hO1legB hB2legB hOppositeD2 hParallel_nm
        have hRayEB2 : HilbertSameRay Geo w1.O E B2 :=
          hilbert_sameRay_of_between Geo w1.O E B2 hOEB2
        have hAngleEOA :
            Geo.Angle E w1.O w1.A = Geo.Angle B2 w1.O w1.A :=
          hilbert_angle_eq_of_sameRay_first Geo w1.O E B2 w1.A hRayEB2
        have hRayB2E : HilbertSameRay Geo B2 E w1.O := by
          have hB2EO : Geo.Between B2 E w1.O :=
            (HilbertOrder.between_incidence w1.O E B2 hOEB2).2.2.2.2
          exact hilbert_sameRay_of_between Geo B2 E w1.O hB2EO
        have hAngleED2 :
            Geo.Angle E B2 D2 = Geo.Angle w1.O B2 D2 :=
          hilbert_angle_eq_of_sameRay_first Geo B2 E w1.O D2 hRayB2E

        have hEn2' : Geo.AngleCongruent B2 w1.O w1.A w1.O B2 D2 := by
          unfold Geometry.Geo.AngleCongruent at hEn2 ⊢
          rw [← hAngleEOA, ← hAngleED2]
          exact hEn2

        have hB2OA_β : Geo.AngleCongruent B2 w1.O w1.A w1.A w1.B w1.O :=
          Geometry.Geo.angle_congruent_transitivity
            Geo B2 w1.O w1.A w1.O B2 D2 w1.A w1.B w1.O
            hEn2'
            (Geometry.Geo.angle_congruent_symmetry
              Geo w1.A w1.B w1.O w1.O B2 D2 hAngleD2)

        have hStepA : Geo.AngleCongruent w1.A w1.O B2 w1.A w1.B w1.O :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo B2 w1.O w1.A w1.A w1.B w1.O).mp hB2OA_β

        have hRaySymm : HilbertSameRay Geo w1.O B2 w1.B :=
          hilbert_sameRay_symm Geo w1.O w1.B B2 hRayB1B2

        have hAOB2_AOB :
            Geo.Angle w1.A w1.O B2 = Geo.Angle w1.A w1.O w1.B :=
          hilbert_angle_eq_of_sameRay_second Geo w1.O w1.A B2 w1.B hRaySymm

        have hStepB : Geo.AngleCongruent w1.A w1.O w1.B w1.A w1.B w1.O := by
          unfold Geometry.Geo.AngleCongruent at hStepA ⊢
          rw [← hAOB2_AOB]
          exact hStepA

        have hFinalLess : HilbertAngleLess Geo w1.A w1.B w1.O w1.A w1.B w1.O :=
          hilbert_angleLess_transport_right
            Geo w1.A w1.B w1.O w1.A w1.O w1.B w1.A w1.B w1.O
            hβLess hABO hStepB

        exact hilbert_angleLess_irrefl Geo w1.A w1.B w1.O hFinalLess

      ----------------------------------------------------------------
      -- `A2 := n ∩ m`.  REMAINING WORK: characterize `A2`'s ray from
      -- `w1.O` relative to `w1.A` (`hilbert_between_trichotomy` on
      -- `w1.A, w1.O, A2`, and separately relative to `D2, B2, A2`
      -- (`A2 ≠ w1.O` is immediate: `A2 ∈ legB` would force `A2 = w1.O`,
      -- the only point of `n ∩ legB`, since `w1.A ∉ legB`; similarly
      -- `A2 ≠ B2` from `B2 ∉ n`).  The natural case split is
      -- `by_cases` on `Geo.Between w1.A w1.O A2` (only 2 cases, not a
      -- full trichotomy, directly from `HilbertSameRay`'s own
      -- definition when it fails).  The two ray-relations are NOT
      -- independent: `legB` meets `n` only at `w1.O` and meets `m`
      -- only at `B2` (`m ≠ legB` since `m` crosses it at angle `β ≠ 0,
      -- 180`), so each of the two rays of `n` from `w1.O`, and each of
      -- the two rays of `m` from `B2`, lies entirely on one side of
      -- `legB`; since `D2`'s ray (from `B2`) is on the side opposite
      -- `w1.A` (`hOppositeD2`), `A2` is on `w1.A`'s ray of `n` iff it
      -- is on the ray of `m` OPPOSITE `D2`, and on the opposite ray of
      -- `n` iff it is on `D2`'s own ray of `m` -- i.e. the same
      -- `by_cases` split determines both relations at once, it just
      -- needs proving for `m` the same way it would be proved for
      -- `n` (same-side-of-a-line-via-no-segment-crossing, as for
      -- `hSameSideB2B1`/`hNoMeetB1B2n` in Goal 3 above, or via
      -- `hilbert_between_points_sameSide_transversal` used inside
      -- `euclid_proposition_32_exterior`'s own proof).
      --
      -- Given the right ray-relations: same-ray case, transport the
      -- right angle and the `β`-angle via `hilbert_angle_eq_of_sameRay_first`/
      -- `_second` (plain `Angle` equalities, lifted to `AngleCongruent`
      -- by the `unfold; rw; exact` pattern used throughout this file,
      -- e.g. Goal 3's `hRightA2B2`).  Opposite-ray case: via
      -- `hilbert_right_angle_chosen_supplement` for the right angle
      -- (exactly as sketched previously) and the same kind of
      -- same-ray transport for the `β`-angle (now from the ray
      -- OPPOSITE `D2`, using `hilbert_sameRay_symm`/`hilbert_between_transport_sameRays`
      -- as needed).  Either way this gives `HilbertRightAngle Geo A2
      -- w1.O B2` (via `hilbert_right_angle_of_congruent`) and
      -- `AngleCongruent w1.A w1.B w1.O A2 w1.O B2`-ish (i.e. the
      -- `hAngleB` hypothesis of `hilbert_right_triangle_third_angle_congruent`,
      -- applied with `(O,A,B) := (w1.O, A2, B2)` and `(O',A',B') :=
      -- (w1.O, w1.A, w1.B)`); its conclusion `AngleCongruent w1.O A2
      -- B2 w1.O w1.A w1.B`, reversed
      -- (`angle_congruent_symmetry`), is exactly `hFinalAngle` in
      -- Goal 3's sense.  Package `⟨class(w1.O, A2), w1, {witness2},
      -- hFinalAngle⟩` exactly as in Goal 3's final `refine`
      -- (`hFirst := Quotient.sound hO1B2_UV`, `hSecond := rfl`,
      -- `hNoncol` via `hilbert_noncollinear_of_sameRays` as in Goal 3).
      ----------------------------------------------------------------

      rcases hMeet with ⟨A2, hA2n, hA2m⟩

      have hA2O : A2 ≠ w1.O := by
        intro h
        have hOm : HilbertIncidence.OnLine w1.O m := by
          rw [← h]
          exact hA2m
        have hmlegB : m = legB :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2
            m legB
            hOm hB2m
            hO1legB hB2legB
        exact hOppositeD2.2.1 (hmlegB ▸ hD2m)

      have hA2B2 : A2 ≠ B2 := by
        intro h
        have hB2n : HilbertIncidence.OnLine B2 n := by
          rw [← h]
          exact hA2n
        have hnlegB : n = legB :=
          HilbertPlaneIncidence.line_unique
            w1.O B2 hO1B2
            n legB
            hOn hB2n
            hO1legB hB2legB
        exact hA1legB (hnlegB ▸ hAn)

      have hA2legB :
          ¬ HilbertIncidence.OnLine A2 legB := by
        intro h
        have hnlegB : n = legB :=
          HilbertPlaneIncidence.line_unique
            w1.O A2 hA2O.symm
            n legB
            hOn hA2n
            hO1legB h
        exact hA1legB (hnlegB ▸ hAn)

      sorry

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

  ------------------------------------------------------------------
  -- REMAINING: Case 2 (`hCase2 : Between w1.O w1.B B2`, c > a) at
  -- Goal 1 above is still `sorry`.
  --
  -- The Goal-3 (Thales/Pasch) technique above is the WRONG model for
  -- this case -- and, in hindsight, it is not how Hilbert or
  -- Hartshorne actually build the fourth proportional at all.  Both
  -- (Hilbert, Grundlagen sec. 15; Hartshorne, *Geometry: Euclid and
  -- Beyond*, sec. 19, Definition before Prop. 19.2) construct a
  -- product/ratio by building the SECOND right triangle from
  -- scratch -- copying an angle and erecting a perpendicular -- never
  -- by extending a shared axis and cutting with a parallel.  That
  -- construction has NO case split on which of two given segments is
  -- longer, because it never compares them; it only ever compares an
  -- angle against a right angle.  Concretely, for our shape
  -- (`HilbertPositiveSegmentRatioWitness`, angle at the vertex
  -- adjacent to the given/wanted legs, not at the right-angle
  -- vertex), the construction is:
  --
  --  1. Let `β := ∠(w1.A, w1.B, w1.O)` (vertex `w1.B`), the OTHER
  --     acute angle of witness `w1`, i.e. the complement of `θ`.
  --  2. `β` is strictly less than a right angle: apply
  --     `euclid_proposition_16_first` (Proposition16.lean) to the
  --     triangle `(w1.B, w1.A, w1.O)`, extending side `w1.A–w1.O`
  --     through `w1.O` to the SAME point `C` already provided by
  --     `w1.hRight` (`w1.hRight : ∃C, Between w1.A w1.O C ∧
  --     AngleCongruent w1.A w1.O w1.B w1.B w1.O C`) -- no fresh
  --     extension point is needed.  This gives
  --     `HilbertAngleLess Geo w1.A w1.B w1.O w1.B w1.O C`, and
  --     transporting the right side along `w1.hRight`'s own
  --     congruence (`hilbert_angleLess_transport_right`) gives
  --     `HilbertAngleLess Geo w1.A w1.B w1.O w1.A w1.O w1.B`, i.e.
  --     `β` is less than the right angle at `w1.O`.
  --  3. Copy `β` onto vertex `B2`, arm preserved towards `w1.O`
  --     (`angle_construction`, base line `= line(w1.O, B2)`), on the
  --     side containing `w1.A`.  This gives a ray from `B2`; let `m`
  --     be its carrier line.
  --  4. `m` is not parallel to `n := line(w1.O, w1.A)`: if it were,
  --     since `legB := line(w1.O, B2) ⊥ n` already (same right angle
  --     as `w1.hRight`, transported along `HilbertSameRay Geo w1.O
  --     w1.B B2 = hRayB1B2`), corresponding angles for the transversal
  --     `legB` crossing the parallels `m, n` would force the angle
  --     `m` makes with `legB` at `B2` (`= β`, by construction) to be
  --     congruent to the angle `n` makes with `legB` at `w1.O`
  --     (`=` a right angle).  That contradicts step 2
  --     (`hilbert_angleLess_irrefl`, after transporting `β`'s
  --     partner to `β` itself via the derived congruence).  Hence,
  --     as in Goal 3, `m` and `n` meet (`hilbert_parallel_transitive_distinct`
  --     + `intersection_test_not_parallel_of_common_point`, no Pasch
  --     needed since this argument does not depend on any
  --     betweenness case).  Call the meeting point `A2`.
  --  5. The remaining gap: show `∠(w1.O, A2, B2) ≅ θ`.  On reflection
  --     (after reading Hilbert's own §16 and Hartshorne 19.2(5)) this
  --     is NOT the general "AA similarity" fact and does NOT need
  --     Hartshorne's incenter argument (Prop. 20.1) -- that argument
  --     is for *arbitrary* equiangular triangles.  Both `(w1.O, w1.A,
  --     w1.B)` and `(w1.O, A2, B2)` already have a RIGHT angle, so
  --     their third angle is pinned down by `euclid_proposition_32`
  --     (I.32, angle sum = two right angles) alone, applied once to
  --     EACH triangle, exactly as Hartshorne does for the
  --     multiplicative-inverse case (19.2(5)): "let β be the other
  --     acute angle [of the first triangle]... since the other angle
  --     [of the second triangle] is β (I.32), ab = 1" -- no
  --     incenter, no comparison of the two triangles against each
  --     other, just the same numeric fact (`180 - 90 - β`) instantiated
  --     twice.  The remaining work is to extract this cleanly from
  --     `HilbertTriangleAnglesEqualTwoRightAngles` /
  --     `HilbertExteriorAngleEqualsRemoteAngles` (Proposition32.lean),
  --     which package I.32 as an exterior-angle-splitting statement
  --     (a point `R` with `∠BAC ≅ ∠ACR` and `∠ABC ≅ ∠RCD`) rather
  --     than a numeric equation, so turning "two triangles agree on
  --     two angles out of three, hence agree on the third" into a
  --     couple of lines of `AngleCongruent` bookkeeping is still
  --     genuine (if now clearly bounded) work; not yet done.  Steps
  --     1-4 above are believed correct and mostly follow patterns
  --     already used and verified in Goal 3.
  ------------------------------------------------------------------

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

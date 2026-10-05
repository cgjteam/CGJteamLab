import CGJteamLab.HilbertInterfaceV
import CGJteamLab.Proposition5_14
import CGJteamLab.Proposition10
import CGJteamLab.MidsegmentParallel
import CGJteamLab.Proposition29

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- HilbertInterfaceVI
--
-- First bridge from concrete segment congruence to the Eudoxus
-- proportion language used by Book V and the forthcoming Book VI.
------------------------------------------------------------------------


/--
Congruent nondegenerate segments determine the same positive
segment class.

This is the quotient-level bridge used repeatedly in Book VI.
-/
theorem hilbertPositiveSegmentClassOf_eq_of_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hAB : Ne A B)
    (hCD : Ne C D)
    (hCong : Geo.Congruent A B C D) :
    hilbertPositiveSegmentClassOf Geo A B hAB =
      hilbertPositiveSegmentClassOf Geo C D hCD := by

  exact Quotient.sound hCong


/--
Two pairs of congruent positive segments determine equal Eudoxus
ratios.

If

    AB ~= CD
    EF ~= GH,

then

    AB : EF = CD : GH

in the Eudoxus language of Book V.

No Archimedean argument is needed: after passing to quotient classes,
both corresponding terms are literally equal.
-/
theorem hilbertEudoxusProportion_of_congruent_pairs
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F G H : Geo.Point)
    (hAB : Ne A B)
    (hCD : Ne C D)
    (hEF : Ne E F)
    (hGH : Ne G H)
    (hABCD : Geo.Congruent A B C D)
    (hEFGH : Geo.Congruent E F G H) :
    HilbertEudoxusProportion
      Geo
      (hilbertPositiveSegmentClassOf Geo A B hAB)
      (hilbertPositiveSegmentClassOf Geo E F hEF)
      (hilbertPositiveSegmentClassOf Geo C D hCD)
      (hilbertPositiveSegmentClassOf Geo G H hGH) := by

  have hNum :
      hilbertPositiveSegmentClassOf Geo A B hAB =
        hilbertPositiveSegmentClassOf Geo C D hCD :=
    hilbertPositiveSegmentClassOf_eq_of_congruent
      Geo A B C D hAB hCD hABCD

  have hDen :
      hilbertPositiveSegmentClassOf Geo E F hEF =
        hilbertPositiveSegmentClassOf Geo G H hGH :=
    hilbertPositiveSegmentClassOf_eq_of_congruent
      Geo E F G H hEF hGH hEFGH

  rw [hNum, hDen]

  exact
    hilbertEudoxusProportion_refl
      Geo
      (hilbertPositiveSegmentClassOf Geo C D hCD)
      (hilbertPositiveSegmentClassOf Geo G H hGH)


/--
Equal radial cuts give the Eudoxus proportion needed as input to
the converse direction of Euclid VI.2.

Configuration:

    O - P - L
    O - Q - M

with

    OP ~= OQ
    OL ~= OM.

Segment subtraction gives

    PL ~= QM,

hence

    OP : PL = OQ : QM.

This theorem deliberately stops at the proportion.  The conclusion

    PQ || LM

is the genuinely VI.2 step and is not hidden here.
-/
theorem hilbertEudoxusProportion_of_equal_radial_cuts
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O P L Q M : Geo.Point)
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hOPOQ : Geo.Congruent O P O Q)
    (hOLOM : Geo.Congruent O L O M) :
    HilbertEudoxusProportion
      Geo
      (hilbertPositiveSegmentClassOf
        Geo O P
        (HilbertOrder.between_incidence O P L hOPL).1)
      (hilbertPositiveSegmentClassOf
        Geo P L
        (HilbertOrder.between_incidence O P L hOPL).2.1)
      (hilbertPositiveSegmentClassOf
        Geo O Q
        (HilbertOrder.between_incidence O Q M hOQM).1)
      (hilbertPositiveSegmentClassOf
        Geo Q M
        (HilbertOrder.between_incidence O Q M hOQM).2.1) := by

  have hPLQM :
      Geo.Congruent P L Q M :=
    bookZero_differenceOfParts
      Geo
      O P L
      O Q M
      hOPOQ
      hOLOM
      hOPL
      hOQM

  exact
    hilbertEudoxusProportion_of_congruent_pairs
      Geo
      O P
      O Q
      P L
      Q M
      (HilbertOrder.between_incidence O P L hOPL).1
      (HilbertOrder.between_incidence O Q M hOQM).1
      (HilbertOrder.between_incidence O P L hOPL).2.1
      (HilbertOrder.between_incidence O Q M hOQM).2.1
      hOPOQ
      hPLQM


/--
The same equal-radial-cut data also give the whole-side proportion

    OP : OL = OQ : OM.

This form is not the classical statement of VI.2, but it is a useful
normalization lemma for later Book VI arguments.
-/
theorem hilbertEudoxusProportion_of_equal_radial_wholes
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O P L Q M : Geo.Point)
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hOPOQ : Geo.Congruent O P O Q)
    (hOLOM : Geo.Congruent O L O M) :
    HilbertEudoxusProportion
      Geo
      (hilbertPositiveSegmentClassOf
        Geo O P
        (HilbertOrder.between_incidence O P L hOPL).1)
      (hilbertPositiveSegmentClassOf
        Geo O L
        (HilbertOrder.between_incidence O P L hOPL).2.2.1)
      (hilbertPositiveSegmentClassOf
        Geo O Q
        (HilbertOrder.between_incidence O Q M hOQM).1)
      (hilbertPositiveSegmentClassOf
        Geo O M
        (HilbertOrder.between_incidence O Q M hOQM).2.2.1) := by

  exact
    hilbertEudoxusProportion_of_congruent_pairs
      Geo
      O P
      O Q
      O L
      O M
      (HilbertOrder.between_incidence O P L hOPL).1
      (HilbertOrder.between_incidence O Q M hOQM).1
      (HilbertOrder.between_incidence O P L hOPL).2.2.1
      (HilbertOrder.between_incidence O Q M hOQM).2.2.1
      hOPOQ
      hOLOM



------------------------------------------------------------------------
-- VI.2 target language
------------------------------------------------------------------------

/--
Forward direction of Euclid VI.2 in the Book V Eudoxus language.

If XYZ is a noncollinear triangle, E and F divide the two sides XY
and XZ, and EF is parallel to YZ, then the adjacent parts are
proportional:

    XE : EY = XF : FZ.
-/
def HilbertVI2EudoxusForward
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop :=
  forall X E Y F Z : Geo.Point,
    forall _hXYZ : Not (Collinear Geo X Y Z),
    forall hXEY : Geo.Between X E Y,
    forall hXFZ : Geo.Between X F Z,
      Geo.Parallel E F Y Z ->
      HilbertEudoxusProportion
        Geo
        (hilbertPositiveSegmentClassOf
          Geo X E
          (HilbertOrder.between_incidence X E Y hXEY).1)
        (hilbertPositiveSegmentClassOf
          Geo E Y
          (HilbertOrder.between_incidence X E Y hXEY).2.1)
        (hilbertPositiveSegmentClassOf
          Geo X F
          (HilbertOrder.between_incidence X F Z hXFZ).1)
        (hilbertPositiveSegmentClassOf
          Geo F Z
          (HilbertOrder.between_incidence X F Z hXFZ).2.1)


/--
Converse direction of Euclid VI.2 in the Book V Eudoxus language.

If XYZ is a noncollinear triangle and E and F divide the two sides
XY and XZ proportionally, then the joining segment EF is parallel to
YZ.
-/
def HilbertVI2EudoxusConverse
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop :=
  forall X E Y F Z : Geo.Point,
    forall _hXYZ : Not (Collinear Geo X Y Z),
    forall hXEY : Geo.Between X E Y,
    forall hXFZ : Geo.Between X F Z,
      HilbertEudoxusProportion
        Geo
        (hilbertPositiveSegmentClassOf
          Geo X E
          (HilbertOrder.between_incidence X E Y hXEY).1)
        (hilbertPositiveSegmentClassOf
          Geo E Y
          (HilbertOrder.between_incidence X E Y hXEY).2.1)
        (hilbertPositiveSegmentClassOf
          Geo X F
          (HilbertOrder.between_incidence X F Z hXFZ).1)
        (hilbertPositiveSegmentClassOf
          Geo F Z
          (HilbertOrder.between_incidence X F Z hXFZ).2.1) ->
      Geo.Parallel E F Y Z


/--
Full Euclid VI.2 content in the Eudoxus segment language.
-/
def HilbertVI2Eudoxus
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop :=
  HilbertVI2EudoxusForward Geo /\
  HilbertVI2EudoxusConverse Geo


------------------------------------------------------------------------
-- Plane-order helpers for the constructive VI.2 proof
------------------------------------------------------------------------

/--
If Q and R are both on the opposite side of a line from P,
and P,Q,R are noncollinear, then Q and R are on the same side.

This is a pure incidence/order lemma.
-/
theorem hilbert_two_oppositeSides_sameSide_VI
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P Q R : Geo.Point)
    (l : Geo.Line)
    (hPQR : Not (PrimCollinear Geo P Q R))
    (hPQ : HilbertOppositeSide Geo P Q l)
    (hPR : HilbertOppositeSide Geo P R l) :
    HilbertSameSide Geo Q R l := by

  cases hPQ.2.2 with
  | intro X hPXQ_data =>
      cases hPXQ_data with
      | intro hPXQ hXl =>
          cases hPR.2.2 with
          | intro Y hPYR_data =>
              cases hPYR_data with
              | intro hPYR hYl =>
                  exact
                    hilbert_third_side_endpoints_sameSide
                      Geo P Q R X Y l
                      hPQR hPXQ hPYR hXl hYl


/--
If P and Q are collinear with O on a carrier line, and P,Q lie on
opposite sides of a second line through O, then O lies strictly
between P and Q.

This is the order-normalization lemma needed when a constructed
parallel is intersected with a side of a triangle.
-/
theorem hilbert_between_of_collinear_oppositeSide_VI
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

  cases hOpp.2.2 with
  | intro X hPXQ_data =>
      cases hPXQ_data with
      | intro hPXQ hXbase =>

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



------------------------------------------------------------------------
-- Euclid VI.12 / Hilbert Supplement II: fourth proportional
------------------------------------------------------------------------

/--
The fourth proportional exists in Hilbert's synthetic positive-segment
ratio language.  Given positive segment classes `a`, `b`, `c`, construct
`d` such that

    a : b = c : d.

This is the production form of Euclid VI.12 used by XI.27.  The proof
uses only the existing segment-construction, order, parallel-existence,
and I.29 infrastructure; it does not depend on the unfinished segment
multiplication or area layer.
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
        hilbert_between_of_collinear_oppositeSide_VI
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


------------------------------------------------------------------------
-- Uniqueness of proportional division
------------------------------------------------------------------------

/--
If two Eudoxus ratios are equal and the sums of their two terms are
equal, then the corresponding terms are equal.

This is the magnitude-theoretic uniqueness statement needed for the
converse direction of VI.2.

Mathematically:

    a : b = c : d
    a + b = c + d
    ----------------
    a = c and b = d.

The proof uses V.14.  If a < c, then V.14 gives b < d, hence
a+b < c+d, contradicting equality of the sums.  The case c < a is
symmetric.
-/
theorem hilbertEudoxusProportion_eq_of_equal_sums
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp : HilbertEudoxusProportion Geo a b c d)
    (hSum : a + b = c + d) :
    a = c /\ b = d := by

  cases
      hilbertPositiveSegmentLess_trichotomy
        Geo a c with

  | inl hac =>

      have hbd :
          HilbertPositiveSegmentLess Geo b d :=
        (hilbertEudoxus_v14_lt_iff
          Geo a b c d hProp).1 hac

      have hStrict :
          HilbertPositiveSegmentLess
            Geo
            (a + b)
            (c + d) :=
        hilbertPositiveSegment_add_lt_add
          Geo a c b d hac hbd

      rw [hSum] at hStrict

      exact
        False.elim
          (hilbertPositiveSegmentLess_irrefl
            Geo
            (c + d)
            hStrict)

  | inr hrest =>

      cases hrest with

      | inl hac =>

          have hbd :
              b = d :=
            (hilbertEudoxus_v14_eq_iff
              Geo a b c d hProp).1 hac

          exact And.intro hac hbd

      | inr hca =>

          have hdb :
              HilbertPositiveSegmentLess Geo d b :=
            (hilbertEudoxus_v14_gt_iff
              Geo a b c d hProp).1 hca

          have hStrict :
              HilbertPositiveSegmentLess
                Geo
                (c + d)
                (a + b) :=
            hilbertPositiveSegment_add_lt_add
              Geo c a d b hca hdb

          rw [hSum] at hStrict

          exact
            False.elim
              (hilbertPositiveSegmentLess_irrefl
                Geo
                (c + d)
                hStrict)


/--
A strict betweenness decomposition realizes addition of positive
segment classes as an equality:

    A-B-C  ==>  [AB] + [BC] = [AC].
-/
theorem hilbertPositiveSegmentClassOf_add_of_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    let hAB : Ne A B :=
      (HilbertOrder.between_incidence A B C hABC).1
    let hBC : Ne B C :=
      (HilbertOrder.between_incidence A B C hABC).2.1
    let hAC : Ne A C :=
      (HilbertOrder.between_incidence A B C hABC).2.2.1
    hilbertPositiveSegmentClassOf Geo A B hAB +
      hilbertPositiveSegmentClassOf Geo B C hBC =
        hilbertPositiveSegmentClassOf Geo A C hAC := by

  dsimp

  let hAB : Ne A B :=
    (HilbertOrder.between_incidence A B C hABC).1

  let hBC : Ne B C :=
    (HilbertOrder.between_incidence A B C hABC).2.1

  let hAC : Ne A C :=
    (HilbertOrder.between_incidence A B C hABC).2.2.1

  have hRaw :
      HilbertPositiveSegmentSum
        Geo
        (hilbertPositiveSegmentClassOf Geo A B hAB)
        (hilbertPositiveSegmentClassOf Geo B C hBC)
        (hilbertPositiveSegmentClassOf Geo A C hAC) := by
    simpa [hAB, hBC, hAC] using
      hilbertPositiveSegmentSum_of_between
        Geo A B C hABC

  have hSpec :
      HilbertPositiveSegmentSum
        Geo
        (hilbertPositiveSegmentClassOf Geo A B hAB)
        (hilbertPositiveSegmentClassOf Geo B C hBC)
        (hilbertPositiveSegmentClassOf Geo A B hAB +
          hilbertPositiveSegmentClassOf Geo B C hBC) :=
    hilbertPositiveSegmentAdd_spec
      Geo
      (hilbertPositiveSegmentClassOf Geo A B hAB)
      (hilbertPositiveSegmentClassOf Geo B C hBC)

  have hUnique :
      hilbertPositiveSegmentClassOf Geo A C hAC =
        hilbertPositiveSegmentClassOf Geo A B hAB +
          hilbertPositiveSegmentClassOf Geo B C hBC :=
    hilbertPositiveSegmentSum_unique
      Geo
      (hilbertPositiveSegmentClassOf Geo A B hAB)
      (hilbertPositiveSegmentClassOf Geo B C hBC)
      (hilbertPositiveSegmentClassOf Geo A C hAC)
      (hilbertPositiveSegmentClassOf Geo A B hAB +
        hilbertPositiveSegmentClassOf Geo B C hBC)
      hRaw hSpec

  exact hUnique.symm


/--
Two points on the same ray from O, at congruent distances from O,
are equal.

This is Hilbert III.1 uniqueness of segment construction written in
the form needed for VI.2.
-/
theorem hilbert_sameRay_eq_of_congruent_from_origin
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R P Q : Geo.Point)
    (hRayP : HilbertSameRay Geo O R P)
    (hRayQ : HilbertSameRay Geo O R Q)
    (hCong : Geo.Congruent O P O Q) :
    P = Q := by

  have hOP :
      Geo.Congruent O P O P :=
    hilbert_congruent_reflexive
      Geo O P

  have hOQOP :
      Geo.Congruent O Q O P :=
    hilbert_congruent_symmetry
      Geo O P O Q hCong

  exact
    hilbert_segment_construction_unique
      Geo
      O P
      O R
      P Q
      hRayP
      hRayQ
      hOP
      hOQOP


/--
Two points on the same ray from O are equal when their positive
segment classes from O are equal.
-/
theorem hilbert_sameRay_eq_of_positiveClass_eq
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R P Q : Geo.Point)
    (hRayP : HilbertSameRay Geo O R P)
    (hRayQ : HilbertSameRay Geo O R Q)
    (hClass :
      hilbertPositiveSegmentClassOf
          Geo O P hRayP.2.1.symm =
        hilbertPositiveSegmentClassOf
          Geo O Q hRayQ.2.1.symm) :
    P = Q := by

  have hCong :
      Geo.Congruent O P O Q :=
    Quotient.exact hClass

  exact
    hilbert_sameRay_eq_of_congruent_from_origin
      Geo O R P Q
      hRayP hRayQ hCong



------------------------------------------------------------------------
-- Parallel direction and pointwise parallel projection
------------------------------------------------------------------------

/--
Two nondegenerate point-lines have the same affine direction when
their carriers coincide or when they are parallel.

Unlike Geo.Parallel, this relation is reflexive on a nondegenerate
line.  This matters for parallel projection: the endpoint Y of a
triangle side must project to Z, so the section YZ has the same
direction as itself, not Geo.Parallel Y Z Y Z.
-/
def HilbertSameDirection
    [HilbertIncidence Geo]
    (A B C D : Geo.Point) : Prop :=
  Ne A B /\
  Ne C D /\
  (Geo.PointLine A B = Geo.PointLine C D \/
   Geo.Parallel A B C D)


/--
Every nondegenerate point-line has its own direction.
-/
theorem hilbertSameDirection_refl
    [HilbertIncidence Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    HilbertSameDirection Geo A B A B := by

  exact
    And.intro hAB
      (And.intro hAB
        (Or.inl rfl))


/--
Parallel point-lines have the same direction.
-/
theorem hilbertSameDirection_of_parallel
    [HilbertIncidence Geo]
    (A B C D : Geo.Point)
    (hPar : Geo.Parallel A B C D) :
    HilbertSameDirection Geo A B C D := by

  exact
    And.intro hPar.1
      (And.intro hPar.2.1
        (Or.inr hPar))


/--
Symmetry of affine direction.
-/
theorem hilbertSameDirection_symm
    [HilbertIncidence Geo]
    (A B C D : Geo.Point)
    (hDir : HilbertSameDirection Geo A B C D) :
    HilbertSameDirection Geo C D A B := by

  have hAB : Ne A B := hDir.1
  have hCD : Ne C D := hDir.2.1

  cases hDir.2.2 with

  | inl hEq =>
      exact
        And.intro hCD
          (And.intro hAB
            (Or.inl hEq.symm))

  | inr hPar =>
      exact
        And.intro hCD
          (And.intro hAB
            (Or.inr
              (ParallelSymmetry
                Geo A B C D hPar)))


/--
Pointwise existence of parallel projection between the two side-lines
of a noncollinear triangle.

Let XYZ be noncollinear.  If P lies on the line XY and P is not X,
then there exists Q on the line XZ such that PQ has the same affine
direction as YZ.

The relation HilbertSameDirection is essential at P = Y: then Q = Z
and the section is the base YZ itself.  For P != Y, Hilbert I.31 gives
the parallel through P; Euclidean parallel uniqueness forces that line
to meet XZ.
-/
theorem hilbert_parallel_projection_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z P : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hPXY : Collinear Geo X Y P)
    (hPX : Ne P X) :
    Exists fun Q : Geo.Point =>
      Collinear Geo X Z Q /\
      HilbertSameDirection Geo P Q Y Z := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy of the triangle.
  --------------------------------------------------------------------

  have hXY : Ne X Y :=
    hilbert_noncollinear_ne_first
      Geo X Y Z hXYZ

  have hXZ : Ne X Z := by
    intro hEq
    subst Z

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.1)))

  have hYZ : Ne Y Z := by
    intro hEq
    subst Z

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.2)))

  --------------------------------------------------------------------
  -- Fix the three side carriers.
  --------------------------------------------------------------------

  let lineXY : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hLineXY :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hXxy :
      HilbertIncidence.OnLine X lineXY :=
    hLineXY.1

  have hYxy :
      HilbertIncidence.OnLine Y lineXY :=
    hLineXY.2

  let lineXZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hLineXZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hXxz :
      HilbertIncidence.OnLine X lineXZ :=
    hLineXZ.1

  have hZxz :
      HilbertIncidence.OnLine Z lineXZ :=
    hLineXZ.2

  let lineYZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hLineYZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hYyz :
      HilbertIncidence.OnLine Y lineYZ :=
    hLineYZ.1

  have hZyz :
      HilbertIncidence.OnLine Z lineYZ :=
    hLineYZ.2

  --------------------------------------------------------------------
  -- Put P on the canonical carrier XY.
  --------------------------------------------------------------------

  let pLine : Geo.Line :=
    Classical.choose hPXY

  have hpLine :=
    Classical.choose_spec hPXY

  have hPlineXYeq :
      pLine = lineXY :=
    HilbertPlaneIncidence.line_unique
      X Y hXY
      pLine lineXY
      hpLine.1 hpLine.2.1
      hXxy hYxy

  have hPxy :
      HilbertIncidence.OnLine P lineXY := by
    rw [hPlineXYeq.symm]
    exact hpLine.2.2

  --------------------------------------------------------------------
  -- Endpoint case: P = Y, so choose Q = Z.
  --------------------------------------------------------------------

  by_cases hPY : P = Y

  case pos =>
    subst P

    have hColXZZ :
        Collinear Geo X Z Z :=
      Exists.intro lineXZ
        (And.intro hXxz
          (And.intro hZxz hZxz))

    have hDirYZYZ :
        HilbertSameDirection Geo Y Z Y Z :=
      hilbertSameDirection_refl
        Geo Y Z hYZ

    exact
      Exists.intro Z
        (And.intro hColXZZ hDirYZYZ)

  --------------------------------------------------------------------
  -- Genuine case: P is off the base YZ.
  --------------------------------------------------------------------

  case neg =>

    have hYP : Ne Y P := by
      intro hEq
      exact hPY hEq.symm

    have hYZP :
        Not (Collinear Geo Y Z P) := by

      intro hCol

      let m : Geo.Line :=
        Classical.choose hCol

      have hm :=
        Classical.choose_spec hCol

      have hLineEq :
          lineXY = m :=
        HilbertPlaneIncidence.line_unique
          Y P hYP
          lineXY m
          hYxy hPxy
          hm.1 hm.2.2

      have hZxy :
          HilbertIncidence.OnLine Z lineXY := by
        rw [hLineEq]
        exact hm.2.1

      exact
        hXYZ
          (Exists.intro lineXY
            (And.intro hXxy
              (And.intro hYxy hZxy)))

    ------------------------------------------------------------------
    -- I.31: through P draw the line parallel to YZ.
    ------------------------------------------------------------------

    cases
        hilbert_parallel_through_point_exists
          Geo Y Z P hYZ hYZP with

    | intro Q0 hQ0Data =>

      have hPQ0 : Ne P Q0 :=
        hQ0Data.1

      have hParYZ_PQ0 :
          Geo.Parallel Y Z P Q0 :=
        hQ0Data.2

      have hParPQ0_YZ :
          Geo.Parallel P Q0 Y Z :=
        ParallelSymmetry
          Geo Y Z P Q0 hParYZ_PQ0

      let linePQ0 : Geo.Line :=
        Classical.choose
          (HilbertPlaneIncidence.line_through
            P Q0 hPQ0)

      have hLinePQ0 :=
        Classical.choose_spec
          (HilbertPlaneIncidence.line_through
            P Q0 hPQ0)

      have hPpq :
          HilbertIncidence.OnLine P linePQ0 :=
        hLinePQ0.1

      have hQ0pq :
          HilbertIncidence.OnLine Q0 linePQ0 :=
        hLinePQ0.2

      ----------------------------------------------------------------
      -- The constructed parallel must meet XZ.
      ----------------------------------------------------------------

      have hDistinctYZ_XZ :
          Ne (Geo.PointLine Y Z)
          (Geo.PointLine X Z) := by

        intro hSame

        have hX_XZ :=
          intersection_test_left_mem
            Geo X Z

        have hX_YZ := hX_XZ
        rw [hSame.symm] at hX_YZ

        have hXyz :
            HilbertIncidence.OnLine X lineYZ :=
          (hilbert_mem_pointLine_iff_onLine
            Geo Y Z X lineYZ
            hYZ hYyz hZyz).mp hX_YZ

        exact
          hXYZ
            (Exists.intro lineYZ
              (And.intro hXyz
                (And.intro hYyz hZyz)))

      have hMeet :
          HilbertLinesMeet Geo linePQ0 lineXZ := by

        by_contra hDisjoint

        have hParPQ0_XZ :
            Geo.Parallel P Q0 X Z :=
          intersection_test_parallel_of_lines_disjoint
            Geo
            P Q0 X Z
            linePQ0 lineXZ
            hPQ0 hXZ
            hPpq hQ0pq
            hXxz hZxz
            hDisjoint

        have hParXZ_PQ0 :
            Geo.Parallel X Z P Q0 :=
          ParallelSymmetry
            Geo P Q0 X Z hParPQ0_XZ

        have hParYZ_XZ :
            Geo.Parallel Y Z X Z :=
          hilbert_parallel_transitive_distinct
            Geo
            Y Z
            X Z
            P Q0
            hParYZ_PQ0
            hParXZ_PQ0
            hDistinctYZ_XZ

        exact
          (intersection_test_not_parallel_of_common_point
            Geo
            Y Z
            X Z
            Z
            (intersection_test_right_mem
              Geo Y Z)
            (intersection_test_right_mem
              Geo X Z))
            hParYZ_XZ

      ----------------------------------------------------------------
      -- Choose the intersection Q.
      ----------------------------------------------------------------

      cases hMeet with

      | intro Q hQData =>

        have hQpq :
            HilbertIncidence.OnLine Q linePQ0 :=
          hQData.1

        have hQxz :
            HilbertIncidence.OnLine Q lineXZ :=
          hQData.2

        have hPQ : Ne P Q := by

          intro hEq
          subst Q

          have hLineEq :
              lineXY = lineXZ :=
            HilbertPlaneIncidence.line_unique
              X P hPX.symm
              lineXY lineXZ
              hXxy hPxy
              hXxz hQxz

          have hZxy :
              HilbertIncidence.OnLine Z lineXY := by
            rw [hLineEq]
            exact hZxz

          exact
            hXYZ
              (Exists.intro lineXY
                (And.intro hXxy
                  (And.intro hYxy hZxy)))

        have hColPQ0 :
            Collinear Geo P Q Q0 :=
          Exists.intro linePQ0
            (And.intro hPpq
              (And.intro hQpq hQ0pq))

        have hParPQ_YZ :
            Geo.Parallel P Q Y Z :=
          collinear_parallel_trans
            Geo
            P Q Q0
            Y Z
            hPQ
            hColPQ0
            hParPQ0_YZ

        have hColXZQ :
            Collinear Geo X Z Q :=
          Exists.intro lineXZ
            (And.intro hXxz
              (And.intro hZxz hQxz))

        exact
          Exists.intro Q
            (And.intro hColXZQ
              (hilbertSameDirection_of_parallel
                Geo P Q Y Z hParPQ_YZ))



------------------------------------------------------------------------
-- Uniqueness of the pointwise parallel projection
------------------------------------------------------------------------

/--
If the first point A is off the carrier CD, then SameDirection AB CD
cannot be the equal-carrier case.  It is therefore genuine parallelism.

This helper lets later projection proofs use Hilbert's Euclidean
parallel uniqueness without repeatedly splitting the direction relation.
-/
theorem hilbertSameDirection_parallel_of_first_off_line
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hCbase : HilbertIncidence.OnLine C base)
    (hDbase : HilbertIncidence.OnLine D base)
    (hAoff : Not (HilbertIncidence.OnLine A base))
    (hDir : HilbertSameDirection Geo A B C D) :
    Geo.Parallel A B C D := by

  cases hDir.2.2 with

  | inl hEq =>

      have hAAB :=
        intersection_test_left_mem
          Geo A B

      have hACD := hAAB

      rw [hEq] at hACD

      have hAbase :
          HilbertIncidence.OnLine A base :=
        (hilbert_mem_pointLine_iff_onLine
          Geo C D A base
          hDir.2.1
          hCbase hDbase).mp hACD

      exact
        False.elim
          (hAoff hAbase)

  | inr hPar =>
      exact hPar


/--
Endpoint uniqueness for parallel projection.

In a noncollinear triangle XYZ, if Q lies on XZ and YQ has the same
direction as YZ, then Q is Z.

The equal-carrier case says directly that Q lies on YZ, so the two
distinct points Q,Z would determine both XZ and YZ if Q != Z.
The genuine-parallel case is impossible because YQ and YZ share Y.
-/
theorem hilbert_parallel_projection_endpoint_unique
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (X Y Z Q : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hQXZ : Collinear Geo X Z Q)
    (hDir : HilbertSameDirection Geo Y Q Y Z) :
    Q = Z := by

  have hYZ : Ne Y Z :=
    hDir.2.1

  have hXZ : Ne X Z := by
    intro hEq
    subst Z

    have hXY : Ne X Y :=
      Ne.symm hYZ

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.1)))

  let lineXZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hLineXZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hXxz :
      HilbertIncidence.OnLine X lineXZ :=
    hLineXZ.1

  have hZxz :
      HilbertIncidence.OnLine Z lineXZ :=
    hLineXZ.2

  have hQxz :
      HilbertIncidence.OnLine Q lineXZ :=
    hilbert_collinear_on_line
      Geo X Z Q lineXZ
      hXZ hXxz hZxz hQXZ

  let lineYZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hLineYZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hYyz :
      HilbertIncidence.OnLine Y lineYZ :=
    hLineYZ.1

  have hZyz :
      HilbertIncidence.OnLine Z lineYZ :=
    hLineYZ.2

  cases hDir.2.2 with

  | inl hCarrier =>

      have hQYQ :=
        intersection_test_right_mem
          Geo Y Q

      have hQYZ := hQYQ
      rw [hCarrier] at hQYZ

      have hQyz :
          HilbertIncidence.OnLine Q lineYZ :=
        (hilbert_mem_pointLine_iff_onLine
          Geo Y Z Q lineYZ
          hYZ hYyz hZyz).mp hQYZ

      by_contra hQZ

      have hLinesEq :
          lineXZ = lineYZ :=
        HilbertPlaneIncidence.line_unique
          Q Z hQZ
          lineXZ lineYZ
          hQxz hZxz
          hQyz hZyz

      have hXyz :
          HilbertIncidence.OnLine X lineYZ := by
        rw [hLinesEq.symm]
        exact hXxz

      exact
        hXYZ
          (Exists.intro lineYZ
            (And.intro hXyz
              (And.intro hYyz hZyz)))

  | inr hPar =>

      exact
        False.elim
          ((intersection_test_not_parallel_of_common_point
            Geo
            Y Q
            Y Z
            Y
            (intersection_test_left_mem
              Geo Y Q)
            (intersection_test_left_mem
              Geo Y Z))
            hPar)


/--
The pointwise parallel projection between the two side-lines of a
noncollinear triangle is unique.

If Q1,Q2 both lie on XZ and both sections PQ1,PQ2 have the direction
of YZ, then Q1=Q2.

The proof separates the endpoint case P=Y.  Otherwise P is off YZ,
so both direction statements are genuine parallels.  Euclidean
parallel uniqueness makes the two section carriers equal, and then
incidence uniqueness makes their common intersection with XZ equal.
-/
theorem hilbert_parallel_projection_unique
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z P Q1 Q2 : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hPXY : Collinear Geo X Y P)
    (hPX : Ne P X)
    (hQ1XZ : Collinear Geo X Z Q1)
    (hQ2XZ : Collinear Geo X Z Q2)
    (hDir1 : HilbertSameDirection Geo P Q1 Y Z)
    (hDir2 : HilbertSameDirection Geo P Q2 Y Z) :
    Q1 = Q2 := by

  have hXY : Ne X Y :=
    hilbert_noncollinear_ne_first
      Geo X Y Z hXYZ

  have hXZ : Ne X Z := by
    intro hEq
    subst Z

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.1)))

  have hYZ : Ne Y Z := by
    intro hEq
    subst Z

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.2)))

  --------------------------------------------------------------------
  -- Endpoint case.
  --------------------------------------------------------------------

  by_cases hPY : P = Y

  case pos =>

    subst P

    have hQ1Z :
        Q1 = Z :=
      hilbert_parallel_projection_endpoint_unique
        Geo X Y Z Q1
        hXYZ hQ1XZ hDir1

    have hQ2Z :
        Q2 = Z :=
      hilbert_parallel_projection_endpoint_unique
        Geo X Y Z Q2
        hXYZ hQ2XZ hDir2

    exact hQ1Z.trans hQ2Z.symm

  --------------------------------------------------------------------
  -- Genuine interior/exterior point P != Y.
  --------------------------------------------------------------------

  case neg =>

    have hYP : Ne Y P := by
      intro hEq
      exact hPY hEq.symm

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hXxy :
        HilbertIncidence.OnLine X lineXY :=
      hLineXY.1

    have hYxy :
        HilbertIncidence.OnLine Y lineXY :=
      hLineXY.2

    have hPxy :
        HilbertIncidence.OnLine P lineXY :=
      hilbert_collinear_on_line
        Geo X Y P lineXY
        hXY hXxy hYxy hPXY

    let lineYZ : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          Y Z hYZ)

    have hLineYZ :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          Y Z hYZ)

    have hYyz :
        HilbertIncidence.OnLine Y lineYZ :=
      hLineYZ.1

    have hZyz :
        HilbertIncidence.OnLine Z lineYZ :=
      hLineYZ.2

    have hPoffYZ :
        Not (HilbertIncidence.OnLine P lineYZ) := by

      intro hPyz

      have hLinesEq :
          lineXY = lineYZ :=
        HilbertPlaneIncidence.line_unique
          Y P hYP
          lineXY lineYZ
          hYxy hPxy
          hYyz hPyz

      have hXyz :
          HilbertIncidence.OnLine X lineYZ := by
        rw [hLinesEq.symm]
        exact hXxy

      exact
        hXYZ
          (Exists.intro lineYZ
            (And.intro hXyz
              (And.intro hYyz hZyz)))

    have hPar1 :
        Geo.Parallel P Q1 Y Z :=
      hilbertSameDirection_parallel_of_first_off_line
        Geo P Q1 Y Z
        lineYZ
        hYyz hZyz
        hPoffYZ hDir1

    have hPar2 :
        Geo.Parallel P Q2 Y Z :=
      hilbertSameDirection_parallel_of_first_off_line
        Geo P Q2 Y Z
        lineYZ
        hYyz hZyz
        hPoffYZ hDir2

    ------------------------------------------------------------------
    -- Canonical carriers PQ1 and PQ2.
    ------------------------------------------------------------------

    let linePQ1 : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          P Q1 hPar1.1)

    have hLinePQ1 :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          P Q1 hPar1.1)

    have hPpq1 :
        HilbertIncidence.OnLine P linePQ1 :=
      hLinePQ1.1

    have hQ1pq1 :
        HilbertIncidence.OnLine Q1 linePQ1 :=
      hLinePQ1.2

    let linePQ2 : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          P Q2 hPar2.1)

    have hLinePQ2 :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          P Q2 hPar2.1)

    have hPpq2 :
        HilbertIncidence.OnLine P linePQ2 :=
      hLinePQ2.1

    have hQ2pq2 :
        HilbertIncidence.OnLine Q2 linePQ2 :=
      hLinePQ2.2

    have hDis1 :
        HilbertLinesDisjoint Geo linePQ1 lineYZ := by

      intro hMeet
      cases hMeet with
      | intro T hData =>

          have hTpq :
              Geo.PointLine P Q1 T :=
            (hilbert_mem_pointLine_iff_onLine
              Geo P Q1 T linePQ1
              hPar1.1
              hPpq1 hQ1pq1).mpr hData.1

          have hTyz :
              Geo.PointLine Y Z T :=
            (hilbert_mem_pointLine_iff_onLine
              Geo Y Z T lineYZ
              hYZ
              hYyz hZyz).mpr hData.2

          exact
            Set.disjoint_left.mp
              hPar1.2.2
              hTpq hTyz

    have hDis2 :
        HilbertLinesDisjoint Geo linePQ2 lineYZ := by

      intro hMeet
      cases hMeet with
      | intro T hData =>

          have hTpq :
              Geo.PointLine P Q2 T :=
            (hilbert_mem_pointLine_iff_onLine
              Geo P Q2 T linePQ2
              hPar2.1
              hPpq2 hQ2pq2).mpr hData.1

          have hTyz :
              Geo.PointLine Y Z T :=
            (hilbert_mem_pointLine_iff_onLine
              Geo Y Z T lineYZ
              hYZ
              hYyz hZyz).mpr hData.2

          exact
            Set.disjoint_left.mp
              hPar2.2.2
              hTpq hTyz

    have hProjectionCarrier :
        linePQ1 = linePQ2 :=
      HilbertEuclideanPlane.parallel_unique
        (Geo := Geo)
        lineYZ P hPoffYZ
        linePQ1 linePQ2
        hPpq1 hDis1
        hPpq2 hDis2

    ------------------------------------------------------------------
    -- Q1 and Q2 are intersections of that carrier with XZ.
    ------------------------------------------------------------------

    let lineXZ : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Z hXZ)

    have hLineXZ :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Z hXZ)

    have hXxz :
        HilbertIncidence.OnLine X lineXZ :=
      hLineXZ.1

    have hZxz :
        HilbertIncidence.OnLine Z lineXZ :=
      hLineXZ.2

    have hQ1xz :
        HilbertIncidence.OnLine Q1 lineXZ :=
      hilbert_collinear_on_line
        Geo X Z Q1 lineXZ
        hXZ hXxz hZxz hQ1XZ

    have hQ2xz :
        HilbertIncidence.OnLine Q2 lineXZ :=
      hilbert_collinear_on_line
        Geo X Z Q2 lineXZ
        hXZ hXxz hZxz hQ2XZ

    have hQ2pq1 :
        HilbertIncidence.OnLine Q2 linePQ1 := by
      rw [hProjectionCarrier]
      exact hQ2pq2

    by_contra hQ1Q2

    have hLinesEq :
        lineXZ = linePQ1 :=
      HilbertPlaneIncidence.line_unique
        Q1 Q2 hQ1Q2
        lineXZ linePQ1
        hQ1xz hQ2xz
        hQ1pq1 hQ2pq1

    have hZpq1 :
        HilbertIncidence.OnLine Z linePQ1 := by
      rw [hLinesEq.symm]
      exact hZxz

    have hZPQ1 :
        Geo.PointLine P Q1 Z :=
      (hilbert_mem_pointLine_iff_onLine
        Geo P Q1 Z linePQ1
        hPar1.1
        hPpq1 hQ1pq1).mpr hZpq1

    have hZYZ :=
      intersection_test_right_mem
        Geo Y Z

    exact
      Set.disjoint_left.mp
        hPar1.2.2
        hZPQ1 hZYZ



------------------------------------------------------------------------
-- Transitivity of affine direction
------------------------------------------------------------------------

/--
Affine direction is transitive in a Euclidean Hilbert plane.

The only nontrivial case is when AB and EF are both genuinely
parallel to CD.  If their carriers coincide we are in the equal-line
branch of HilbertSameDirection.  Otherwise Hilbert IV gives
parallel transitivity through the common reference line CD.
-/
theorem hilbertSameDirection_trans
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (h1 : HilbertSameDirection Geo A B C D)
    (h2 : HilbertSameDirection Geo C D E F) :
    HilbertSameDirection Geo A B E F := by

  have hAB : Ne A B :=
    h1.1

  have hCD : Ne C D :=
    h1.2.1

  have hEF : Ne E F :=
    h2.2.1

  cases h1.2.2 with

  | inl hEq1 =>

      cases h2.2.2 with

      | inl hEq2 =>

          exact
            And.intro hAB
              (And.intro hEF
                (Or.inl
                  (hEq1.trans hEq2)))

      | inr hPar2 =>

          have hPar :
              Geo.Parallel A B E F := by
            refine
              And.intro hAB
                (And.intro hEF ?_)
            rw [hEq1]
            exact hPar2.2.2

          exact
            And.intro hAB
              (And.intro hEF
                (Or.inr hPar))

  | inr hPar1 =>

      cases h2.2.2 with

      | inl hEq2 =>

          have hPar :
              Geo.Parallel A B E F := by
            refine
              And.intro hAB
                (And.intro hEF ?_)
            rw [hEq2.symm]
            exact hPar1.2.2

          exact
            And.intro hAB
              (And.intro hEF
                (Or.inr hPar))

      | inr hPar2 =>

          by_cases hEq :
              Geo.PointLine A B =
                Geo.PointLine E F

          case pos =>

            exact
              And.intro hAB
                (And.intro hEF
                  (Or.inl hEq))

          case neg =>

            have hParEF_CD :
                Geo.Parallel E F C D :=
              ParallelSymmetry
                Geo C D E F hPar2

            have hParAE :
                Geo.Parallel A B E F :=
              hilbert_parallel_transitive_distinct
                Geo
                A B
                E F
                C D
                hPar1
                hParEF_CD
                hEq

            exact
              And.intro hAB
                (And.intro hEF
                  (Or.inr hParAE))



------------------------------------------------------------------------
-- Order preservation by parallel projection
------------------------------------------------------------------------

/--
Replace the first carrier in a SameDirection statement by an equal
nondegenerate point-line.
-/
theorem hilbertSameDirection_replace_left_carrier
    [HilbertIncidence Geo]
    (A B C D E F : Geo.Point)
    (hEF : Ne E F)
    (hCarrier :
      Geo.PointLine E F =
        Geo.PointLine A B)
    (hDir : HilbertSameDirection Geo A B C D) :
    HilbertSameDirection Geo E F C D := by

  have hCD : Ne C D :=
    hDir.2.1

  cases hDir.2.2 with

  | inl hEq =>

      exact
        And.intro hEF
          (And.intro hCD
            (Or.inl
              (hCarrier.trans hEq)))

  | inr hPar =>

      have hParNew :
          Geo.Parallel E F C D := by
        refine
          And.intro hEF
            (And.intro hCD ?_)
        rw [hCarrier]
        exact hPar.2.2

      exact
        And.intro hEF
          (And.intro hCD
            (Or.inr hParNew))


/--
The two adjacent side-lines XY and YZ of a noncollinear triangle
cannot have the same affine direction.
-/
theorem hilbertSameDirection_adjacent_sides_false
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hDir : HilbertSameDirection Geo X Y Y Z) :
    False := by

  have hYZ : Ne Y Z :=
    hDir.2.1

  let lineYZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hLineYZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hYyz :
      HilbertIncidence.OnLine Y lineYZ :=
    hLineYZ.1

  have hZyz :
      HilbertIncidence.OnLine Z lineYZ :=
    hLineYZ.2

  cases hDir.2.2 with

  | inl hEq =>

      have hX_XY :=
        intersection_test_left_mem
          Geo X Y

      have hX_YZ := hX_XY
      rw [hEq] at hX_YZ

      have hXyz :
          HilbertIncidence.OnLine X lineYZ :=
        (hilbert_mem_pointLine_iff_onLine
          Geo Y Z X lineYZ
          hYZ hYyz hZyz).mp hX_YZ

      exact
        hXYZ
          (Exists.intro lineYZ
            (And.intro hXyz
              (And.intro hYyz hZyz)))

  | inr hPar =>

      exact
        (intersection_test_not_parallel_of_common_point
          Geo
          X Y
          Y Z
          Y
          (intersection_test_right_mem
            Geo X Y)
          (intersection_test_left_mem
            Geo Y Z))
          hPar


/--
A projection section meets the source side-line only at its source
point.

If P lies on XY, PQ has the direction of YZ, and R lies both on XY
and on PQ, then R=P.

Otherwise the source carrier XY and the section carrier PQ would
coincide.  Transporting the direction statement to XY would say that
the adjacent sides XY and YZ of the noncollinear triangle have the
same direction, which is impossible.
-/
theorem hilbert_parallel_projection_source_intersection_unique
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z P Q R : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hPXY : Collinear Geo X Y P)
    (hDir : HilbertSameDirection Geo P Q Y Z)
    (hRXY : Collinear Geo X Y R)
    (hRPQ : Collinear Geo P Q R) :
    R = P := by

  have hXY : Ne X Y :=
    hilbert_noncollinear_ne_first
      Geo X Y Z hXYZ

  have hPQ : Ne P Q :=
    hDir.1

  by_contra hRP

  have hPR : Ne P R :=
    Ne.symm hRP

  let lineXY : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hLineXY :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hXxy :
      HilbertIncidence.OnLine X lineXY :=
    hLineXY.1

  have hYxy :
      HilbertIncidence.OnLine Y lineXY :=
    hLineXY.2

  have hPxy :
      HilbertIncidence.OnLine P lineXY :=
    hilbert_collinear_on_line
      Geo X Y P lineXY
      hXY hXxy hYxy hPXY

  have hRxy :
      HilbertIncidence.OnLine R lineXY :=
    hilbert_collinear_on_line
      Geo X Y R lineXY
      hXY hXxy hYxy hRXY

  let linePQ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        P Q hPQ)

  have hLinePQ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        P Q hPQ)

  have hPpq :
      HilbertIncidence.OnLine P linePQ :=
    hLinePQ.1

  have hQpq :
      HilbertIncidence.OnLine Q linePQ :=
    hLinePQ.2

  have hRpq :
      HilbertIncidence.OnLine R linePQ :=
    hilbert_collinear_on_line
      Geo P Q R linePQ
      hPQ hPpq hQpq hRPQ

  have hLinesEq :
      lineXY = linePQ :=
    HilbertPlaneIncidence.line_unique
      P R hPR
      lineXY linePQ
      hPxy hRxy
      hPpq hRpq

  have hQxy :
      HilbertIncidence.OnLine Q lineXY := by
    rw [hLinesEq]
    exact hQpq

  have hCarrier :
      Geo.PointLine X Y =
        Geo.PointLine P Q :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      X Y
      P Q
      lineXY
      hXY hPQ
      hXxy hYxy
      hPxy hQxy

  have hDirXY :
      HilbertSameDirection Geo X Y Y Z :=
    hilbertSameDirection_replace_left_carrier
      Geo
      P Q
      Y Z
      X Y
      hXY
      hCarrier
      hDir

  exact
    hilbertSameDirection_adjacent_sides_false
      Geo X Y Z hXYZ hDirXY


/--
Normalize the same-side conclusion of parallel_endpoints_sameSide
onto a prescribed carrier of the second parallel line.
-/
theorem hilbert_parallel_endpoints_sameSide_on_carrier
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hCbase : HilbertIncidence.OnLine C base)
    (hDbase : HilbertIncidence.OnLine D base)
    (hPar : Geo.Parallel A B C D) :
    HilbertSameSide Geo A B base := by

  cases
      parallel_endpoints_sameSide
        Geo A B C D hPar with

  | intro l hData =>

      have hCl :
          HilbertIncidence.OnLine C l :=
        hData.1

      have hDl :
          HilbertIncidence.OnLine D l :=
        hData.2.1

      have hSame :
          HilbertSameSide Geo A B l :=
        hData.2.2

      have hlbase :
          l = base :=
        HilbertPlaneIncidence.line_unique
          C D hPar.2.1
          l base
          hCl hDl
          hCbase hDbase

      rw [hlbase] at hSame
      exact hSame


/--
Parallel projection between the two side-lines of a noncollinear
triangle preserves strict betweenness.

If A-B-C on XY and A1,B1,C1 are their parallel projections to XZ,
then A1-B1-C1.

This is a pure order/parallel result.  No segment congruence,
Archimedean axiom, or Eudoxus proportion is used.
-/
theorem hilbert_parallel_projection_between
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z A B C A1 B1 C1 : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hABC : Geo.Between A B C)
    (hAXY : Collinear Geo X Y A)
    (hBXY : Collinear Geo X Y B)
    (hCXY : Collinear Geo X Y C)
    (hA1XZ : Collinear Geo X Z A1)
    (hB1XZ : Collinear Geo X Z B1)
    (hC1XZ : Collinear Geo X Z C1)
    (hDirA : HilbertSameDirection Geo A A1 Y Z)
    (hDirB : HilbertSameDirection Geo B B1 Y Z)
    (hDirC : HilbertSameDirection Geo C C1 Y Z) :
    Geo.Between A1 B1 C1 := by

  have hABCData :=
    HilbertOrder.between_incidence
      A B C hABC

  have hAB : Ne A B :=
    hABCData.1

  have hBC : Ne B C :=
    hABCData.2.1

  have hBB1 : Ne B B1 :=
    hDirB.1

  --------------------------------------------------------------------
  -- The projection carrier BB1.
  --------------------------------------------------------------------

  let base : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        B B1 hBB1)

  have hBase :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        B B1 hBB1)

  have hBbase :
      HilbertIncidence.OnLine B base :=
    hBase.1

  have hB1base :
      HilbertIncidence.OnLine B1 base :=
    hBase.2

  --------------------------------------------------------------------
  -- A and C are off BB1, since BB1 meets the source carrier XY
  -- only at B.
  --------------------------------------------------------------------

  have hAoff :
      Not (HilbertIncidence.OnLine A base) := by

    intro hAbase

    have hBB1A :
        Collinear Geo B B1 A :=
      Exists.intro base
        (And.intro hBbase
          (And.intro hB1base hAbase))

    have hABeq :
        A = B :=
      hilbert_parallel_projection_source_intersection_unique
        Geo
        X Y Z
        B B1 A
        hXYZ
        hBXY
        hDirB
        hAXY
        hBB1A

    exact hAB hABeq

  have hCoff :
      Not (HilbertIncidence.OnLine C base) := by

    intro hCbase

    have hBB1C :
        Collinear Geo B B1 C :=
      Exists.intro base
        (And.intro hBbase
          (And.intro hB1base hCbase))

    have hCBeq :
        C = B :=
      hilbert_parallel_projection_source_intersection_unique
        Geo
        X Y Z
        B B1 C
        hXYZ
        hBXY
        hDirB
        hCXY
        hBB1C

    exact hBC hCBeq.symm

  have hOppAC :
      HilbertOppositeSide Geo A C base :=
    And.intro hAoff
      (And.intro hCoff
        (Exists.intro B
          (And.intro hABC hBbase)))

  --------------------------------------------------------------------
  -- AA1 and CC1 have the direction of BB1.
  --------------------------------------------------------------------

  have hDirYZ_BB1 :
      HilbertSameDirection Geo Y Z B B1 :=
    hilbertSameDirection_symm
      Geo B B1 Y Z hDirB

  have hDirA_BB1 :
      HilbertSameDirection Geo A A1 B B1 :=
    hilbertSameDirection_trans
      Geo
      A A1
      Y Z
      B B1
      hDirA
      hDirYZ_BB1

  have hDirC_BB1 :
      HilbertSameDirection Geo C C1 B B1 :=
    hilbertSameDirection_trans
      Geo
      C C1
      Y Z
      B B1
      hDirC
      hDirYZ_BB1

  have hParA :
      Geo.Parallel A A1 B B1 :=
    hilbertSameDirection_parallel_of_first_off_line
      Geo
      A A1
      B B1
      base
      hBbase hB1base
      hAoff hDirA_BB1

  have hParC :
      Geo.Parallel C C1 B B1 :=
    hilbertSameDirection_parallel_of_first_off_line
      Geo
      C C1
      B B1
      base
      hBbase hB1base
      hCoff hDirC_BB1

  have hSameAA1 :
      HilbertSameSide Geo A A1 base :=
    hilbert_parallel_endpoints_sameSide_on_carrier
      Geo
      A A1
      B B1
      base
      hBbase hB1base
      hParA

  have hSameCC1 :
      HilbertSameSide Geo C C1 base :=
    hilbert_parallel_endpoints_sameSide_on_carrier
      Geo
      C C1
      B B1
      base
      hBbase hB1base
      hParC

  --------------------------------------------------------------------
  -- Transport the opposite-side relation from A,C to A1,C1.
  --------------------------------------------------------------------

  have hOppA_C1 :
      HilbertOppositeSide Geo A C1 base :=
    hilbert_oppositeSide_transport_right
      Geo
      A C C1
      base
      hOppAC hSameCC1

  have hOppC1_A :
      HilbertOppositeSide Geo C1 A base :=
    hilbert_oppositeSide_symm
      Geo A C1 base hOppA_C1

  have hOppC1_A1 :
      HilbertOppositeSide Geo C1 A1 base :=
    hilbert_oppositeSide_transport_right
      Geo
      C1 A A1
      base
      hOppC1_A hSameAA1

  have hOppA1_C1 :
      HilbertOppositeSide Geo A1 C1 base :=
    hilbert_oppositeSide_symm
      Geo C1 A1 base hOppC1_A1

  --------------------------------------------------------------------
  -- A1,B1,C1 lie on the target carrier XZ.
  --------------------------------------------------------------------

  have hXZ : Ne X Z := by
    intro hEq
    subst Z

    have hXY : Ne X Y :=
      hDirB.2.1.symm

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.1)))

  let carrier : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hCarrier :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hXcarrier :
      HilbertIncidence.OnLine X carrier :=
    hCarrier.1

  have hZcarrier :
      HilbertIncidence.OnLine Z carrier :=
    hCarrier.2

  have hA1carrier :
      HilbertIncidence.OnLine A1 carrier :=
    hilbert_collinear_on_line
      Geo X Z A1 carrier
      hXZ hXcarrier hZcarrier hA1XZ

  have hB1carrier :
      HilbertIncidence.OnLine B1 carrier :=
    hilbert_collinear_on_line
      Geo X Z B1 carrier
      hXZ hXcarrier hZcarrier hB1XZ

  have hC1carrier :
      HilbertIncidence.OnLine C1 carrier :=
    hilbert_collinear_on_line
      Geo X Z C1 carrier
      hXZ hXcarrier hZcarrier hC1XZ

  exact
    hilbert_between_of_collinear_oppositeSide_VI
      Geo
      B1 A1 C1
      base carrier
      hB1base
      hB1carrier
      hA1carrier
      hC1carrier
      hOppA1_C1



------------------------------------------------------------------------
-- Midpoint transport through a family of parallel sections
------------------------------------------------------------------------

/--
A same-direction relation between two lines through the same point
forces equality of their carriers.

The genuine-parallel branch is impossible because the two carriers
share the common point O.
-/
theorem hilbertSameDirection_common_origin_carrier
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A B : Geo.Point)
    (hDir : HilbertSameDirection Geo O A O B) :
    Geo.PointLine O A =
      Geo.PointLine O B := by

  cases hDir.2.2 with

  | inl hEq =>
      exact hEq

  | inr hPar =>

      exact
        False.elim
          ((intersection_test_not_parallel_of_common_point
            Geo
            O A
            O B
            O
            (intersection_test_left_mem
              Geo O A)
            (intersection_test_left_mem
              Geo O B))
            hPar)


/--
Midpoint line in a trapezoid, stated with the reflexive affine
direction relation used by the parallel-projection layer.

Assume:
- B is the midpoint of AC,
- B2 is the midpoint of A1C1,
- M is the midpoint of the diagonal AC1,
- the two side sections AA1 and CC1 have the same direction YZ.

Then BB2 has that same direction.

The two noncollinearity hypotheses are precisely those needed by the
two applications of MidsegmentParallel.  In the projection-specific
corollary they will be derived from the source/target configuration.
-/
theorem hilbert_trapezoid_midpoints_sameDirection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (Y Z A B C A1 B2 C1 M : Geo.Point)
    (hB : HilbertIsMidpoint Geo B A C)
    (hB2 : HilbertIsMidpoint Geo B2 A1 C1)
    (hM : HilbertIsMidpoint Geo M A C1)
    (hACC1 : Not (Collinear Geo A C C1))
    (hAA1C1 : Not (Collinear Geo A A1 C1))
    (hDirA : HilbertSameDirection Geo A A1 Y Z)
    (hDirC : HilbertSameDirection Geo C C1 Y Z)
    (hBB2 : Ne B B2) :
    HilbertSameDirection Geo B B2 Y Z := by

  --------------------------------------------------------------------
  -- First triangle: A-C-C1.
  --
  -- B is the midpoint of AC and M is the midpoint of AC1.
  -- Hence BM || CC1.
  --------------------------------------------------------------------

  have hB_CA :
      HilbertIsMidpoint Geo B C A :=
    MidpointSymmetry
      Geo B A C hB

  have hM_C1A :
      HilbertIsMidpoint Geo M C1 A :=
    MidpointSymmetry
      Geo M A C1 hM

  have hTri1 :
      Not (Collinear Geo M B A) :=
    hilbert_midpoints_noncollinear
      Geo
      A C C1
      B M
      hB hM
      hACC1

  have hParBM_CC1 :
      Geo.Parallel B M C C1 :=
    MidsegmentParallel
      Geo
      C C1 A
      B M
      hB_CA
      hM_C1A
      hTri1

  --------------------------------------------------------------------
  -- Second triangle: A-A1-C1.
  --
  -- M is the midpoint of AC1 and B2 is the midpoint of A1C1.
  -- Hence MB2 || AA1.
  --------------------------------------------------------------------

  have hC1AA1 :
      Not (Collinear Geo C1 A A1) := by
    intro h
    exact
      hAA1C1
        (PrimCollinearCycle
          Geo C1 A A1 h)

  have hM_C1A' :
      HilbertIsMidpoint Geo M C1 A :=
    MidpointSymmetry
      Geo M A C1 hM

  have hB2_C1A1 :
      HilbertIsMidpoint Geo B2 C1 A1 :=
    MidpointSymmetry
      Geo B2 A1 C1 hB2

  have hTri2 :
      Not (Collinear Geo B2 M C1) :=
    hilbert_midpoints_noncollinear
      Geo
      C1 A A1
      M B2
      hM_C1A'
      hB2_C1A1
      hC1AA1

  have hParMB2_AA1 :
      Geo.Parallel M B2 A A1 :=
    MidsegmentParallel
      Geo
      A A1 C1
      M B2
      hM hB2
      hTri2

  --------------------------------------------------------------------
  -- Both midpoint lines have the common direction YZ.
  --------------------------------------------------------------------

  have hParMB_CC1 :
      Geo.Parallel M B C C1 :=
    ParallelSwapFirstLine
      Geo B M C C1 hParBM_CC1

  have hDirMB_CC1 :
      HilbertSameDirection Geo M B C C1 :=
    hilbertSameDirection_of_parallel
      Geo M B C C1 hParMB_CC1

  have hDirMB_YZ :
      HilbertSameDirection Geo M B Y Z :=
    hilbertSameDirection_trans
      Geo
      M B
      C C1
      Y Z
      hDirMB_CC1
      hDirC

  have hDirMB2_AA1 :
      HilbertSameDirection Geo M B2 A A1 :=
    hilbertSameDirection_of_parallel
      Geo M B2 A A1 hParMB2_AA1

  have hDirMB2_YZ :
      HilbertSameDirection Geo M B2 Y Z :=
    hilbertSameDirection_trans
      Geo
      M B2
      A A1
      Y Z
      hDirMB2_AA1
      hDirA

  --------------------------------------------------------------------
  -- Therefore MB and MB2 have the same carrier.
  --------------------------------------------------------------------

  have hDirMB_MB2 :
      HilbertSameDirection Geo M B M B2 :=
    hilbertSameDirection_trans
      Geo
      M B
      Y Z
      M B2
      hDirMB_YZ
      (hilbertSameDirection_symm
        Geo M B2 Y Z hDirMB2_YZ)

  have hCarrierMB :
      Geo.PointLine M B =
        Geo.PointLine M B2 :=
    hilbertSameDirection_common_origin_carrier
      Geo M B B2 hDirMB_MB2

  --------------------------------------------------------------------
  -- Replace the determining pair MB2 by BB2 on that carrier.
  --------------------------------------------------------------------

  have hMB2 : Ne M B2 :=
    hDirMB2_YZ.1

  let carrier : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        M B2 hMB2)

  have hCarrierData :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        M B2 hMB2)

  have hMcarrier :
      HilbertIncidence.OnLine M carrier :=
    hCarrierData.1

  have hB2carrier :
      HilbertIncidence.OnLine B2 carrier :=
    hCarrierData.2

  have hB_MB :=
    intersection_test_right_mem
      Geo M B

  have hB_MB2 := hB_MB
  rw [hCarrierMB] at hB_MB2

  have hBcarrier :
      HilbertIncidence.OnLine B carrier :=
    (hilbert_mem_pointLine_iff_onLine
      Geo M B2 B carrier
      hMB2
      hMcarrier hB2carrier).mp
      hB_MB2

  have hCarrierBB2 :
      Geo.PointLine B B2 =
        Geo.PointLine M B2 :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      B B2
      M B2
      carrier
      hBB2 hMB2
      hBcarrier hB2carrier
      hMcarrier hB2carrier

  exact
    hilbertSameDirection_replace_left_carrier
      Geo
      M B2
      Y Z
      B B2
      hBB2
      hCarrierBB2
      hDirMB2_YZ



------------------------------------------------------------------------
-- Equal steps are preserved by parallel projection
------------------------------------------------------------------------

/--
The two side-lines XY and XZ of a noncollinear triangle meet only at X.
-/
theorem hilbert_triangle_side_intersection_eq_vertex
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (X Y Z P : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hPXY : Collinear Geo X Y P)
    (hPXZ : Collinear Geo X Z P) :
    P = X := by

  have hXY : Ne X Y :=
    hilbert_noncollinear_ne_first
      Geo X Y Z hXYZ

  have hXZ : Ne X Z := by
    intro hEq
    subst Z

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.1)))

  by_contra hPX

  have hXP : Ne X P :=
    Ne.symm hPX

  let lineXY : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hLineXY :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hXxy :
      HilbertIncidence.OnLine X lineXY :=
    hLineXY.1

  have hYxy :
      HilbertIncidence.OnLine Y lineXY :=
    hLineXY.2

  have hPxy :
      HilbertIncidence.OnLine P lineXY :=
    hilbert_collinear_on_line
      Geo X Y P lineXY
      hXY hXxy hYxy hPXY

  let lineXZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hLineXZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hXxz :
      HilbertIncidence.OnLine X lineXZ :=
    hLineXZ.1

  have hZxz :
      HilbertIncidence.OnLine Z lineXZ :=
    hLineXZ.2

  have hPxz :
      HilbertIncidence.OnLine P lineXZ :=
    hilbert_collinear_on_line
      Geo X Z P lineXZ
      hXZ hXxz hZxz hPXZ

  have hLinesEq :
      lineXY = lineXZ :=
    HilbertPlaneIncidence.line_unique
      X P hXP
      lineXY lineXZ
      hXxy hPxy
      hXxz hPxz

  have hZxy :
      HilbertIncidence.OnLine Z lineXY := by
    rw [hLinesEq]
    exact hZxz

  exact
    hXYZ
      (Exists.intro lineXY
        (And.intro hXxy
          (And.intro hYxy hZxy)))


/--
In a noncollinear triangle, the side XZ cannot have the same affine
direction as the adjacent side YZ.
-/
theorem hilbertSameDirection_other_adjacent_sides_false
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hDir : HilbertSameDirection Geo X Z Y Z) :
    False := by

  have hYZ : Ne Y Z :=
    hDir.2.1

  let lineYZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hLineYZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        Y Z hYZ)

  have hYyz :
      HilbertIncidence.OnLine Y lineYZ :=
    hLineYZ.1

  have hZyz :
      HilbertIncidence.OnLine Z lineYZ :=
    hLineYZ.2

  cases hDir.2.2 with

  | inl hEq =>

      have hX_XZ :=
        intersection_test_left_mem
          Geo X Z

      have hX_YZ := hX_XZ
      rw [hEq] at hX_YZ

      have hXyz :
          HilbertIncidence.OnLine X lineYZ :=
        (hilbert_mem_pointLine_iff_onLine
          Geo Y Z X lineYZ
          hYZ hYyz hZyz).mp hX_YZ

      exact
        hXYZ
          (Exists.intro lineYZ
            (And.intro hXyz
              (And.intro hYyz hZyz)))

  | inr hPar =>

      exact
        (intersection_test_not_parallel_of_common_point
          Geo
          X Z
          Y Z
          Z
          (intersection_test_right_mem
            Geo X Z)
          (intersection_test_right_mem
            Geo Y Z))
          hPar


/--
A source point of a valid parallel projection is never the vertex X.
-/
theorem hilbert_parallel_projection_source_ne_vertex
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z P Q : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hPXY : Collinear Geo X Y P)
    (hQXZ : Collinear Geo X Z Q)
    (hDir : HilbertSameDirection Geo P Q Y Z) :
    Ne P X := by

  intro hPX
  subst P

  have hXZ : Ne X Z := by
    intro hEq
    subst Z

    have hXY : Ne X Y :=
      hDir.2.1.symm

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    exact
      hXYZ
        (Exists.intro lineXY
          (And.intro hLineXY.1
            (And.intro hLineXY.2
              hLineXY.1)))

  let lineXZ : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hLineXZ :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Z hXZ)

  have hXxz :
      HilbertIncidence.OnLine X lineXZ :=
    hLineXZ.1

  have hZxz :
      HilbertIncidence.OnLine Z lineXZ :=
    hLineXZ.2

  have hQxz :
      HilbertIncidence.OnLine Q lineXZ :=
    hilbert_collinear_on_line
      Geo X Z Q lineXZ
      hXZ hXxz hZxz hQXZ

  have hCarrier :
      Geo.PointLine X Z =
        Geo.PointLine X Q :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      X Z
      X Q
      lineXZ
      hXZ hDir.1
      hXxz hZxz
      hXxz hQxz

  have hDirXZ :
      HilbertSameDirection Geo X Z Y Z :=
    hilbertSameDirection_replace_left_carrier
      Geo
      X Q
      Y Z
      X Z
      hXZ
      hCarrier
      hDir

  exact
    hilbertSameDirection_other_adjacent_sides_false
      Geo X Y Z hXYZ hDirXZ


/--
A target point of a valid parallel projection is never the vertex X.
-/
theorem hilbert_parallel_projection_target_ne_vertex
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z P Q : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hPXY : Collinear Geo X Y P)
    (hQXZ : Collinear Geo X Z Q)
    (hDir : HilbertSameDirection Geo P Q Y Z) :
    Ne Q X := by

  intro hQX
  subst Q

  have hXY : Ne X Y :=
    hilbert_noncollinear_ne_first
      Geo X Y Z hXYZ

  let lineXY : Geo.Line :=
    Classical.choose
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hLineXY :=
    Classical.choose_spec
      (HilbertPlaneIncidence.line_through
        X Y hXY)

  have hXxy :
      HilbertIncidence.OnLine X lineXY :=
    hLineXY.1

  have hYxy :
      HilbertIncidence.OnLine Y lineXY :=
    hLineXY.2

  have hPxy :
      HilbertIncidence.OnLine P lineXY :=
    hilbert_collinear_on_line
      Geo X Y P lineXY
      hXY hXxy hYxy hPXY

  have hCarrier :
      Geo.PointLine X Y =
        Geo.PointLine P X :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      X Y
      P X
      lineXY
      hXY hDir.1
      hXxy hYxy
      hPxy hXxy

  have hDirXY :
      HilbertSameDirection Geo X Y Y Z :=
    hilbertSameDirection_replace_left_carrier
      Geo
      P X
      Y Z
      X Y
      hXY
      hCarrier
      hDir

  exact
    hilbertSameDirection_adjacent_sides_false
      Geo X Y Z hXYZ hDirXY


/--
Parallel projection preserves equality of two adjacent source
segments.

If A-B-C on the source side, AB is congruent to BC, and A1,B1,C1 are
their parallel projections to the target side, then A1B1 is congruent
to B1C1.

This is the first genuinely metric statement in the direct proof of
forward VI.2.
-/
theorem hilbert_parallel_projection_equal_step
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z A B C A1 B1 C1 : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (hABC : Geo.Between A B C)
    (hABBC : Geo.Congruent A B B C)
    (hAXY : Collinear Geo X Y A)
    (hBXY : Collinear Geo X Y B)
    (hCXY : Collinear Geo X Y C)
    (hA1XZ : Collinear Geo X Z A1)
    (hB1XZ : Collinear Geo X Z B1)
    (hC1XZ : Collinear Geo X Z C1)
    (hDirA : HilbertSameDirection Geo A A1 Y Z)
    (hDirB : HilbertSameDirection Geo B B1 Y Z)
    (hDirC : HilbertSameDirection Geo C C1 Y Z) :
    Geo.Congruent A1 B1 B1 C1 := by

  --------------------------------------------------------------------
  -- Source and target order.
  --------------------------------------------------------------------

  have hBmid :
      HilbertIsMidpoint Geo B A C :=
    And.intro hABC hABBC

  have hTargetBetween :
      Geo.Between A1 B1 C1 :=
    hilbert_parallel_projection_between
      Geo
      X Y Z
      A B C
      A1 B1 C1
      hXYZ
      hABC
      hAXY hBXY hCXY
      hA1XZ hB1XZ hC1XZ
      hDirA hDirB hDirC

  have hTargetData :=
    HilbertOrder.between_incidence
      A1 B1 C1 hTargetBetween

  have hA1C1 : Ne A1 C1 :=
    hTargetData.2.2.1

  --------------------------------------------------------------------
  -- Construct the midpoint B2 of A1C1.
  --------------------------------------------------------------------

  cases
      euclid_proposition_10
        Geo A1 C1 hA1C1 with

  | intro B2 hB2mid =>

    have hB2col_raw :
        Collinear Geo A1 B2 C1 :=
      (HilbertOrder.between_incidence
        A1 B2 C1 hB2mid.1).2.2.2.1

    have hB2col :
        Collinear Geo A1 C1 B2 :=
      PrimCollinearRotate
        Geo A1 B2 C1 hB2col_raw

    have hXZ : Ne X Z := by
      intro hEq
      subst Z

      have hXY : Ne X Y :=
        hDirB.2.1.symm

      let lineXY : Geo.Line :=
        Classical.choose
          (HilbertPlaneIncidence.line_through
            X Y hXY)

      have hLineXY :=
        Classical.choose_spec
          (HilbertPlaneIncidence.line_through
            X Y hXY)

      exact
        hXYZ
          (Exists.intro lineXY
            (And.intro hLineXY.1
              (And.intro hLineXY.2
                hLineXY.1)))

    let lineXZ : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Z hXZ)

    have hLineXZ :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Z hXZ)

    have hXxz :
        HilbertIncidence.OnLine X lineXZ :=
      hLineXZ.1

    have hZxz :
        HilbertIncidence.OnLine Z lineXZ :=
      hLineXZ.2

    have hA1xz :
        HilbertIncidence.OnLine A1 lineXZ :=
      hilbert_collinear_on_line
        Geo X Z A1 lineXZ
        hXZ hXxz hZxz hA1XZ

    have hC1xz :
        HilbertIncidence.OnLine C1 lineXZ :=
      hilbert_collinear_on_line
        Geo X Z C1 lineXZ
        hXZ hXxz hZxz hC1XZ

    have hB2xz :
        HilbertIncidence.OnLine B2 lineXZ :=
      hilbert_collinear_on_line
        Geo A1 C1 B2 lineXZ
        hA1C1 hA1xz hC1xz hB2col

    have hB2XZ :
        Collinear Geo X Z B2 :=
      Exists.intro lineXZ
        (And.intro hXxz
          (And.intro hZxz hB2xz))

    ------------------------------------------------------------------
    -- Noncollinearity of A,C,C1.
    ------------------------------------------------------------------

    have hAC :
        Ne A C :=
      (HilbertOrder.between_incidence
        A B C hABC).2.2.1

    have hXY : Ne X Y :=
      hilbert_noncollinear_ne_first
        Geo X Y Z hXYZ

    let lineXY : Geo.Line :=
      Classical.choose
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hLineXY :=
      Classical.choose_spec
        (HilbertPlaneIncidence.line_through
          X Y hXY)

    have hXxy :
        HilbertIncidence.OnLine X lineXY :=
      hLineXY.1

    have hYxy :
        HilbertIncidence.OnLine Y lineXY :=
      hLineXY.2

    have hAxy :
        HilbertIncidence.OnLine A lineXY :=
      hilbert_collinear_on_line
        Geo X Y A lineXY
        hXY hXxy hYxy hAXY

    have hCxy :
        HilbertIncidence.OnLine C lineXY :=
      hilbert_collinear_on_line
        Geo X Y C lineXY
        hXY hXxy hYxy hCXY

    have hC1neX :
        Ne C1 X :=
      hilbert_parallel_projection_target_ne_vertex
        Geo
        X Y Z
        C C1
        hXYZ hCXY hC1XZ hDirC

    have hACC1 :
        Not (Collinear Geo A C C1) := by

      intro hCol

      have hC1xy :
          HilbertIncidence.OnLine C1 lineXY :=
        hilbert_collinear_on_line
          Geo A C C1 lineXY
          hAC hAxy hCxy hCol

      have hC1XY :
          Collinear Geo X Y C1 :=
        Exists.intro lineXY
          (And.intro hXxy
            (And.intro hYxy hC1xy))

      have hC1X :
          C1 = X :=
        hilbert_triangle_side_intersection_eq_vertex
          Geo
          X Y Z C1
          hXYZ hC1XY hC1XZ

      exact hC1neX hC1X

    ------------------------------------------------------------------
    -- Noncollinearity of A,A1,C1.
    ------------------------------------------------------------------

    have hAneX :
        Ne A X :=
      hilbert_parallel_projection_source_ne_vertex
        Geo
        X Y Z
        A A1
        hXYZ hAXY hA1XZ hDirA

    have hAA1C1 :
        Not (Collinear Geo A A1 C1) := by

      intro hCol

      have hA1C1A :
          Collinear Geo A1 C1 A :=
        PrimCollinearCycle
          Geo A A1 C1 hCol

      have hAxz :
          HilbertIncidence.OnLine A lineXZ :=
        hilbert_collinear_on_line
          Geo A1 C1 A lineXZ
          hA1C1 hA1xz hC1xz hA1C1A

      have hAXZ :
          Collinear Geo X Z A :=
        Exists.intro lineXZ
          (And.intro hXxz
            (And.intro hZxz hAxz))

      have hAX :
          A = X :=
        hilbert_triangle_side_intersection_eq_vertex
          Geo
          X Y Z A
          hXYZ hAXY hAXZ

      exact hAneX hAX

    ------------------------------------------------------------------
    -- Construct midpoint M of the diagonal AC1.
    ------------------------------------------------------------------

    have hAC1 : Ne A C1 := by

      intro hEq
      subst C1

      have hACA :
          Collinear Geo A C A :=
        Exists.intro lineXY
          (And.intro hAxy
            (And.intro hCxy hAxy))

      exact hACC1 hACA

    cases
        euclid_proposition_10
          Geo A C1 hAC1 with

    | intro M hMmid =>

      ----------------------------------------------------------------
      -- B and B2 are distinct.
      ----------------------------------------------------------------

      have hBneX :
          Ne B X :=
        hilbert_parallel_projection_source_ne_vertex
          Geo
          X Y Z
          B B1
          hXYZ hBXY hB1XZ hDirB

      have hBB2 :
          Ne B B2 := by

        intro hEq
        subst B2

        have hBX :
            B = X :=
          hilbert_triangle_side_intersection_eq_vertex
            Geo
            X Y Z B
            hXYZ hBXY hB2XZ

        exact hBneX hBX

      ----------------------------------------------------------------
      -- Trapezoid midpoint theorem: BB2 has the projection direction.
      ----------------------------------------------------------------

      have hDirB2 :
          HilbertSameDirection Geo B B2 Y Z :=
        hilbert_trapezoid_midpoints_sameDirection
          Geo
          Y Z
          A B C
          A1 B2 C1
          M
          hBmid
          hB2mid
          hMmid
          hACC1
          hAA1C1
          hDirA
          hDirC
          hBB2

      ----------------------------------------------------------------
      -- Projection uniqueness identifies B2 with the given B1.
      ----------------------------------------------------------------

      have hB1B2 :
          B1 = B2 :=
        hilbert_parallel_projection_unique
          Geo
          X Y Z
          B B1 B2
          hXYZ
          hBXY
          hBneX
          hB1XZ
          hB2XZ
          hDirB
          hDirB2

      rw [hB1B2]

      exact hB2mid.2



theorem hilbert_parallel_inner_intersection_between
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O L M P Q : Geo.Point)
    (hOLM : Not (Collinear Geo O L M))
    (hOPL : Geo.Between O P L)
    (hOQMcol : Collinear Geo O M Q)
    (hParallel : Geo.Parallel P Q L M) :
    Geo.Between O Q M := by

  have hOPLData :=
    HilbertOrder.between_incidence
      O P L hOPL

  have hOP : Ne O P :=
    hOPLData.1

  have hOLP :
      Collinear Geo O L P := by
    cases hOPLData.2.2.2.1 with
    | intro line hData =>
        exact
          Exists.intro line
            (And.intro hData.1
              (And.intro hData.2.2 hData.2.1))

  have hOML :
      Not (Collinear Geo O M L) := by
    intro h
    exact
      hOLM
        (PrimCollinearRotate
          Geo O M L h)

  have hOM : Ne O M :=
    hilbert_noncollinear_ne_first
      Geo O M L hOML

  have hDir :
      HilbertSameDirection Geo P Q L M :=
    hilbertSameDirection_of_parallel
      Geo P Q L M hParallel

  have hQO : Ne Q O :=
    hilbert_parallel_projection_target_ne_vertex
      Geo
      O L M
      P Q
      hOLM
      hOLP
      hOQMcol
      hDir

  have hOQ : Ne O Q :=
    hQO.symm

  have hQM : Ne Q M := by

    intro hEq
    subst Q

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        P M
        L M
        M
        (intersection_test_right_mem
          Geo P M)
        (intersection_test_right_mem
          Geo L M))
        hParallel

  have hOQM :
      Collinear Geo O Q M := by
    cases hOQMcol with
    | intro line hData =>
        exact
          Exists.intro line
            (And.intro hData.1
              (And.intro hData.2.2 hData.2.1))

  cases
      hilbert_between_trichotomy
        Geo
        O Q M
        hOQ
        hQM
        hOM
        hOQM
  with

  | inl hOQM =>
      exact hOQM

  | inr hRest =>

      cases hRest with

      | inl hQOM =>

          cases
              hilbert_parallel_second_endpoints_sameSide
                Geo P Q L M hParallel
          with
          | intro linePQ hData =>

              have hPline :
                  HilbertIncidence.OnLine P linePQ :=
                hData.1

              have hQline :
                  HilbertIncidence.OnLine Q linePQ :=
                hData.2.1

              have hLMsame :
                  HilbertSameSide Geo L M linePQ :=
                hData.2.2

              have hLoff :
                  Not (HilbertIncidence.OnLine L linePQ) :=
                hLMsame.1

              have hMoff :
                  Not (HilbertIncidence.OnLine M linePQ) :=
                hLMsame.2.1

              have hOoff :
                  Not (HilbertIncidence.OnLine O linePQ) := by

                intro hOline

                have hLline :
                    HilbertIncidence.OnLine L linePQ :=
                  hilbert_collinear_on_line
                    Geo
                    O P L
                    linePQ
                    hOP
                    hOline
                    hPline
                    hOPLData.2.2.2.1

                exact hLoff hLline

              have hOppOL :
                  HilbertOppositeSide Geo O L linePQ :=
                And.intro hOoff
                  (And.intro hLoff
                    (Exists.intro P
                      (And.intro hOPL hPline)))

              have hMOQ :
                  Geo.Between M O Q :=
                (HilbertOrder.between_incidence
                  Q O M hQOM).2.2.2.2

              have hMOside :
                  HilbertSameSide Geo M O linePQ :=
                hilbert_between_sameSide_of_endpoint_on_line
                  Geo
                  M O Q
                  linePQ
                  hMOQ
                  hQline
                  hMoff

              have hLOside :
                  HilbertSameSide Geo L O linePQ :=
                hilbert_sameSide_trans
                  Geo
                  L M O
                  linePQ
                  hLMsame
                  hMOside

              have hOLside :
                  HilbertSameSide Geo O L linePQ :=
                hilbert_sameSide_symm
                  Geo L O linePQ hLOside

              exact
                False.elim
                  ((hilbert_oppositeSide_not_sameSide
                    Geo O L linePQ hOppOL)
                    hOLside)

      | inr hOMQ =>

          cases
              parallel_endpoints_sameSide
                Geo P Q L M hParallel
          with
          | intro lineLM hData =>

              have hLline :
                  HilbertIncidence.OnLine L lineLM :=
                hData.1

              have hMline :
                  HilbertIncidence.OnLine M lineLM :=
                hData.2.1

              have hPQsame :
                  HilbertSameSide Geo P Q lineLM :=
                hData.2.2

              have hQoff :
                  Not (HilbertIncidence.OnLine Q lineLM) :=
                hPQsame.2.1

              have hOoff :
                  Not (HilbertIncidence.OnLine O lineLM) := by

                intro hOline

                exact
                  hOLM
                    (Exists.intro lineLM
                      (And.intro hOline
                        (And.intro hLline hMline)))

              have hOPsame :
                  HilbertSameSide Geo O P lineLM :=
                hilbert_between_sameSide_of_endpoint_on_line
                  Geo
                  O P L
                  lineLM
                  hOPL
                  hLline
                  hOoff

              have hOQsame :
                  HilbertSameSide Geo O Q lineLM :=
                hilbert_sameSide_trans
                  Geo
                  O P Q
                  lineLM
                  hOPsame
                  hPQsame

              have hOppOQ :
                  HilbertOppositeSide Geo O Q lineLM :=
                And.intro hOoff
                  (And.intro hQoff
                    (Exists.intro M
                      (And.intro hOMQ hMline)))

              exact
                False.elim
                  ((hilbert_oppositeSide_not_sameSide
                    Geo O Q lineLM hOppOQ)
                    hOQsame)

------------------------------------------------------------------------
-- Converse VI.2 from the forward direction
------------------------------------------------------------------------

/--
The converse direction of VI.2 follows from the forward direction.

Given proportional cuts E and F on the two sides of triangle XYZ,
construct F1 on XZ so that EF1 is parallel to YZ. The forward
direction gives

  XE : EY = XF1 : F1Z.

Together with the assumed

  XE : EY = XF : FZ,

V.11 gives

  XF : FZ = XF1 : F1Z.

Since both pairs decompose the same whole XZ, V.14 plus equality of
sums forces XF = XF1. The points F and F1 lie on the same ray XZ, so
Hilbert III.1 uniqueness gives F = F1. Hence EF is parallel to YZ.
-/
theorem hilbertVI2EudoxusConverse_of_forward
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (hForward : HilbertVI2EudoxusForward Geo) :
    HilbertVI2EudoxusConverse Geo := by

  intro X E Y F Z hXYZ hXEY hXFZ hGiven

  have hXEYData :=
    HilbertOrder.between_incidence
      X E Y hXEY

  have hXFZData :=
    HilbertOrder.between_incidence
      X F Z hXFZ

  have hXE : Ne X E :=
    hXEYData.1

  have hEY : Ne E Y :=
    hXEYData.2.1

  have hXY : Ne X Y :=
    hXEYData.2.2.1

  have hXF : Ne X F :=
    hXFZData.1

  have hFZ : Ne F Z :=
    hXFZData.2.1

  have hXZ : Ne X Z :=
    hXFZData.2.2.1

  have hYZ : Ne Y Z := by
    intro hEq
    subst Z

    rcases hXEYData.2.2.2.1 with
      ⟨line, hXline, _hEline, hYline⟩

    exact
      hXYZ
        ⟨line, hXline, hYline, hYline⟩

  have hXYE :
      Collinear Geo X Y E := by
    cases hXEYData.2.2.2.1 with
    | intro line hData =>
        exact
          Exists.intro line
            (And.intro hData.1
              (And.intro hData.2.2 hData.2.1))

  --------------------------------------------------------------------
  -- Construct the parallel section through E.
  --------------------------------------------------------------------

  cases
      hilbert_parallel_projection_exists
        Geo
        X Y Z
        E
        hXYZ
        hXYE
        hXE.symm
  with
  | intro F1 hProjection =>

      have hXF1Zcol :
          Collinear Geo X Z F1 :=
        hProjection.1

      have hDir :
          HilbertSameDirection Geo E F1 Y Z :=
        hProjection.2

      ----------------------------------------------------------------
      -- E is off the base YZ, so SameDirection is genuine parallelism.
      ----------------------------------------------------------------

      cases
          HilbertPlaneIncidence.line_through
            Y Z hYZ
      with
      | intro baseYZ hBaseYZ =>

          have hYbase :
              HilbertIncidence.OnLine Y baseYZ :=
            hBaseYZ.1

          have hZbase :
              HilbertIncidence.OnLine Z baseYZ :=
            hBaseYZ.2

          have hEoff :
              Not (HilbertIncidence.OnLine E baseYZ) := by

            intro hEbase

            have hXbase :
                HilbertIncidence.OnLine X baseYZ :=
              hilbert_collinear_on_line
                Geo
                E Y X
                baseYZ
                hEY
                hEbase
                hYbase
                (PrimCollinearSymm
                  Geo X Y E hXYE)

            exact
              hXYZ
                (Exists.intro baseYZ
                  (And.intro hXbase
                    (And.intro hYbase hZbase)))

          have hParallel :
              Geo.Parallel E F1 Y Z :=
            hilbertSameDirection_parallel_of_first_off_line
              Geo
              E F1
              Y Z
              baseYZ
              hYbase
              hZbase
              hEoff
              hDir

          ----------------------------------------------------------------
          -- The new point F1 lies strictly inside XZ.
          ----------------------------------------------------------------

          have hXF1Z :
              Geo.Between X F1 Z :=
            hilbert_parallel_inner_intersection_between
              Geo
              X Y Z
              E F1
              hXYZ
              hXEY
              hXF1Zcol
              hParallel

          have hXF1ZData :=
            HilbertOrder.between_incidence
              X F1 Z hXF1Z

          have hXF1 : Ne X F1 :=
            hXF1ZData.1

          have hF1Z : Ne F1 Z :=
            hXF1ZData.2.1

          ----------------------------------------------------------------
          -- Forward VI.2 on the constructed parallel.
          ----------------------------------------------------------------

          have hConstructed :
              HilbertEudoxusProportion
                Geo
                (hilbertPositiveSegmentClassOf
                  Geo X E hXE)
                (hilbertPositiveSegmentClassOf
                  Geo E Y hEY)
                (hilbertPositiveSegmentClassOf
                  Geo X F1 hXF1)
                (hilbertPositiveSegmentClassOf
                  Geo F1 Z hF1Z) := by

            simpa using
              hForward
                X E Y F1 Z
                hXYZ
                hXEY
                hXF1Z
                hParallel

          ----------------------------------------------------------------
          -- V.11: compare the two divisions of XZ.
          ----------------------------------------------------------------

          have hGivenSymm :
              HilbertEudoxusProportion
                Geo
                (hilbertPositiveSegmentClassOf
                  Geo X F hXF)
                (hilbertPositiveSegmentClassOf
                  Geo F Z hFZ)
                (hilbertPositiveSegmentClassOf
                  Geo X E hXE)
                (hilbertPositiveSegmentClassOf
                  Geo E Y hEY) := by

            simpa using
              hilbertEudoxusProportion_symm
                Geo
                (hilbertPositiveSegmentClassOf
                  Geo X E hXE)
                (hilbertPositiveSegmentClassOf
                  Geo E Y hEY)
                (hilbertPositiveSegmentClassOf
                  Geo X F hXF)
                (hilbertPositiveSegmentClassOf
                  Geo F Z hFZ)
                hGiven

          have hDivision :
              HilbertEudoxusProportion
                Geo
                (hilbertPositiveSegmentClassOf
                  Geo X F hXF)
                (hilbertPositiveSegmentClassOf
                  Geo F Z hFZ)
                (hilbertPositiveSegmentClassOf
                  Geo X F1 hXF1)
                (hilbertPositiveSegmentClassOf
                  Geo F1 Z hF1Z) :=
            hilbertEudoxusProportion_trans
              Geo
              (hilbertPositiveSegmentClassOf
                Geo X F hXF)
              (hilbertPositiveSegmentClassOf
                Geo F Z hFZ)
              (hilbertPositiveSegmentClassOf
                Geo X E hXE)
              (hilbertPositiveSegmentClassOf
                Geo E Y hEY)
              (hilbertPositiveSegmentClassOf
                Geo X F1 hXF1)
              (hilbertPositiveSegmentClassOf
                Geo F1 Z hF1Z)
              hGivenSymm
              hConstructed

          ----------------------------------------------------------------
          -- Both divisions have the same whole XZ.
          ----------------------------------------------------------------

          have hSumF :
              hilbertPositiveSegmentClassOf Geo X F hXF +
                  hilbertPositiveSegmentClassOf Geo F Z hFZ =
                hilbertPositiveSegmentClassOf Geo X Z hXZ := by

            simpa using
              hilbertPositiveSegmentClassOf_add_of_between
                Geo X F Z hXFZ

          have hSumF1 :
              hilbertPositiveSegmentClassOf Geo X F1 hXF1 +
                  hilbertPositiveSegmentClassOf Geo F1 Z hF1Z =
                hilbertPositiveSegmentClassOf Geo X Z hXZ := by

            simpa using
              hilbertPositiveSegmentClassOf_add_of_between
                Geo X F1 Z hXF1Z

          have hSameSum :
              hilbertPositiveSegmentClassOf Geo X F hXF +
                  hilbertPositiveSegmentClassOf Geo F Z hFZ =
                hilbertPositiveSegmentClassOf Geo X F1 hXF1 +
                  hilbertPositiveSegmentClassOf Geo F1 Z hF1Z :=
            Eq.trans hSumF hSumF1.symm

          ----------------------------------------------------------------
          -- V.14 plus equality of sums identifies the first parts.
          ----------------------------------------------------------------

          have hParts :=
            hilbertEudoxusProportion_eq_of_equal_sums
              Geo
              (hilbertPositiveSegmentClassOf
                Geo X F hXF)
              (hilbertPositiveSegmentClassOf
                Geo F Z hFZ)
              (hilbertPositiveSegmentClassOf
                Geo X F1 hXF1)
              (hilbertPositiveSegmentClassOf
                Geo F1 Z hF1Z)
              hDivision
              hSameSum

          have hFirst :
              hilbertPositiveSegmentClassOf Geo X F hXF =
                hilbertPositiveSegmentClassOf Geo X F1 hXF1 :=
            hParts.1

          ----------------------------------------------------------------
          -- F and F1 are on the same ray XZ, hence they coincide.
          ----------------------------------------------------------------

          have hRayXFZ :
              HilbertSameRay Geo X F Z :=
            hilbert_sameRay_of_between
              Geo X F Z hXFZ

          have hRayXZF :
              HilbertSameRay Geo X Z F :=
            hilbert_sameRay_symm
              Geo X F Z hRayXFZ

          have hRayXF1Z :
              HilbertSameRay Geo X F1 Z :=
            hilbert_sameRay_of_between
              Geo X F1 Z hXF1Z

          have hRayXZF1 :
              HilbertSameRay Geo X Z F1 :=
            hilbert_sameRay_symm
              Geo X F1 Z hRayXF1Z

          have hFF1 :
              F = F1 :=
            hilbert_sameRay_eq_of_positiveClass_eq
              Geo
              X Z
              F F1
              hRayXZF
              hRayXZF1
              (by
                simpa using hFirst)

          subst F1

          exact hParallel


end Geometry

import CGJteamLab.HilbertBookZero

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Synthetic segment sums

Small dimension-free utilities for the witness-based relation
`HilbertSegmentSumGreater`.
-/

/--
Construct a point realizing the sum of two non-null segments.

If AB and CD are non-null, there is a point P beyond B on ray AB
such that BP is congruent to CD.
-/
theorem hilbert_segmentSum_witness
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hAB : Not (A = B))
    (hCD : Not (C = D)) :
    exists P : Geo.Point,
      Geo.Between A B P /\
      Geo.Congruent B P C D := by

  cases
      HilbertOrder.between_extension
        A B hAB with
  | intro R hABR =>

      have hBR : Not (B = R) :=
        (HilbertOrder.between_incidence
          A B R hABR).2.1

      cases
          bookZero_49_layoff
            Geo
            B R
            C D
            hBR
            hCD with
      | intro P hP =>

          have hRayBRP :
              HilbertSameRay Geo B R P :=
            hP.1

          have hBP_CD :
              Geo.Congruent B P C D :=
            hP.2

          have hRayBAA :
              HilbertSameRay Geo B A A :=
            hilbert_sameRay_refl
              Geo B A hAB

          have hABP :
              Geo.Between A B P :=
            hilbert_between_transport_sameRays
              Geo
              A B R
              A P
              hABR
              hRayBAA
              hRayBRP

          exact
            Exists.intro P
              (And.intro hABP hBP_CD)


/--
If EF is strictly shorter than the first summand AB, then
AB + CD is strictly greater than EF, provided both summands are
non-null.
-/
theorem hilbertSegmentSumGreater_of_less_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hAB : Not (A = B))
    (hCD : Not (C = D))
    (hEF_AB :
      HilbertSegmentLess Geo E F A B) :
    HilbertSegmentSumGreater
      Geo A B C D E F := by

  cases
      hilbert_segmentSum_witness
        Geo
        A B C D
        hAB
        hCD with
  | intro P hP =>

      have hABP :
          Geo.Between A B P :=
        hP.1

      have hBP_CD :
          Geo.Congruent B P C D :=
        hP.2

      have hAB_AP :
          HilbertSegmentLess Geo A B A P :=
        hilbert_segmentLess_of_between
          Geo
          A B P
          hABP

      have hEF_AP :
          HilbertSegmentLess Geo E F A P :=
        bookZero_52_lessThanTransitive
          Geo
          E F
          A B
          A P
          hEF_AB
          hAB_AP

      exact
        Exists.intro P
          (And.intro hABP
            (And.intro hBP_CD hEF_AP))


/--
If EF is congruent to the first summand AB, then
AB + CD is strictly greater than EF, provided both summands are
non-null.
-/
theorem hilbertSegmentSumGreater_of_congruent_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hAB : Not (A = B))
    (hCD : Not (C = D))
    (hEF_AB :
      Geo.Congruent E F A B) :
    HilbertSegmentSumGreater
      Geo A B C D E F := by

  cases
      hilbert_segmentSum_witness
        Geo
        A B C D
        hAB
        hCD with
  | intro P hP =>

      have hABP :
          Geo.Between A B P :=
        hP.1

      have hBP_CD :
          Geo.Congruent B P C D :=
        hP.2

      have hAB_AP :
          HilbertSegmentLess Geo A B A P :=
        hilbert_segmentLess_of_between
          Geo
          A B P
          hABP

      have hEF_AP :
          HilbertSegmentLess Geo E F A P :=
        hilbert_segmentLess_congruent_left
          Geo
          A B
          E F
          A P
          hAB_AP
          hEF_AB

      exact
        Exists.intro P
          (And.intro hABP
            (And.intro hBP_CD hEF_AP))


/--
The witness-based strict segment sum is commutative in its two
summands.

From

    AB + CD > EF

we obtain

    CD + AB > EF.
-/
theorem hilbertSegmentSumGreater_swap
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (h :
      HilbertSegmentSumGreater
        Geo A B C D E F) :
    HilbertSegmentSumGreater
      Geo C D A B E F := by

  cases h with
  | intro P hP =>

      have hABP :
          Geo.Between A B P :=
        hP.1

      have hBP_CD :
          Geo.Congruent B P C D :=
        hP.2.1

      have hEF_AP :
          HilbertSegmentLess Geo E F A P :=
        hP.2.2

      have hAB : Not (A = B) :=
        (HilbertOrder.between_incidence
          A B P hABP).1

      have hBP : Not (B = P) :=
        (HilbertOrder.between_incidence
          A B P hABP).2.1

      have hCD : Not (C = D) :=
        bookZero_nullSegment3
          Geo
          B P
          C D
          hBP
          hBP_CD

      cases
          hilbert_segmentSum_witness
            Geo
            C D A B
            hCD
            hAB with
      | intro Q hQ =>

          have hCDQ :
              Geo.Between C D Q :=
            hQ.1

          have hDQ_AB :
              Geo.Congruent D Q A B :=
            hQ.2

          have hQDC :
              Geo.Between Q D C :=
            (HilbertOrder.between_incidence
              C D Q hCDQ).2.2.2.2

          have hQD_AB :
              Geo.Congruent Q D A B :=
            CongruentReverseFirst
              Geo
              D Q
              A B
              hDQ_AB

          have hAB_QD :
              Geo.Congruent A B Q D :=
            hilbert_congruent_symmetry
              Geo
              Q D
              A B
              hQD_AB

          have hBP_DC :
              Geo.Congruent B P D C :=
            CongruentSwapSecond
              Geo
              B P
              C D
              hBP_CD

          have hAP_QC :
              Geo.Congruent A P Q C :=
            bookZero_sumOfParts
              Geo
              A B P
              Q D C
              hAB_QD
              hBP_DC
              hABP
              hQDC

          have hAP_CQ :
              Geo.Congruent A P C Q :=
            CongruentSwapSecond
              Geo
              A P
              Q C
              hAP_QC

          have hEF_CQ :
              HilbertSegmentLess Geo E F C Q :=
            bookZero_30_lessThanCongruence
              Geo
              E F
              A P
              C Q
              hEF_AP
              hAP_CQ

          exact
            Exists.intro Q
              (And.intro hCDQ
                (And.intro hDQ_AB hEF_CQ))

end Geometry

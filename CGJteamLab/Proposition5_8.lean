import CGJteamLab.HilbertInterfaceV

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.8
------------------------------------------------------------------------

/--
Euclid V.8, first half.

If c < a, then a has a greater ratio to d than c has to d.
-/
theorem hilbertEudoxus_v8_greater_first_same_second
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a c d : HilbertPositiveSegmentClass Geo)
    (hca : HilbertPositiveSegmentLess Geo c a) :
    HilbertEudoxusGreaterRatio Geo a d c d := by

  rcases
      hilbertPositiveSegment_exists_add_of_less
        Geo c a hca
    with
    ⟨e, hce⟩

  rcases
      hilbertPositiveSegment_archimedean
        Geo e d
    with
    ⟨m, hDE⟩

  let mc :=
    hilbertPositiveSegmentMultiple Geo m c

  let me :=
    hilbertPositiveSegmentMultiple Geo m e

  rcases
      hilbertPositiveSegment_exists_least_exceeding_multiple
        Geo d mc
    with
    ⟨n, hLeast, hMinimal⟩

  have hMa :
      hilbertPositiveSegmentMultiple Geo m a =
        mc + me := by

    calc
      hilbertPositiveSegmentMultiple Geo m a =
          hilbertPositiveSegmentMultiple Geo m (c + e) := by
        rw [hce]

      _ =
          hilbertPositiveSegmentMultiple Geo m c +
            hilbertPositiveSegmentMultiple Geo m e :=
        hilbertPositiveSegmentMultiple_add
          Geo m c e

      _ = mc + me := by
        rfl

  refine
    ⟨m, n, ?_, ?_⟩

  · cases n with

    | zero =>

        have hMeSum :
            HilbertPositiveSegmentLess
              Geo me (mc + me) := by

          have h0 :=
            hilbertPositiveSegment_lt_add_right
              Geo me mc

          rw [
            hilbertPositiveSegment_add_comm
              Geo me mc
          ] at h0

          exact h0

        have hDSum :
            HilbertPositiveSegmentLess
              Geo d (mc + me) :=
          hilbertPositiveSegmentLess_trans
            Geo d me (mc + me)
            hDE hMeSum

        rw [
          hilbertPositiveSegmentMultiple_zero,
          hMa
        ]

        exact hDSum

    | succ k =>

        have hk :
            k < Nat.succ k :=
          Nat.lt_succ_self k

        have hNotPrev :
            Not
              (HilbertPositiveSegmentLess
                Geo
                mc
                (hilbertPositiveSegmentMultiple Geo k d)) :=
          hMinimal k hk

        rcases
            hilbertPositiveSegmentLess_trichotomy
              Geo
              (hilbertPositiveSegmentMultiple Geo k d)
              mc
          with
          hPrev | hEq | hReverse

        · have hAdd :
              HilbertPositiveSegmentLess
                Geo
                (hilbertPositiveSegmentMultiple Geo k d + d)
                (mc + me) :=
            hilbertPositiveSegment_add_lt_add
              Geo
              (hilbertPositiveSegmentMultiple Geo k d)
              mc
              d
              me
              hPrev
              hDE

          rw [
            hilbertPositiveSegmentMultiple_succ,
            hMa
          ]

          exact hAdd

        · have hAdd :
              HilbertPositiveSegmentLess
                Geo
                (hilbertPositiveSegmentMultiple Geo k d + d)
                (mc + me) := by

            rw [hEq]

            exact
              hilbertPositiveSegment_add_lt_add_left
                Geo d me mc hDE

          rw [
            hilbertPositiveSegmentMultiple_succ,
            hMa
          ]

          exact hAdd

        · exact
            False.elim
              (hNotPrev hReverse)

  · exact
      hilbertPositiveSegmentLess_asymm
        Geo
        mc
        (hilbertPositiveSegmentMultiple Geo n d)
        hLeast

/--
Euclid V.8, second half.

If b < d, then a has a greater ratio to b than a has to d.
-/
theorem hilbertEudoxus_v8_same_first_lesser_second
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b d : HilbertPositiveSegmentClass Geo)
    (hbd : HilbertPositiveSegmentLess Geo b d) :
    HilbertEudoxusGreaterRatio Geo a b a d := by

  rcases
      hilbertPositiveSegment_exists_add_of_less
        Geo b d hbd
    with
    ⟨e, hbe⟩

  rcases
      hilbertPositiveSegment_archimedean
        Geo e a
    with
    ⟨n, hAE⟩

  let nb :=
    hilbertPositiveSegmentMultiple Geo n b

  let ne :=
    hilbertPositiveSegmentMultiple Geo n e

  rcases
      hilbertPositiveSegment_exists_least_exceeding_multiple
        Geo a nb
    with
    ⟨m, hLeast, hMinimal⟩

  have hNd :
      hilbertPositiveSegmentMultiple Geo n d =
        nb + ne := by

    calc
      hilbertPositiveSegmentMultiple Geo n d =
          hilbertPositiveSegmentMultiple Geo n (b + e) := by
        rw [hbe]

      _ =
          hilbertPositiveSegmentMultiple Geo n b +
            hilbertPositiveSegmentMultiple Geo n e :=
        hilbertPositiveSegmentMultiple_add
          Geo n b e

      _ = nb + ne := by
        rfl

  refine
    ⟨m, n, hLeast, ?_⟩

  cases m with

  | zero =>

      have hNeSum :
          HilbertPositiveSegmentLess
            Geo ne (nb + ne) := by

        have h0 :=
          hilbertPositiveSegment_lt_add_right
            Geo ne nb

        rw [
          hilbertPositiveSegment_add_comm
            Geo ne nb
        ] at h0

        exact h0

      have hANd :
          HilbertPositiveSegmentLess
            Geo a
            (hilbertPositiveSegmentMultiple Geo n d) := by

        rw [hNd]

        exact
          hilbertPositiveSegmentLess_trans
            Geo a ne (nb + ne)
            hAE hNeSum

      simpa only [
        hilbertPositiveSegmentMultiple_zero
      ] using
        (hilbertPositiveSegmentLess_asymm
          Geo
          a
          (hilbertPositiveSegmentMultiple Geo n d)
          hANd)

  | succ k =>

      have hk :
          k < Nat.succ k :=
        Nat.lt_succ_self k

      have hNotPrev :
          Not
            (HilbertPositiveSegmentLess
              Geo
              nb
              (hilbertPositiveSegmentMultiple Geo k a)) :=
        hMinimal k hk

      rcases
          hilbertPositiveSegmentLess_trichotomy
            Geo
            (hilbertPositiveSegmentMultiple Geo k a)
            nb
        with
        hPrev | hEq | hReverse

      · have hAdd :
            HilbertPositiveSegmentLess
              Geo
              (hilbertPositiveSegmentMultiple Geo k a + a)
              (nb + ne) :=
          hilbertPositiveSegment_add_lt_add
            Geo
            (hilbertPositiveSegmentMultiple Geo k a)
            nb
            a
            ne
            hPrev
            hAE

        have hScaled :
            HilbertPositiveSegmentLess
              Geo
              (hilbertPositiveSegmentMultiple
                Geo (Nat.succ k) a)
              (hilbertPositiveSegmentMultiple Geo n d) := by

          rw [
            hilbertPositiveSegmentMultiple_succ,
            hNd
          ]

          exact hAdd

        exact
          hilbertPositiveSegmentLess_asymm
            Geo
            (hilbertPositiveSegmentMultiple
              Geo (Nat.succ k) a)
            (hilbertPositiveSegmentMultiple Geo n d)
            hScaled

      · have hAdd :
            HilbertPositiveSegmentLess
              Geo
              (hilbertPositiveSegmentMultiple Geo k a + a)
              (nb + ne) := by

          rw [hEq]

          exact
            hilbertPositiveSegment_add_lt_add_left
              Geo a ne nb hAE

        have hScaled :
            HilbertPositiveSegmentLess
              Geo
              (hilbertPositiveSegmentMultiple
                Geo (Nat.succ k) a)
              (hilbertPositiveSegmentMultiple Geo n d) := by

          rw [
            hilbertPositiveSegmentMultiple_succ,
            hNd
          ]

          exact hAdd

        exact
          hilbertPositiveSegmentLess_asymm
            Geo
            (hilbertPositiveSegmentMultiple
              Geo (Nat.succ k) a)
            (hilbertPositiveSegmentMultiple Geo n d)
            hScaled

      · exact
          False.elim
            (hNotPrev hReverse)

/--
Euclid V.8.

Of unequal positive magnitudes, the greater has to the same a greater
ratio than the less has; and the same has to the less a greater ratio
than it has to the greater.
-/
theorem euclid_proposition_5_8
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a c d : HilbertPositiveSegmentClass Geo)
    (hca : HilbertPositiveSegmentLess Geo c a) :
    HilbertEudoxusGreaterRatio Geo a d c d /\
    HilbertEudoxusGreaterRatio Geo d c d a := by

  constructor

  · exact
      hilbertEudoxus_v8_greater_first_same_second
        Geo a c d hca

  · exact
      hilbertEudoxus_v8_same_first_lesser_second
        Geo d c a hca

end Geometry

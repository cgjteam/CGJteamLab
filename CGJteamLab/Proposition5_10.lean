import CGJteamLab.HilbertInterfaceV

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.10
------------------------------------------------------------------------

/--
Euclid V.10, first half.

If a has a greater ratio to d than c has to d, then c < a.
-/
theorem hilbertEudoxus_v10_same_second_lt_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a c d : HilbertPositiveSegmentClass Geo)
    (h :
      HilbertEudoxusGreaterRatio Geo a d c d) :
    HilbertPositiveSegmentLess Geo c a := by

  rcases h with
    ⟨m, n, hGreater, hNotGreater⟩

  rcases
      hilbertPositiveSegmentLess_trichotomy
        Geo c a
    with
    hca | hEq | hac

  · exact hca

  · subst a
    exact
      False.elim
        (hNotGreater hGreater)

  · have hMul :
        HilbertPositiveSegmentLess
          Geo
          (hilbertPositiveSegmentMultiple Geo m a)
          (hilbertPositiveSegmentMultiple Geo m c) :=
      hilbertPositiveSegmentMultiple_lt
        Geo m a c hac

    have hContr :
        HilbertPositiveSegmentLess
          Geo
          (hilbertPositiveSegmentMultiple Geo n d)
          (hilbertPositiveSegmentMultiple Geo m c) :=
      hilbertPositiveSegmentLess_trans
        Geo
        (hilbertPositiveSegmentMultiple Geo n d)
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m c)
        hGreater
        hMul

    exact
      False.elim
        (hNotGreater hContr)

/--
Euclid V.10, second half.

If a has a greater ratio to b than a has to d, then b < d.
-/
theorem hilbertEudoxus_v10_same_first_lt_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b d : HilbertPositiveSegmentClass Geo)
    (h :
      HilbertEudoxusGreaterRatio Geo a b a d) :
    HilbertPositiveSegmentLess Geo b d := by

  rcases h with
    ⟨m, n, hGreater, hNotGreater⟩

  rcases
      hilbertPositiveSegmentLess_trichotomy
        Geo b d
    with
    hbd | hEq | hdb

  · exact hbd

  · subst d
    exact
      False.elim
        (hNotGreater hGreater)

  · have hMul :
        HilbertPositiveSegmentLess
          Geo
          (hilbertPositiveSegmentMultiple Geo n d)
          (hilbertPositiveSegmentMultiple Geo n b) :=
      hilbertPositiveSegmentMultiple_lt
        Geo n d b hdb

    have hContr :
        HilbertPositiveSegmentLess
          Geo
          (hilbertPositiveSegmentMultiple Geo n d)
          (hilbertPositiveSegmentMultiple Geo m a) :=
      hilbertPositiveSegmentLess_trans
        Geo
        (hilbertPositiveSegmentMultiple Geo n d)
        (hilbertPositiveSegmentMultiple Geo n b)
        (hilbertPositiveSegmentMultiple Geo m a)
        hMul
        hGreater

    exact
      False.elim
        (hNotGreater hContr)

/--
Euclid V.10, packaged in the two comparison forms used by the library.
-/
theorem euclid_proposition_5_10
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo) :
    (HilbertEudoxusGreaterRatio Geo a d c d ->
      HilbertPositiveSegmentLess Geo c a) /\
    (HilbertEudoxusGreaterRatio Geo a b a d ->
      HilbertPositiveSegmentLess Geo b d) := by

  constructor

  · exact
      hilbertEudoxus_v10_same_second_lt_first
        Geo a c d

  · exact
      hilbertEudoxus_v10_same_first_lt_second
        Geo a b d

end Geometry

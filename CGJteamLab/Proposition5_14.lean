import CGJteamLab.Proposition5_8
import CGJteamLab.Proposition5_10
import CGJteamLab.Proposition5_13

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.14
------------------------------------------------------------------------

/--
V.14 strict direction:
under equal ratios, increasing the first term increases the second.
-/
theorem hilbertEudoxus_v14_lt_second_of_lt_first
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d)
    (hac :
      HilbertPositiveSegmentLess Geo a c) :
    HilbertPositiveSegmentLess Geo b d := by

  have hV8 :
      HilbertEudoxusGreaterRatio Geo c d a d :=
    hilbertEudoxus_v8_greater_first_same_second
      Geo c a d hac

  have hTransport :
      HilbertEudoxusGreaterRatio Geo a b a d :=
    euclid_proposition_5_13
      Geo
      a b c d a d
      hProp
      hV8

  exact
    hilbertEudoxus_v10_same_first_lt_second
      Geo a b d hTransport

/--
V.14 equality direction:
under equal ratios, equality of the first terms forces equality
of the second terms.
-/
theorem hilbertEudoxus_v14_eq_second_of_eq_first
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d)
    (hac : a = c) :
    b = d := by

  subst c

  rcases
      hilbertPositiveSegmentLess_trichotomy
        Geo b d
    with
    hbd | hEq | hdb

  · have hGreater :
        HilbertEudoxusGreaterRatio Geo a b a d :=
      hilbertEudoxus_v8_same_first_lesser_second
        Geo a b d hbd

    exact
      False.elim
        ((hilbertEudoxusProportion_not_greater
          Geo a b a d hProp)
          hGreater)

  · exact hEq

  · have hGreater :
        HilbertEudoxusGreaterRatio Geo a d a b :=
      hilbertEudoxus_v8_same_first_lesser_second
        Geo a d b hdb

    have hSymm :
        HilbertEudoxusProportion Geo a d a b :=
      hilbertEudoxusProportion_symm
        Geo a b a d hProp

    exact
      False.elim
        ((hilbertEudoxusProportion_not_greater
          Geo a d a b hSymm)
          hGreater)

/--
Euclid V.14, less-than comparison form.
-/
theorem hilbertEudoxus_v14_lt_iff
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d) :
    (HilbertPositiveSegmentLess Geo a c
      <->
     HilbertPositiveSegmentLess Geo b d) := by

  constructor

  · exact
      hilbertEudoxus_v14_lt_second_of_lt_first
        Geo a b c d hProp

  · intro hbd

    rcases
        hilbertPositiveSegmentLess_trichotomy
          Geo a c
      with
      hac | hEq | hca

    · exact hac

    · have hbdEq :
          b = d :=
        hilbertEudoxus_v14_eq_second_of_eq_first
          Geo a b c d hProp hEq

      exact
        False.elim
          ((hilbertPositiveSegmentLess_ne
            Geo b d hbd)
            hbdEq)

    · have hSymm :
          HilbertEudoxusProportion Geo c d a b :=
        hilbertEudoxusProportion_symm
          Geo a b c d hProp

      have hdb :
          HilbertPositiveSegmentLess Geo d b :=
        hilbertEudoxus_v14_lt_second_of_lt_first
          Geo c d a b hSymm hca

      exact
        False.elim
          ((hilbertPositiveSegmentLess_asymm
            Geo b d hbd)
            hdb)

/--
Euclid V.14, equality comparison form.
-/
theorem hilbertEudoxus_v14_eq_iff
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d) :
    (a = c <-> b = d) := by

  constructor

  · exact
      hilbertEudoxus_v14_eq_second_of_eq_first
        Geo a b c d hProp

  · intro hbd

    rcases
        hilbertPositiveSegmentLess_trichotomy
          Geo a c
      with
      hac | hEq | hca

    · have hbdLt :
          HilbertPositiveSegmentLess Geo b d :=
        (hilbertEudoxus_v14_lt_iff
          Geo a b c d hProp).1
          hac

      exact
        False.elim
          ((hilbertPositiveSegmentLess_ne
            Geo b d hbdLt)
            hbd)

    · exact hEq

    · have hSymm :
          HilbertEudoxusProportion Geo c d a b :=
        hilbertEudoxusProportion_symm
          Geo a b c d hProp

      have hdbLt :
          HilbertPositiveSegmentLess Geo d b :=
        (hilbertEudoxus_v14_lt_iff
          Geo c d a b hSymm).1
          hca

      exact
        False.elim
          ((hilbertPositiveSegmentLess_ne
            Geo d b hdbLt)
            hbd.symm)

/--
Euclid V.14, greater-than comparison form.
-/
theorem hilbertEudoxus_v14_gt_iff
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d) :
    (HilbertPositiveSegmentLess Geo c a
      <->
     HilbertPositiveSegmentLess Geo d b) := by

  have hSymm :
      HilbertEudoxusProportion Geo c d a b :=
    hilbertEudoxusProportion_symm
      Geo a b c d hProp

  exact
    hilbertEudoxus_v14_lt_iff
      Geo c d a b hSymm

/--
Euclid V.14, packaged as preservation of all three comparisons between
corresponding terms of equal ratios.
-/
theorem euclid_proposition_5_14
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp : HilbertEudoxusProportion Geo a b c d) :
    (HilbertPositiveSegmentLess Geo a c <->
      HilbertPositiveSegmentLess Geo b d) /\
    (a = c <-> b = d) /\
    (HilbertPositiveSegmentLess Geo c a <->
      HilbertPositiveSegmentLess Geo d b) := by

  exact
    ⟨hilbertEudoxus_v14_lt_iff
        Geo a b c d hProp,
     hilbertEudoxus_v14_eq_iff
        Geo a b c d hProp,
     hilbertEudoxus_v14_gt_iff
        Geo a b c d hProp⟩

end Geometry

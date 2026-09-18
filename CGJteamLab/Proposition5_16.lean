import CGJteamLab.Proposition5_11
import CGJteamLab.Proposition5_14
import CGJteamLab.Proposition5_15

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.16
------------------------------------------------------------------------

/--
Euclid V.16 (alternando) for Eudoxus proportions.

From

  a:b = c:d

we obtain

  a:c = b:d.
-/
theorem euclid_proposition_5_16
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d) :
    HilbertEudoxusProportion Geo a c b d := by

  intro m n

  have hScaleAB :
      HilbertEudoxusProportion
        Geo
        a b
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b) :=
    euclid_proposition_5_15
      Geo a b m

  have hScaleCD :
      HilbertEudoxusProportion
        Geo
        c d
        (hilbertPositiveSegmentMultiple Geo n c)
        (hilbertPositiveSegmentMultiple Geo n d) :=
    euclid_proposition_5_15
      Geo c d n

  have hScaledAB_to_CD :
      HilbertEudoxusProportion
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b)
        c d := by

    exact
      euclid_proposition_5_11
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b)
        a b
        c d
        (hilbertEudoxusProportion_symm
          Geo
          a b
          (hilbertPositiveSegmentMultiple Geo m a)
          (hilbertPositiveSegmentMultiple Geo m b)
          hScaleAB)
        hProp

  have hScaled :
      HilbertEudoxusProportion
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b)
        (hilbertPositiveSegmentMultiple Geo n c)
        (hilbertPositiveSegmentMultiple Geo n d) :=
    euclid_proposition_5_11
      Geo
      (hilbertPositiveSegmentMultiple Geo m a)
      (hilbertPositiveSegmentMultiple Geo m b)
      c d
      (hilbertPositiveSegmentMultiple Geo n c)
      (hilbertPositiveSegmentMultiple Geo n d)
      hScaledAB_to_CD
      hScaleCD

  exact
    ⟨hilbertEudoxus_v14_lt_iff
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b)
        (hilbertPositiveSegmentMultiple Geo n c)
        (hilbertPositiveSegmentMultiple Geo n d)
        hScaled,
     hilbertEudoxus_v14_eq_iff
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b)
        (hilbertPositiveSegmentMultiple Geo n c)
        (hilbertPositiveSegmentMultiple Geo n d)
        hScaled,
     hilbertEudoxus_v14_gt_iff
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo m b)
        (hilbertPositiveSegmentMultiple Geo n c)
        (hilbertPositiveSegmentMultiple Geo n d)
        hScaled⟩

end Geometry

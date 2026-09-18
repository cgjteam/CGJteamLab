import CGJteamLab.HilbertInterfaceV

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.15
------------------------------------------------------------------------

/--
Euclid V.15 content needed for XI.23:

  a:b = M_k(a):M_k(b).

We prove it directly from Eudoxus Def.5 and preservation/reflection
of order and equality under a common positive multiple.
-/
theorem euclid_proposition_5_15
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo)
    (k : Nat) :
    HilbertEudoxusProportion
      Geo
      a b
      (hilbertPositiveSegmentMultiple Geo k a)
      (hilbertPositiveSegmentMultiple Geo k b) := by

  intro m n

  exact
    ⟨(hilbertPositiveSegmentMultiple_nested_lt_iff
        Geo m n k a b).symm,
     (hilbertPositiveSegmentMultiple_nested_eq_iff
        Geo m n k a b).symm,
     (hilbertPositiveSegmentMultiple_nested_lt_iff
        Geo n m k b a).symm⟩

end Geometry

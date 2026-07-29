import CGJteamLab.Common

namespace Geometry
namespace Tarski

universe u

/--
Primitive geometric signature used by the Tarski route.
-/
structure Geo where
  Point : Type u

  Between :
    Point -> Point -> Point -> Prop

  SegmentCongruent :
    UnorderedPair Point ->
    UnorderedPair Point ->
    Prop

namespace Geo

/-- The unoriented segment with endpoints `A` and `B`. -/
def Segment
    (Geo : Tarski.Geo)
    (A B : Geo.Point) :
    UnorderedPair Geo.Point :=
  Common.Segment A B

/--
Congruence of the unoriented segments `AB` and `CD`.

The four-point interface is retained for compatibility with the rest of
the Tarski geometry library.
-/
def Congruent
    (Geo : Tarski.Geo)
    (A B C D : Geo.Point) : Prop :=
  Common.PairRelation Geo.SegmentCongruent A B C D

/-- Reversal of the endpoints of an unoriented segment. -/
theorem segment_swap
    (Geo : Tarski.Geo)
    (A B : Geo.Point) :
    Geo.Segment A B = Geo.Segment B A :=
  Common.segment_swap A B

theorem congruent_reverse_first
    (Geo : Tarski.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D <->
    Geo.Congruent B A C D :=
  Common.pairRelation_reverse_first
    Geo.SegmentCongruent A B C D

theorem congruent_reverse_second
    (Geo : Tarski.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D <->
    Geo.Congruent A B D C :=
  Common.pairRelation_reverse_second
    Geo.SegmentCongruent A B C D

end Geo

end Tarski
end Geometry

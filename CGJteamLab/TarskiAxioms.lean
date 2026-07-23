import CGJteamLab.GeometryCore

namespace Geometry

namespace Tarski

universe u

/-!
# TarskiAxioms

An independent Lean formalization of the geometric content of Tarski's
axioms. The primitive point type, betweenness relation, and segment
congruence relation are reused from `GeometryCore`.

The mathematical reference is:

Alfred Tarski and Steven Givant, "Tarski's System of Geometry",
*Bulletin of Symbolic Logic* 5 (1999), 175-214.

GeoCoq's presentation of the Schwabhäuser-Szmielew-Tarski hierarchy
was consulted only as a completeness and organization check. No GeoCoq
code or proofs were copied or translated.

The continuity schema is intentionally not included in this initial
axiom hierarchy.
-/

/--
The dimension-independent neutral axioms of Tarski geometry.

Only `Geo.Point`, `Geo.Between`, and `Geo.Congruent` occur in these
axioms. Equality is Lean's logical equality.
-/
class TarskiNeutral (Geo : Geometry.Geo) : Prop where
  /-- Ax.1: reflexivity (endpoint reversal) for segment congruence. -/
  congruent_reversal :
    ∀ A B : Geo.Point,
      Geo.Congruent A B B A

  /-- Ax.2: transitivity for segment congruence. -/
  congruent_transitivity :
    ∀ A B P Q R S : Geo.Point,
      Geo.Congruent A B P Q →
      Geo.Congruent A B R S →
      Geo.Congruent P Q R S

  /-- Ax.3: identity for segment congruence. -/
  congruent_identity :
    ∀ A B C : Geo.Point,
      Geo.Congruent A B C C →
      A = B

  /-- Ax.4: construction of a segment on a prescribed ray. -/
  segment_construction :
    ∀ Q A B C : Geo.Point,
      ∃ X : Geo.Point,
        Geo.Between Q A X ∧
        Geo.Congruent A X B C

  /-- Ax.5: the five-segment axiom. -/
  five_segment :
    ∀ A A' B B' C C' D D' : Geo.Point,
      A ≠ B →
      Geo.Between A B C →
      Geo.Between A' B' C' →
      Geo.Congruent A B A' B' →
      Geo.Congruent B C B' C' →
      Geo.Congruent A D A' D' →
      Geo.Congruent B D B' D' →
      Geo.Congruent C D C' D'

  /-- Ax.6: identity for betweenness. -/
  between_identity :
    ∀ A B : Geo.Point,
      Geo.Between A B A →
      A = B

  /-- Ax.7: the inner form of Pasch's axiom. -/
  inner_pasch :
    ∀ A B C P Q : Geo.Point,
      Geo.Between A P C →
      Geo.Between B Q C →
      ∃ X : Geo.Point,
        Geo.Between P X B ∧
        Geo.Between Q X A

/-- The lower and upper dimension axioms for a Tarski plane. -/
class TarskiPlane (Geo : Geometry.Geo) : Prop
    extends TarskiNeutral Geo where
  /-- Ax.8(2): three non-collinear points exist. -/
  lower_dimension_two :
    ∃ A B C : Geo.Point,
      ¬ Geo.Between A B C ∧
      ¬ Geo.Between B C A ∧
      ¬ Geo.Between C A B

  /--
  Ax.9(2): three points equidistant from two distinct points are
  collinear, expressed using the three cyclic betweenness cases.
  -/
  upper_dimension_two :
    ∀ A B C P Q : Geo.Point,
      P ≠ Q →
      Geo.Congruent A P A Q →
      Geo.Congruent B P B Q →
      Geo.Congruent C P C Q →
      Geo.Between A B C ∨
      Geo.Between B C A ∨
      Geo.Between C A B

/--
A two-dimensional Euclidean Tarski geometry.

The field `euclid` is the first form of Euclid's axiom, Ax.10.
-/
class TarskiEuclideanPlane (Geo : Geometry.Geo) : Prop
    extends TarskiPlane Geo where
  /-- Ax.10: the first form of Euclid's axiom. -/
  euclid :
    ∀ A B C D T : Geo.Point,
      Geo.Between A D T →
      Geo.Between B D C →
      A ≠ D →
      ∃ X Y : Geo.Point,
        Geo.Between A B X ∧
        Geo.Between A C Y ∧
        Geo.Between X T Y

end Tarski

end Geometry

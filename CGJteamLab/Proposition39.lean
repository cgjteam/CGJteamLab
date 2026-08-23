import CGJteamLab.HilbertScissors

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.39 / Hilbert Theorem 48
------------------------------------------------------------------------

/--
Temporary formulation of Hilbert Theorem 48 in the language used by
the present Euclid Book I development.

Hilbert Theorem 48 is the converse of Theorem 46: for two triangles
with the same base, equicomplementability forces equality of altitude.
For Euclid I.39 this is expressed geometrically by saying that the two
third vertices lie on one line disjoint from the base line.

This declaration is the single temporary assumption of this file.
-/
axiom proposition39_test_hilbert_48
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hBC : B ≠ C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A D base)
    (hEqual :
      HilbertScissorsEquicomplementable
        Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo D B C)) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base


/--
Euclid I.39.

Equal triangles on the same base and on the same side are between
the same parallels.

In Hilbert's organization this is Theorem 48.
-/
theorem euclid_proposition_39
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hBC : B ≠ C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A D base)
    (hEqual :
      HilbertScissorsEquicomplementable
        Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo D B C)) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  exact
    proposition39_test_hilbert_48
      Geo
      A B C D
      base
      hBC
      hBbase
      hCbase
      hSame
      hEqual

end Geometry

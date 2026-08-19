import CGJteamLab.HilbertScissors

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid I.35.

Parallelograms on the same base and in the same parallels are
equicomplementable in the formal Hilbert scissors calculus.

The hypotheses `hADF` and `hAEF` encode the common upper parallel
configuration used in the present Hilbert reconstruction.
-/
theorem euclid_proposition_35
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F)
    (hAEF : Collinear Geo A E F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E B C F) := by
  exact
    test_i35_complete
      Geo
      A B C D E F
      hABCD
      hEBCF
      hADF
      hAEF

end Geometry

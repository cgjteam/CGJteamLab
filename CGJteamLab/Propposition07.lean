import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.7.

Two points on the same side of a fixed base cannot have
the same prescribed distances from both endpoints of the base.
-/
theorem euclid_proposition_7
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hSame : HilbertSameSide Geo C D base)
    (hACAD : Geo.Congruent A C A D)
    (hBCBD : Geo.Congruent B C B D) :
    C = D := by

  by_cases hCD : C = D
  · exact hCD
  · have hCbase :
        ¬ HilbertIncidence.OnLine C base :=
      hSame.1

    have hDbase :
        ¬ HilbertIncidence.OnLine D base :=
      hSame.2.1

    have hABC :
        ¬ Collinear Geo A B C :=
      hilbert_not_collinear_of_off_line
        Geo A B C
        base
        hAB
        hAbase
        hBbase
        hCbase

    have hABD :
        ¬ Collinear Geo A B D :=
      hilbert_not_collinear_of_off_line
        Geo A B D
        base
        hAB
        hAbase
        hBbase
        hDbase
    have hABAB :
        Geo.Congruent A B A B :=
      hilbert_congruent_reflexive Geo A B

    have hSSS :=
      HilbertSSS
        Geo
        A B C
        A B D
        hABC
        hABAB
        hBCBD
        hACAD

    have hAngleB :
        Geo.AngleCongruent A B C A B D :=
      hSSS.2.angleB

    rcases
        hilbert_angle_unique_common_ray
          Geo
          A B C D
          base
          hAB
          hAbase
          hBbase
          hCbase
          hSame
          hAngleB with
      ⟨X, hRayXC, hRayXD⟩

    have hBD_BC :
        Geo.Congruent B D B C :=
      hilbert_congruent_symmetry
        Geo B C B D hBCBD

    exact
      hilbert_segment_construction_unique
        Geo
        B C
        B X
        C D
        hRayXC
        hRayXD
        (hilbert_congruent_reflexive Geo B C)
        hBD_BC



end Geometry

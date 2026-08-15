import CGJteamLab.Proposition24

namespace Geometry

universe u

variable {Geo : Geometry.Geo}

/--
Euclid, Book I, Proposition 25.

If two triangles have two corresponding sides congruent, and the third
side of the first triangle is greater than the third side of the second,
then the included angle of the first triangle is greater than the
included angle of the second.
-/
theorem euclid_proposition_25
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hDEF : ¬ PrimCollinear Geo D E F)
    (hAB_DE : Geo.Congruent A B D E)
    (hAC_DF : Geo.Congruent A C D F)
    (hEF_BC : HilbertSegmentLess Geo E F B C) :
    HilbertAngleLess Geo E D F B A C := by

  have hBAC :
      ¬ PrimCollinear Geo B A C := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hEDF :
      ¬ PrimCollinear Geo E D F := by
    intro h
    exact hDEF
      (PrimCollinearSwap Geo E D F h)

  rcases
      angle_trichotomy
        (Geo := Geo)
        B A C
        E D F
        hBAC
        hEDF with
    hAnglesEq | hBAC_EDF | hEDF_BAC

  --------------------------------------------------------------------
  -- Case 1: BAC ~= EDF.
  --
  -- SAS gives BC ~= EF, contradicting EF < BC.
  --------------------------------------------------------------------

  ·
    have hSAS :=
      SAS
        (Geo := Geo)
        A B C
        D E F
        hABC
        hDEF
        hAB_DE
        hAnglesEq
        hAC_DF

    have hBC_EF :
        Geo.Congruent B C E F :=
      hSAS.sideBC

    have hEF_BC_cong :
        Geo.Congruent E F B C :=
      hilbert_congruent_symmetry
        Geo B C E F hBC_EF

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
            Geo E F B C hEF_BC)
          hEF_BC_cong)

  --------------------------------------------------------------------
  -- Case 2: BAC < EDF.
  --
  -- Apply Proposition I.24 with the triangles interchanged.
  -- This gives BC < EF, contradicting EF < BC.
  --------------------------------------------------------------------

  ·
    have hDE_AB :
        Geo.Congruent D E A B :=
      hilbert_congruent_symmetry
        Geo A B D E hAB_DE

    have hDF_AC :
        Geo.Congruent D F A C :=
      hilbert_congruent_symmetry
        Geo A C D F hAC_DF

    have hBC_EF :
        HilbertSegmentLess Geo B C E F :=
      euclid_proposition_24
        (Geo := Geo)
        D E F
        A B C
        hDEF
        hABC
        hDE_AB
        hDF_AC
        hBAC_EDF

    exact
      False.elim
        ((hilbert_segmentLess_asymm
            Geo E F B C hEF_BC)
          hBC_EF)

  --------------------------------------------------------------------
  -- Case 3: EDF < BAC.
  --
  -- This is exactly the desired conclusion.
  --------------------------------------------------------------------

  · exact hEDF_BAC


end Geometry

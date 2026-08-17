import CGJteamLab.Proposition27

namespace Geometry

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]

/--
Euclid I.28, corresponding-angle criterion.

The transversal contains E-G-H.
The two lines contain A-G-B and C-H-D.

If the corresponding angles

  angle EGB  and  angle GHD

are congruent, then AB is parallel to CD.

This is a neutral theorem. The corresponding-angle hypothesis is
converted into equal alternate interior angles using vertical angles,
and Euclid I.27 is then applied.
-/
theorem euclid_proposition_28_corresponding
    (A B C D E G H : Geo.Point)
    (trans : Geo.Line)
    (hAGB : Geo.Between A G B)
    (hCHD : Geo.Between C H D)
    (hEGH : Geo.Between E G H)
    (hGH : Not (G = H))
    (hGtrans : HilbertIncidence.OnLine G trans)
    (hHtrans : HilbertIncidence.OnLine H trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hAGH : Not (Collinear Geo A G H))
    (hCorresponding :
      Geo.AngleCongruent E G B G H D) :
    Geo.Parallel A B C D := by

  have hHGE : Geo.Between H G E :=
    (HilbertOrder.between_incidence
      E G H hEGH).2.2.2.2

  have hVertical :
      Geo.AngleCongruent A G H B G E :=
    VerticalAngles
      Geo
      A G H B E
      hAGB
      hHGE
      hAGH

  have hVertical' :
      Geo.AngleCongruent A G H E G B :=
    (Geo.angle_congruent_reverse_second
      A G H B G E).mp hVertical

  have hAlternate :
      Geo.AngleCongruent A G H G H D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A G H
      E G B
      G H D
      hVertical'
      hCorresponding

  exact
    euclid_proposition_27_transversal
      Geo
      A B C D G H
      trans
      hAGB
      hCHD
      hGH
      hGtrans
      hHtrans
      hOpposite
      hAlternate

/--
Euclid I.28, same-side interior-angle criterion.

The hypothesis that angle BGH and angle GHD are together equal
to two right angles is represented synthetically by requiring
angle GHD to be congruent to angle AGH, where A-G-B.

Thus the supplementary configuration corresponding to Euclid I.13
is built directly into the hypothesis. The conclusion then follows
from Euclid I.27.
-/
theorem euclid_proposition_28_same_side
    (A B C D G H : Geo.Point)
    (trans : Geo.Line)
    (hCHD : Geo.Between C H D)
    (hGH : Not (G = H))
    (hGtrans : HilbertIncidence.OnLine G trans)
    (hHtrans : HilbertIncidence.OnLine H trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hTwoRight :
      HilbertAnglesEqualTwoRightAnglesWithSupplement
        Geo G H D H G B A) :
    Geo.Parallel A B C D := by

  rcases hTwoRight with
    ⟨hBGA, hGHD_HGA⟩

  have hAGB : Geo.Between A G B :=
    (HilbertOrder.between_incidence
      B G A hBGA).2.2.2.2

  have hHGA_GHD :
      Geo.AngleCongruent H G A G H D :=
    Geo.angle_congruent_symmetry
      G H D
      H G A
      hGHD_HGA

  have hAlternate :
      Geo.AngleCongruent A G H G H D :=
    (Geo.angle_congruent_reverse_first
      H G A G H D).mp
      hHGA_GHD

  exact
    euclid_proposition_27_transversal
      Geo
      A B C D G H
      trans
      hAGB
      hCHD
      hGH
      hGtrans
      hHtrans
      hOpposite
      hAlternate

end Geometry

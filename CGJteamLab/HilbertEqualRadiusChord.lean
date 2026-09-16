import CGJteamLab.Proposition24

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Equal-radius chord comparison

This module contains dimension-free lemmas relating proper angles to
their opposite chords when the two pairs of radial sides are congruent.

No numerical angle measure is used.
-/

/--
For two proper angles with pairwise congruent radial sides,
congruent included angles have congruent opposite chords.

Triangles OAB and PCD satisfy

    OA ~= PC,
    OB ~= PD,
    angle AOB ~= angle CPD,

hence SAS gives

    AB ~= CD.
-/
theorem hilbert_equalRadiusChord_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B P C D : Geo.Point)
    (hOAB : Not (PrimCollinear Geo O A B))
    (hPCD : Not (PrimCollinear Geo P C D))
    (hOA_PC : Geo.Congruent O A P C)
    (hOB_PD : Geo.Congruent O B P D)
    (hAngle :
      Geo.AngleCongruent A O B C P D) :
    Geo.Congruent A B C D := by

  have hSAS :=
    SAS
      (Geo := Geo)
      O A B
      P C D
      hOAB
      hPCD
      hOA_PC
      hAngle
      hOB_PD

  exact hSAS.sideBC


/--
For two proper angles with pairwise congruent radial sides,
a strictly smaller included angle has a strictly shorter opposite chord.

If

    angle AOB < angle CPD,

while

    OA ~= PC,
    OB ~= PD,

then Euclid I.24 gives

    AB < CD.
-/
theorem hilbert_equalRadiusChord_less
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B P C D : Geo.Point)
    (hOAB : Not (PrimCollinear Geo O A B))
    (hPCD : Not (PrimCollinear Geo P C D))
    (hOA_PC : Geo.Congruent O A P C)
    (hOB_PD : Geo.Congruent O B P D)
    (hAngle :
      HilbertAngleLess Geo A O B C P D) :
    HilbertSegmentLess Geo A B C D := by

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      P C
      hOA_PC

  have hPD_OB :
      Geo.Congruent P D O B :=
    hilbert_congruent_symmetry
      Geo
      O B
      P D
      hOB_PD

  exact
    euclid_proposition_24
      (Geo := Geo)
      P C D
      O A B
      hPCD
      hOAB
      hPC_OA
      hPD_OB
      hAngle

end Geometry

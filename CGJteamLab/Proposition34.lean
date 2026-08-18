import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid, Elements, Book I, Proposition 34.

In a parallelogram, the opposite sides and opposite angles
are congruent.
-/
theorem euclid_proposition_34
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    OppositeSidesCongruent Geo A B C D ∧
    OppositeAnglesCongruent Geo A B C D := by

  constructor

  · exact
      ParallelogramOppositeSidesCongruent
        Geo A B C D hParallelogram

  · exact
      ParallelogramOppositeAnglesCongruent
        Geo A B C D hParallelogram

/--
The diagonal AC divides the parallelogram ABCD into two
congruent triangles.
-/
theorem euclid_proposition_34_diagonal
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    TriangleCongruenceResult Geo A B C C D A := by

  have hParallel :
      Geo.Parallel A B C D :=
    hParallelogram.1

  have hAB : A ≠ B :=
    hParallel.1

  have hCD : C ≠ D :=
    hParallel.2.1

  have hABC :
      ¬ Collinear Geo A B C := by
    intro hCol

    rcases hCol with
      ⟨lineAB, hAab, hBab, hCab⟩

    rcases HilbertPlaneIncidence.line_through
        C D hCD with
      ⟨lineCD, hCcd, hDcd⟩

    have hC_AB :
        C ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B C lineAB
        hAB hAab hBab).mpr hCab

    have hC_CD :
        C ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D C lineCD
        hCD hCcd hDcd).mpr hCcd

    exact
      Set.disjoint_left.mp hParallel.2.2
        hC_AB hC_CD

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hParallelogram

  have hAC_CA :
      Geo.Congruent A C C A :=
    CongruentSwapSecond
      Geo A C A C
      (hilbert_congruent_reflexive Geo A C)

  have hSSS :=
    HilbertSSS
      Geo
      A B C
      C D A
      hABC
      hSides.1
      hSides.2
      hAC_CA

  exact hSSS.2

end Geometry

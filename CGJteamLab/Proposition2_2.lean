import CGJteamLab.Proposition2_1

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid II.2, for an instantiated rectangular cut diagram.

If B-M-C, then the sum of any rectangles contained by

  BC, BM
  BC, MC

is scissors-equal to the square on BC.
-/
theorem euclid_proposition_2_2
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (B C D E L M X : Geo.Point)

    -- Square on BC.
    (hSquare : IsSquare Geo B C E D)

    -- Cut of the square at M-L.
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDXC : Geo.Between D X C)
    (hMXL : Geo.Between M X L)
    (hLeftPar :
      IsParallelogram Geo L D B M)
    (hRightPar :
      IsParallelogram Geo C E L M)

    -- Arbitrary representatives of the two rectangles in Euclid's
    -- order: whole side first, part second.
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)

    (hPart1 :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 B C B M)

    (hPart2 :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 B C M C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3)
      (hilbertParallelogramTerm Geo B C E D) := by

  --------------------------------------------------------------------
  -- The square is Rect(BC, BC).
  --------------------------------------------------------------------

  have hSquareContained :
      IsRectangleContainedBy Geo
        B C E D B C B C :=
    square_is_rectangle_contained_by_side
      Geo B C E D hSquare

  have hRect :
      IsRectangle Geo B C E D :=
    hSquareContained.1

  have hCE_BC :
      Geo.Congruent C E B C :=
    hSquareContained.2.2

  --------------------------------------------------------------------
  -- Euclid writes the two rectangles as
  --
  --   Rect(BC, BM), Rect(BC, MC),
  --
  -- whereas the cut theorem uses
  --
  --   Rect(BM, BC), Rect(MC, BC).
  --
  -- Rotate the representatives.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_swap
        Geo
        V0 V1 V2 V3
        B C B M
        hPart1 with
    ⟨hPart1Swap, hRotate1⟩

  rcases
      rectangle_contained_by_swap
        Geo
        W0 W1 W2 W3
        B C M C
        hPart2 with
    ⟨hPart2Swap, hRotate2⟩

  --------------------------------------------------------------------
  -- Apply the binary form of II.1 with the fixed segment PQ = BC.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo V1 V2 V3 V0 +
         hilbertParallelogramTerm Geo W1 W2 W3 W0) :=
    euclid_proposition_2_1_two
      Geo
      B C D E L M X
      B C
      hRect
      hCE_BC
      hBMC
      hDLE
      hDXC
      hMXL
      hLeftPar
      hRightPar
      B C E D
      V1 V2 V3 V0
      W1 W2 W3 W0
      hSquareContained
      hPart1Swap
      hPart2Swap

  --------------------------------------------------------------------
  -- Return from the rotated representatives to Euclid's original
  -- ordering.
  --------------------------------------------------------------------

  have hPartsBack :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo V1 V2 V3 V0 +
         hilbertParallelogramTerm Geo W1 W2 W3 W0)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.symm
        (Geo := Geo) hRotate1)
      (HilbertScissorsEq.symm
        (Geo := Geo) hRotate2)

  have hSquareToParts :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hSplit
      hPartsBack

  exact
    HilbertScissorsEq.symm
      (Geo := Geo)
      hSquareToParts

end Geometry

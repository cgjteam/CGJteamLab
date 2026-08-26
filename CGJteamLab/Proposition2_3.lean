import CGJteamLab.Proposition2_1

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid II.3.

If B-M-C, then the rectangle contained by BC and MC equals
the rectangle contained by BM and MC together with the square on MC.

This is the binary form of II.1 with the fixed segment chosen to be MC.
-/
theorem euclid_proposition_2_3
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    -- Concrete cut diagram for Rect(BC, MC).
    (B C D E L M X : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hCE_MC : Geo.Congruent C E M C)

    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDXC : Geo.Between D X C)
    (hMXL : Geo.Between M X L)
    (hLeftPar :
      IsParallelogram Geo L D B M)
    (hRightPar :
      IsParallelogram Geo C E L M)

    -- Square on MC.
    (F G : Geo.Point)
    (hSquare : IsSquare Geo M C F G)

    -- Arbitrary representatives of:
    --
    --   Rect(BC, MC)
    --   Rect(BM, MC).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 B C M C)

    (hProduct :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 B M M C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo M C F G) := by

  --------------------------------------------------------------------
  -- The square on MC is a representative of Rect(MC, MC).
  --------------------------------------------------------------------

  have hSquareContained :
      IsRectangleContainedBy Geo
        M C F G M C M C :=
    square_is_rectangle_contained_by_side
      Geo M C F G hSquare

  --------------------------------------------------------------------
  -- II.1 with fixed segment PQ = MC:
  --
  --   Rect(BC, MC)
  --     =
  --   Rect(BM, MC) + Rect(MC, MC).
  --------------------------------------------------------------------

  exact
    euclid_proposition_2_1_two
      Geo
      B C D E L M X
      M C
      hRect
      hCE_MC
      hBMC
      hDLE
      hDXC
      hMXL
      hLeftPar
      hRightPar
      U0 U1 U2 U3
      V0 V1 V2 V3
      M C F G
      hWhole
      hProduct
      hSquareContained

end Geometry

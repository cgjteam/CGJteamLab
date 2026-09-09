import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.16, reconstructed in Wyler-style flat language.

Let `pi` and `rho` be parallel planes, and let a third plane `sigma`
meet both of them. A point `A` in `pi` and `sigma`, and a point `B`
in `rho` and `sigma`, determine the two section lines.

The proof first identifies the two sections by exact meet identities

    carrier(pi) intersect carrier(sigma) = carrier(l),
    carrier(rho) intersect carrier(sigma) = carrier(m),

and then proves that the two section lines are parallel. The argument
is purely incidence-theoretic: no order, congruence, perpendicularity,
or Euclidean parallel uniqueness is used.
-/
theorem euclid_proposition_11_16_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho sigma : S.Plane)
    (A B : Geo.Point)
    (hPlanesParallel :
      HilbertSpacePlanesParallel Geo pi rho)
    (hApi : S.OnPlane A pi)
    (hAsigma : S.OnPlane A sigma)
    (hBrho : S.OnPlane B rho)
    (hBsigma : S.OnPlane B sigma) :
    exists l m : Geo.Line,
      H.OnLine A l /\
      H.OnLine B m /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo sigma) =
        HilbertLineCarrier3D Geo l /\
      Set.inter
          (HilbertPlaneCarrier3D Geo rho)
          (HilbertPlaneCarrier3D Geo sigma) =
        HilbertLineCarrier3D Geo m /\
      HilbertSpaceLinesParallel Geo l m := by

  ----------------------------------------------------------------------
  -- The cutting plane sigma is distinct from pi.
  ----------------------------------------------------------------------

  have hPiSigma : Ne pi sigma := by
    intro hEq
    apply hPlanesParallel
    refine Exists.intro B ?_
    constructor
    case left =>
      rw [hEq]
      exact hBsigma
    case right =>
      exact hBrho

  ----------------------------------------------------------------------
  -- Likewise sigma is distinct from rho.
  ----------------------------------------------------------------------

  have hRhoSigma : Ne rho sigma := by
    intro hEq
    apply hPlanesParallel
    refine Exists.intro A ?_
    constructor
    case left =>
      exact hApi
    case right =>
      rw [hEq]
      exact hAsigma

  ----------------------------------------------------------------------
  -- First exact section:
  --
  -- carrier(pi) intersect carrier(sigma) = carrier(l).
  ----------------------------------------------------------------------

  cases
      hilbertPlaneCarrier3D_inter_eq_lineCarrier
        (Geo := Geo)
        pi sigma
        hPiSigma
        A hApi hAsigma with
  | intro l hLData =>
      have hAl : H.OnLine A l :=
        hLData.1

      have hlpi : HilbertLineInPlane Geo l pi :=
        hLData.2.1

      have hlsigma : HilbertLineInPlane Geo l sigma :=
        hLData.2.2.1

      have hMeetPiSigma :
          Set.inter
              (HilbertPlaneCarrier3D Geo pi)
              (HilbertPlaneCarrier3D Geo sigma) =
            HilbertLineCarrier3D Geo l :=
        hLData.2.2.2

      ------------------------------------------------------------------
      -- Second exact section:
      --
      -- carrier(rho) intersect carrier(sigma) = carrier(m).
      ------------------------------------------------------------------

      cases
          hilbertPlaneCarrier3D_inter_eq_lineCarrier
            (Geo := Geo)
            rho sigma
            hRhoSigma
            B hBrho hBsigma with
      | intro m hMData =>
          have hBm : H.OnLine B m :=
            hMData.1

          have hmrho : HilbertLineInPlane Geo m rho :=
            hMData.2.1

          have hmsigma : HilbertLineInPlane Geo m sigma :=
            hMData.2.2.1

          have hMeetRhoSigma :
              Set.inter
                  (HilbertPlaneCarrier3D Geo rho)
                  (HilbertPlaneCarrier3D Geo sigma) =
                HilbertLineCarrier3D Geo m :=
            hMData.2.2.2

          --------------------------------------------------------------
          -- Both section lines lie in sigma. It remains to prove that
          -- they have no common point.
          --------------------------------------------------------------

          have hDisjoint :
              HilbertLinesDisjoint Geo l m := by

            intro hMeet

            cases hMeet with
            | intro P hPData =>
                have hPl : H.OnLine P l :=
                  hPData.1

                have hPm : H.OnLine P m :=
                  hPData.2

                apply hPlanesParallel
                refine Exists.intro P ?_
                exact
                  And.intro
                    (hlpi P hPl)
                    (hmrho P hPm)

          have hParallel :
              HilbertSpaceLinesParallel Geo l m := by

            refine Exists.intro sigma ?_
            exact
              And.intro hlsigma
                (And.intro hmsigma hDisjoint)

          exact
            Exists.intro l
              (Exists.intro m
                (And.intro hAl
                  (And.intro hBm
                    (And.intro hMeetPiSigma
                      (And.intro hMeetRhoSigma hParallel)))))

end Geometry

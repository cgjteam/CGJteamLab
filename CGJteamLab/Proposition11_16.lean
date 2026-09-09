import CGJteamLab.Hilbert3DParallel

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.16 in pure synthetic incidence form.

If two parallel planes pi and rho are cut by a third plane sigma,
then the two section lines in sigma are parallel.

The two section lines are characterized pointwise:
a point lies on the section line iff it lies in both relevant planes.

No Wyler module, flat/span/join/meet calculus, order, congruence,
metric, coordinates, or segment arithmetic is used.
-/
theorem euclid_proposition_11_16
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho sigma : S.Plane)
    (A B : Geo.Point)
    (hPlanesParallel :
      HilbertSpacePlanesParallelIncidence Geo pi rho)
    (hApi : S.OnPlane A pi)
    (hAsigma : S.OnPlane A sigma)
    (hBrho : S.OnPlane B rho)
    (hBsigma : S.OnPlane B sigma) :
    exists l m : Geo.Line,
      H.OnLine A l /\
      H.OnLine B m /\
      (forall X : Geo.Point,
        (S.OnPlane X pi /\ S.OnPlane X sigma) <->
        H.OnLine X l) /\
      (forall X : Geo.Point,
        (S.OnPlane X rho /\ S.OnPlane X sigma) <->
        H.OnLine X m) /\
      HilbertSpaceLinesParallel Geo l m := by

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

  cases
      hilbert_plane_intersection_line
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

      have hLIff :
          forall X : Geo.Point,
            (S.OnPlane X pi /\ S.OnPlane X sigma) <->
            H.OnLine X l :=
        hLData.2.2.2

      cases
          hilbert_plane_intersection_line
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

          have hMIff :
              forall X : Geo.Point,
                (S.OnPlane X rho /\ S.OnPlane X sigma) <->
                H.OnLine X m :=
            hMData.2.2.2

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
                    (And.intro hLIff
                      (And.intro hMIff hParallel)))))

end Geometry

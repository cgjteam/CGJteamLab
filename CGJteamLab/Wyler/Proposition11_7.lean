import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.7.

If two straight lines are parallel and arbitrary points are chosen on
them, then the straight line joining those points lies in the same plane
as the parallel lines.

The flat core is more general than parallelism:

  E in l, F in m
  ----------------
  Span{E,F} subset Join(l,m).

Parallelism is used only to identify `Join(l,m)` with the common carrier
plane and to guarantee `E != F`, so that `Span{E,F}` is a line carrier.
-/
theorem euclid_proposition_11_7
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (E F : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hEl : H.OnLine E l)
    (hFm : H.OnLine F m) :
    exists sigma : S.Plane,
      HilbertLineInPlane Geo l sigma /\
      HilbertLineInPlane Geo m sigma /\
      exists n : Geo.Line,
        H.OnLine E n /\
        H.OnLine F n /\
        HilbertLineInPlane Geo n sigma := by

  cases hParallel with
  | intro sigma hSigma =>
      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigma.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigma.2.1

      have hDisjoint :
          HilbertLinesDisjoint Geo l m :=
        hSigma.2.2

      /-
      Parallel lines are distinct, hence their common plane is exactly
      their join.
      -/
      have hlm : Ne l m := by
        intro hEq

        have hEm : H.OnLine E m := by
          simpa [hEq] using hEl

        exact
          hDisjoint
            (Exists.intro E
              (And.intro hEl hEm))

      have hJoin :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo sigma :=
        hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
          (Geo := Geo)
          sigma l m
          hlm
          hlsigma
          hmsigma

      /-
      E and F are distinct because otherwise the parallel carriers
      would meet.
      -/
      have hEF : Ne E F := by
        intro hEq
        subst F

        exact
          hDisjoint
            (Exists.intro E
              (And.intro hEl hFm))

      /-
      Construct the connector line n = EF.
      -/
      cases
          HilbertPlaneIncidence.line_through
            E F hEF with
      | intro n hN =>
          have hEn : H.OnLine E n :=
            hN.1

          have hFn : H.OnLine F n :=
            hN.2

          /-
          The connector is exactly the rank-one span of its endpoints.
          -/
          have hSpanN :
              HilbertSpan3D Geo ({E, F} : Set Geo.Point) =
                HilbertLineCarrier3D Geo n :=
            hilbertSpan3D_pair_eq_lineCarrier
              (Geo := Geo)
              E F n
              hEF
              hEn hFn

          /-
          Generic connector monotonicity:
              Span{E,F} subset Join(l,m).
          -/
          have hPairSubsetJoin :
              Set.Subset
                (HilbertSpan3D Geo ({E, F} : Set Geo.Point))
                (HilbertJoin3D Geo
                  (HilbertLineCarrier3D Geo l)
                  (HilbertLineCarrier3D Geo m)) :=
            hilbertSpan3D_pair_subset_join_of_mem_lines
              (Geo := Geo)
              l m E F
              hEl hFm

          /-
          Rewrite span and join by their geometric carriers.
          -/
          have hnsigma :
              HilbertLineInPlane Geo n sigma := by
            intro X hXn

            have hXSpan :
                HilbertSpan3D Geo ({E, F} : Set Geo.Point) X := by
              rw [hSpanN]
              exact hXn

            have hXJoin :=
              hPairSubsetJoin hXSpan

            rw [hJoin] at hXJoin
            exact hXJoin

          exact
            Exists.intro sigma
              (And.intro hlsigma
                (And.intro hmsigma
                  (Exists.intro n
                    (And.intro hEn
                      (And.intro hFn hnsigma)))))

end Geometry

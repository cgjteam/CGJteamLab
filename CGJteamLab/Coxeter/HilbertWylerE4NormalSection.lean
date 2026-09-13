import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneIntersection
import CGJteamLab.HilbertWylerE4HilbertLayers
import CGJteamLab.Coxeter.E4NormalSection

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal sections on the Hilbert-Wyler foundation

For two distinct derived E4 hyperplanes meeting exactly in an ambient
2-plane `Delta`, and a point `O` of `Delta`, the local three-dimensional
Hilbert geometry inside each hyperplane produces the two lines normal to
`Delta` at `O`. These two lines determine an ambient 2-plane: the normal
section of the pair.

Public foundation:

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension
    + Hilbert4DAmbientOrder
    + Hilbert4DAmbientCongruence
    + Hilbert4DAmbientEuclidean.

Historical E4 incidence interfaces are supplied by
`HilbertWylerE4PublicInstances`.
-/

/--
For two derived E4 hyperplanes meeting exactly in `Delta`, and a point
`O` of `Delta`, there are distinct local normals `s` and `t` at `O`
which lie in one ambient 2-plane `N`.
-/
theorem hilbertWyler_e4_hyperplane_pair_normal_section_exists
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta) :
    exists s : HyperplaneLine4 Geo Sigma,
      exists t : HyperplaneLine4 Geo Tau,
        HilbertLinePerpendicularPlaneAt
            (HyperplaneGeo4 Geo Sigma)
            s
            (Subtype.mk Delta
              (by
                unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.1))
            (Subtype.mk O
              (by
                unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.1 O hODelta)) /\
        HilbertLinePerpendicularPlaneAt
            (HyperplaneGeo4 Geo Tau)
            t
            (Subtype.mk Delta
              (by
                unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.2.1))
            (Subtype.mk O
              (by
                unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.2.1 O hODelta)) /\
        Ne s.1 t.1 /\
        exists N : S.Plane,
          S.OnPlane O N /\
          HilbertLineInPlane Geo s.1 N /\
          HilbertLineInPlane Geo t.1 N := by

  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_hyperplane_pair_normal_section_exists_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta


/--
The normal section can be chosen with exact traces:

    N cap Sigma = s,
    N cap Tau   = t.

Thus the two local mirror lines in the normal section are exactly the
intersections with the two ambient reflecting hyperplanes.
-/
theorem hilbertWyler_e4_hyperplane_pair_normal_section_exact_traces
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta : S.OnPlane O Delta) :
    exists s : HyperplaneLine4 Geo Sigma,
      exists t : HyperplaneLine4 Geo Tau,
        exists N : S.Plane,
          HilbertLinePerpendicularPlaneAt
              (HyperplaneGeo4 Geo Sigma)
              s
              (Subtype.mk Delta
                (by
                  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.1))
              (Subtype.mk O
                (by
                  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.1 O hODelta)) /\
          HilbertLinePerpendicularPlaneAt
              (HyperplaneGeo4 Geo Tau)
              t
              (Subtype.mk Delta
                (by
                  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.2.1))
              (Subtype.mk O
                (by
                  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.2.1 O hODelta)) /\
          Ne s.1 t.1 /\
          S.OnPlane O N /\
          HilbertLineInPlane Geo s.1 N /\
          HilbertLineInPlane Geo t.1 N /\
          Not (HilbertPlaneInHyperplane4 Geo N Sigma) /\
          Not (HilbertPlaneInHyperplane4 Geo N Tau) /\
          (forall X : Geo.Point,
            (S.OnPlane X N /\
             E4OnHyperplane Geo X Sigma) <->
              H.OnLine X s.1) /\
          (forall X : Geo.Point,
            (S.OnPlane X N /\
             E4OnHyperplane Geo X Tau) <->
              H.OnLine X t.1) := by

  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_hyperplane_pair_normal_section_exact_traces_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta

end Geometry

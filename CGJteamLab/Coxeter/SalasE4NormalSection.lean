import CGJteamLab.Coxeter.SalasE4HyperplaneIntersection
import CGJteamLab.Coxeter.SalasE4HilbertLayers
import CGJteamLab.Coxeter.E4NormalSection

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal sections on the Salas foundation

For two distinct derived E4 hyperplanes meeting exactly in an ambient
2-plane `Delta`, and a point `O` of `Delta`, the local three-dimensional
Hilbert geometry inside each hyperplane produces the two lines normal to
`Delta` at `O`.  These two lines determine an ambient 2-plane: the normal
section of the pair.

Public foundation:

    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

All historical E4 incidence interfaces are derived locally.
-/

@[instance_reducible]
local instance salasE4Primitive_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_normalSection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


/--
For two derived E4 hyperplanes meeting exactly in `Delta`, and a point
`O` of `Delta`, there are distinct local normals `s` and `t` at `O`
which lie in one ambient 2-plane `N`.
-/
theorem salas_e4_hyperplane_pair_normal_section_exists
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
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
                unfold SalasE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.1))
            (Subtype.mk O
              (by
                unfold SalasE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.1 O hODelta)) /\
        HilbertLinePerpendicularPlaneAt
            (HyperplaneGeo4 Geo Tau)
            t
            (Subtype.mk Delta
              (by
                unfold SalasE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.2.1))
            (Subtype.mk O
              (by
                unfold SalasE4HyperplanesMeetInPlane at hMeet
                exact hMeet.2.2.1 O hODelta)) /\
        Ne s.1 t.1 /\
        exists N : S.Plane,
          S.OnPlane O N /\
          HilbertLineInPlane Geo s.1 N /\
          HilbertLineInPlane Geo t.1 N := by

  unfold SalasE4HyperplanesMeetInPlane at hMeet

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
theorem salas_e4_hyperplane_pair_normal_section_exact_traces
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
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
                  unfold SalasE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.1))
              (Subtype.mk O
                (by
                  unfold SalasE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.1 O hODelta)) /\
          HilbertLinePerpendicularPlaneAt
              (HyperplaneGeo4 Geo Tau)
              t
              (Subtype.mk Delta
                (by
                  unfold SalasE4HyperplanesMeetInPlane at hMeet
                  exact hMeet.2.2.1))
              (Subtype.mk O
                (by
                  unfold SalasE4HyperplanesMeetInPlane at hMeet
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

  unfold SalasE4HyperplanesMeetInPlane at hMeet

  exact
    hilbert4D_hyperplane_pair_normal_section_exact_traces_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta

end Geometry

-- SalasE4HyperplaneReflectionLineTransport FIX2 - 2026-09-11
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionIncidence
import CGJteamLab.Coxeter.E4HyperplaneReflectionLineTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane line transport on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional metric/order assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

The historical E4 classes are installed only as local compatibility
instances.  The public definitions below are stated directly for
`E4Hyperplane`.
-/

@[instance_reducible]
local instance salasE4Primitive_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_lineTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo] :
    Hilbert4DNormalFromExternalPointExistence_corrected Geo :=
  hilbert4D_XI11_implies_normalFromExternalPointExistence_corrected
    (Geo := Geo)


/--
Exact setwise transport of a line by the Salas-based E4 hyperplane
reflection.
-/
def SalasE4HyperplaneReflectionMapsLine
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line) : Prop :=
  HyperplaneReflectionMapsLine4_corrected
    Geo Sigma source target


/--
Two reflected images of distinct source points determine the exact image
line.
-/
theorem salasE4HyperplaneReflectionMapsLine_of_two_points
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hAs : H.OnLine A source)
    (hBs : H.OnLine B source)
    (hA't :
      H.OnLine
        (salasE4HyperplaneReflect (Geo := Geo) Sigma A)
        target)
    (hB't :
      H.OnLine
        (salasE4HyperplaneReflect (Geo := Geo) Sigma B)
        target) :
    SalasE4HyperplaneReflectionMapsLine
      Geo Sigma source target := by

  unfold SalasE4HyperplaneReflectionMapsLine
  unfold salasE4HyperplaneReflect at hA't hB't

  exact
    hyperplaneReflectionMapsLine4_corrected_of_two_points
      (Geo := Geo)
      Sigma source target
      A B
      hAB hAs hBs
      hA't hB't


/--
Every line has an exact reflected image line.
-/
theorem salasE4HyperplaneReflectionMapsLine_exists
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    exists target : Geo.Line,
      SalasE4HyperplaneReflectionMapsLine
        Geo Sigma source target := by

  unfold SalasE4HyperplaneReflectionMapsLine

  exact
    hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma source


/--
The exact reflected image line is unique.
-/
theorem salasE4HyperplaneReflectionMapsLine_unique
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target1 target2 : Geo.Line)
    (hMap1 :
      SalasE4HyperplaneReflectionMapsLine
        Geo Sigma source target1)
    (hMap2 :
      SalasE4HyperplaneReflectionMapsLine
        Geo Sigma source target2) :
    target1 = target2 := by

  unfold SalasE4HyperplaneReflectionMapsLine at hMap1 hMap2

  exact
    hyperplaneReflectionMapsLine4_corrected_unique
      (Geo := Geo)
      Sigma source target1 target2
      hMap1 hMap2


/--
Canonical reflected image of a line.
-/
noncomputable def salasE4HyperplaneReflectionLineCarrier
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    Geo.Line :=
  hyperplaneReflectionLineCarrier4_corrected
    (Geo := Geo)
    Sigma source


/--
Specification of the canonical reflected line.
-/
theorem salasE4HyperplaneReflectionLineCarrier_spec
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    SalasE4HyperplaneReflectionMapsLine
      Geo Sigma source
      (salasE4HyperplaneReflectionLineCarrier
        (Geo := Geo) Sigma source) := by

  unfold SalasE4HyperplaneReflectionMapsLine
  unfold salasE4HyperplaneReflectionLineCarrier

  exact
    hyperplaneReflectionLineCarrier4_corrected_spec
      (Geo := Geo)
      Sigma source


/--
Pointwise membership characterization of the canonical reflected line.
-/
theorem salasE4HyperplaneReflectionLineCarrier_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line)
    (P : Geo.Point) :
    H.OnLine P source <->
      H.OnLine
        (salasE4HyperplaneReflect (Geo := Geo) Sigma P)
        (salasE4HyperplaneReflectionLineCarrier
          (Geo := Geo) Sigma source) :=
  salasE4HyperplaneReflectionLineCarrier_spec
    (Geo := Geo)
    Sigma source P


/--
Any exact target is the canonical reflected line.
-/
theorem salasE4HyperplaneReflectionLineCarrier_eq
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line)
    (hMap :
      SalasE4HyperplaneReflectionMapsLine
        Geo Sigma source target) :
    salasE4HyperplaneReflectionLineCarrier
        (Geo := Geo) Sigma source =
      target := by

  apply
    salasE4HyperplaneReflectionMapsLine_unique
      (Geo := Geo)
      Sigma source
      (salasE4HyperplaneReflectionLineCarrier
        (Geo := Geo) Sigma source)
      target

  · exact
      salasE4HyperplaneReflectionLineCarrier_spec
        (Geo := Geo)
        Sigma source

  · exact hMap


/--
Exact line transport reverses under the same reflection.
-/
theorem salasE4HyperplaneReflectionMapsLine_symm
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line)
    (hMap :
      SalasE4HyperplaneReflectionMapsLine
        Geo Sigma source target) :
    SalasE4HyperplaneReflectionMapsLine
      Geo Sigma target source := by

  unfold SalasE4HyperplaneReflectionMapsLine at hMap |- 

  exact
    hyperplaneReflectionMapsLine4_corrected_symm
      (Geo := Geo)
      Sigma source target hMap


/--
Canonical line transport is involutive.
-/
theorem salasE4HyperplaneReflectionLineCarrier_involutive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    salasE4HyperplaneReflectionLineCarrier
        (Geo := Geo)
        Sigma
        (salasE4HyperplaneReflectionLineCarrier
          (Geo := Geo) Sigma source) =
      source := by

  unfold salasE4HyperplaneReflectionLineCarrier

  exact
    hyperplaneReflectionLineCarrier4_corrected_involutive
      (Geo := Geo)
      Sigma source

end Geometry

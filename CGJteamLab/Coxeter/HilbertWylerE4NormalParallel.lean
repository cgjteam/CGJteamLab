import CGJteamLab.Coxeter.HilbertWylerE4NormalSection
import CGJteamLab.Coxeter.E4NormalParallel

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal parallelism on the Hilbert-Wyler foundation

Pure incidence results require the Hilbert-Wyler incidence foundation
and `E4Dimension`.

The final XI.6-style parallelism theorem additionally requires ambient
Hilbert Groups II and III. No ambient Group IV assumption is needed.
-/

/--
Inside a derived E4 hyperplane every ambient 2-plane misses at least one
point of the hyperplane.
-/
theorem hilbertWyler_e4_hyperplane_point_off_plane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    (Sigma : E4Hyperplane Geo)
    (rho : S.Plane) :
    exists D : Geo.Point,
      E4OnHyperplane Geo D Sigma /\
      Not (S.OnPlane D rho) := by

  exact
    hilbert4D_hyperplane_point_off_plane_corrected
      (Geo := Geo)
      Sigma rho


/--
Two normals to one derived E4 hyperplane at distinct feet lie in one
derived E4 hyperplane.
-/
theorem hilbertWyler_e4_distinct_foot_normals_common_hyperplane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    (Sigma : E4Hyperplane Geo)
    (l m : Geo.Line)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G) :
    exists Lambda : E4Hyperplane Geo,
      HilbertLineInHyperplane4 Geo l Lambda /\
      HilbertLineInHyperplane4 Geo m Lambda := by

  exact
    hilbert4D_distinct_foot_normals_common_hyperplane_corrected
      (Geo := Geo)
      Sigma
      l m
      F G
      hFG
      hLNormal
      hMNormal


/--
Dimension-safe ambient line parallelism in E4: the two lines lie in one
ambient 2-plane and are disjoint.
-/
def HilbertWylerE4LinesParallel
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    (l m : Geo.Line) : Prop :=
  Hilbert4DLinesParallel_corrected Geo l m


/--
Two normals to the same derived E4 hyperplane at distinct feet are
parallel in the dimension-safe ambient E4 sense.
-/
theorem hilbertWyler_e4_normals_to_same_hyperplane_parallel
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (l m : Geo.Line)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G) :
    HilbertWylerE4LinesParallel Geo l m := by

  unfold HilbertWylerE4LinesParallel

  exact
    hilbert4D_normals_to_same_hyperplane_parallel_corrected
      (Geo := Geo)
      Sigma
      l m
      F G
      hFG
      hLNormal
      hMNormal

end Geometry

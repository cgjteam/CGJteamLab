import CGJteamLab.Coxeter.E4NormalParallel

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: isolate the hyperplane version of Euclid XI.4

Tests73-75 repaired the distinct-foot normal parallelism argument
dimension-correctly.

The next step toward a Coxeter normal section exposes one genuinely
four-dimensional orthogonality principle which is not present in the
old Book XI API.

For a 2-plane, Euclid XI.4 says:

  perpendicular to two distinct intersecting directions in the plane
  implies perpendicular to the whole plane.

For a 3-hyperplane in E4, the corresponding statement is:

  perpendicular to three independent directions spanning the
  hyperplane implies perpendicular to the whole hyperplane.

This file isolates exactly that principle and nothing stronger.

In particular, it does NOT assume:

* reflection preserves a normal section;
* existence of a normal at a point of the hyperplane;
* uniqueness of a normal;
* parallelism of normals.

Those are separate statements, and uniqueness/parallelism have already
been derived elsewhere.
-/

/--
Three lines through O form a spanning frame of the E4 hyperplane Sigma
when they lie in Sigma and contain points A,B,C such that
O,A,B,C are not coplanar.

Thus the three line directions genuinely span the local 3-dimensional
hyperplane.
-/
def Hilbert4DHyperplaneFrameAt_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (O : Geo.Point)
    (a b c : Geo.Line) : Prop :=
  HilbertLineInHyperplane4 Geo a Sigma /\
  HilbertLineInHyperplane4 Geo b Sigma /\
  HilbertLineInHyperplane4 Geo c Sigma /\
  H.OnLine O a /\
  H.OnLine O b /\
  H.OnLine O c /\
  exists A B C : Geo.Point,
    H.OnLine A a /\
    H.OnLine B b /\
    H.OnLine C c /\
    Not (HilbertCoplanar4 Geo O A B C)

/--
The corrected E4 hyperplane analogue of Euclid XI.4.

A line l through O which is perpendicular at O to three independent
directions spanning Sigma is perpendicular to the whole hyperplane
Sigma at O.

This is intentionally isolated as a separate boundary.  The current
Book XI library proves the 2-plane version XI.4, but does not yet
contain this dimension-4 extension.
-/
class Hilbert4DHyperplanePerpendicularFrameCriterion_corrected
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo] : Prop where

  normal_of_spanning_frame :
    forall Sigma : Q.Hyperplane,
      forall O : Geo.Point,
        forall l a b c : Geo.Line,
          H.OnLine O l ->
          Hilbert4DHyperplaneFrameAt_corrected
            Geo Sigma O a b c ->
          HilbertLinesPerpendicularAt Geo l a O ->
          HilbertLinesPerpendicularAt Geo l b O ->
          HilbertLinesPerpendicularAt Geo l c O ->
          HilbertLinePerpendicularHyperplaneAt4_corrected
            Geo l Sigma O

/--
Convenience wrapper for the corrected E4 hyperplane XI.4 criterion.
-/
theorem hilbert4D_normal_of_spanning_perpendicular_frame_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo]
    (Sigma : Q.Hyperplane)
    (O : Geo.Point)
    (l a b c : Geo.Line)
    (hOl : H.OnLine O l)
    (hFrame :
      Hilbert4DHyperplaneFrameAt_corrected
        Geo Sigma O a b c)
    (hPerpA :
      HilbertLinesPerpendicularAt Geo l a O)
    (hPerpB :
      HilbertLinesPerpendicularAt Geo l b O)
    (hPerpC :
      HilbertLinesPerpendicularAt Geo l c O) :
    HilbertLinePerpendicularHyperplaneAt4_corrected
      Geo l Sigma O := by

  exact
    Hilbert4DHyperplanePerpendicularFrameCriterion_corrected.normal_of_spanning_frame
      (Geo := Geo)
      Sigma O
      l a b c
      hOl
      hFrame
      hPerpA hPerpB hPerpC

end Geometry

import CGJteamLab.Coxeter.HilbertWylerE4NormalParallel
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.E4ReflectionPlaneInvariance

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Reflection-invariant planes on the Hilbert-Wyler E4 foundation

If an ambient 2-plane `N` contains one normal `r` to a reflecting
hyperplane `Sigma`, then reflection in `Sigma` preserves `N`.

Relational invariance needs the Hilbert-Wyler E4 incidence foundation
plus ambient Groups II and III. The canonical reflection function also
uses the derived XI.11 normal-existence interface, hence Group IV.
-/

/--
Relational plane invariance.

If `N` contains a `Sigma`-normal through `O`, then every reflected image
of a point of `N` again lies in `N`.
-/
theorem hilbertWyler_e4_reflection_relation_preserves_plane_of_normal
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (N : S.Plane)
    (O : Geo.Point)
    (r : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (P P' : Geo.Point)
    (hPN :
      S.OnPlane P N)
    (hRefl :
      IsHyperplaneReflection4_corrected
        Geo Sigma P P') :
    S.OnPlane P' N := by

  exact
    hilbert4D_reflection_relation_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma N O r
      hrN hRNormal
      P P'
      hPN
      hRefl


/--
Functional plane invariance for the canonical Hilbert-Wyler-based
hyperplane reflection.
-/
theorem hilbertWylerE4HyperplaneReflect_preserves_plane_of_normal
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (N : S.Plane)
    (O : Geo.Point)
    (r : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (P : Geo.Point)
    (hPN :
      S.OnPlane P N) :
    S.OnPlane
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P)
      N := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma N O r
      hrN hRNormal
      P hPN

end Geometry

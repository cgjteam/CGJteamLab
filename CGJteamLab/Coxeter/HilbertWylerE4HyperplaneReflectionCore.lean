import CGJteamLab.HilbertWylerE4PublicInstances
import CGJteamLab.Coxeter.E4HyperplaneReflectionCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection core on the Hilbert-Wyler foundation

This module exposes the production hyperplane-reflection core with the
public incidence foundation

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension.

The only additional geometric assumptions are the ambient Hilbert
Groups II-IV:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean.

Historical E4 incidence and normal-existence interfaces are supplied by
`HilbertWylerE4PublicInstances`.

No new axiom is introduced here.
-/

/--
On the Hilbert-Wyler E4 foundation, every point outside a derived
hyperplane has a perpendicular foot on that hyperplane.
-/
theorem hilbertWyler_e4_hyperplane_perpendicular_foot_exists
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point)
    (hPSigma : Not (E4OnHyperplane Geo P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P :=
  hyperplane_perpendicular_foot_exists4_corrected
    (Geo := Geo)
    Sigma P hPSigma

/--
The perpendicular foot is unique.
-/
theorem hilbertWyler_e4_hyperplane_perpendicular_foot_exists_unique
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point)
    (hPSigma : Not (E4OnHyperplane Geo P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P /\
      forall G : Geo.Point,
        PerpendicularToHyperplaneThrough4_corrected
            Geo Sigma G P ->
        G = F :=
  hyperplane_perpendicular_foot_exists_unique4_corrected
    (Geo := Geo)
    Sigma P hPSigma

/--
Every point has a reflected point in a derived E4 hyperplane.
-/
theorem hilbertWyler_e4_hyperplane_reflection_exists
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    exists P' : Geo.Point,
      IsHyperplaneReflection4_corrected
        Geo Sigma P P' :=
  hyperplane_reflection_exists4_corrected
    (Geo := Geo)
    Sigma P

/--
Canonical hyperplane reflection on the Hilbert-Wyler E4 foundation.
-/
noncomputable def hilbertWylerE4HyperplaneReflect
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    Geo.Point :=
  hyperplaneReflect4_corrected
    Geo Sigma P

/--
Specification of the canonical Hilbert-Wyler-based hyperplane reflection.
-/
theorem hilbertWylerE4HyperplaneReflect_spec
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    IsHyperplaneReflection4_corrected
      Geo Sigma P
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P) := by
  unfold hilbertWylerE4HyperplaneReflect
  exact
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma P

/--
The canonical Hilbert-Wyler-based E4 hyperplane reflection is involutive.
-/
theorem hilbertWylerE4HyperplaneReflect_involutive
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma
        (hilbertWylerE4HyperplaneReflect
          (Geo := Geo) Sigma P) =
      P := by
  unfold hilbertWylerE4HyperplaneReflect
  exact
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo)
      Sigma P

end Geometry

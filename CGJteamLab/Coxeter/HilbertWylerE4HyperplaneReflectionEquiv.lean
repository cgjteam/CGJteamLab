import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.E4HyperplaneReflectionEquiv

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection equivalence on the Hilbert-Wyler foundation

This module exposes the production hyperplane-reflection equivalence with
public assumptions

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension
    + Hilbert4DAmbientOrder
    + Hilbert4DAmbientCongruence
    + Hilbert4DAmbientEuclidean.

No new axiom is introduced here.
-/

/--
A point is fixed by the canonical Hilbert-Wyler-based hyperplane
reflection exactly when it lies on the reflecting hyperplane.
-/
theorem hilbertWylerE4HyperplaneReflect_fixed_iff
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
        (Geo := Geo) Sigma P = P <->
      E4OnHyperplane Geo P Sigma := by
  unfold hilbertWylerE4HyperplaneReflect
  exact
    hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      Sigma P

/--
The canonical Hilbert-Wyler-based reflection in an E4 hyperplane,
packaged as an equivalence of the ambient point type.
-/
noncomputable def hilbertWylerE4HyperplaneReflectionEquiv
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo) :
    Equiv Geo.Point Geo.Point where
  toFun :=
    hilbertWylerE4HyperplaneReflect
      (Geo := Geo) Sigma
  invFun :=
    hilbertWylerE4HyperplaneReflect
      (Geo := Geo) Sigma
  left_inv := by
    intro P
    exact
      hilbertWylerE4HyperplaneReflect_involutive
        (Geo := Geo)
        Sigma P
  right_inv := by
    intro P
    exact
      hilbertWylerE4HyperplaneReflect_involutive
        (Geo := Geo)
        Sigma P

/--
The Hilbert-Wyler-based equivalence realizes the corrected relational
reflection.
-/
theorem hilbertWylerE4HyperplaneReflectionEquiv_spec
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
      (hilbertWylerE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma P) := by
  change
    IsHyperplaneReflection4_corrected
      Geo Sigma P
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P)
  exact
    hilbertWylerE4HyperplaneReflect_spec
      (Geo := Geo)
      Sigma P

/--
The Hilbert-Wyler-based reflection equivalence is pointwise involutive.
-/
theorem hilbertWylerE4HyperplaneReflectionEquiv_apply_apply
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
    hilbertWylerE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma
        (hilbertWylerE4HyperplaneReflectionEquiv
          (Geo := Geo) Sigma P) =
      P := by
  change
    hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma
        (hilbertWylerE4HyperplaneReflect
          (Geo := Geo) Sigma P) =
      P
  exact
    hilbertWylerE4HyperplaneReflect_involutive
      (Geo := Geo)
      Sigma P

/--
The fixed points of the Hilbert-Wyler-based equivalence are exactly the
points of the reflecting hyperplane.
-/
theorem hilbertWylerE4HyperplaneReflectionEquiv_fixed_iff
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
    hilbertWylerE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma P = P <->
      E4OnHyperplane Geo P Sigma := by
  change
    hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P = P <->
      E4OnHyperplane Geo P Sigma
  exact
    hilbertWylerE4HyperplaneReflect_fixed_iff
      (Geo := Geo)
      Sigma P

end Geometry

import CGJteamLab.Coxeter.E4HyperplaneReflectionIsometry

namespace Geometry

universe u

/-!
# Dimension-free synthetic isometry carrier

The historical `HilbertSpaceIsometry3D` stores only two pieces of data:

* an equivalence of ambient points;
* preservation of segment congruence from each segment to its image.

Those fields are dimension-independent, but the old structure is
parameterized by the full 3D Hilbert hierarchy.

This file extracts the genuinely dimension-free carrier.

No incidence, order, dimension, plane, hyperplane, or Book XI class is
part of the structure itself.
-/

/--
A dimension-free synthetic isometry carrier.

`preserves_congruence A B` says that the segment AB is congruent to its
image under the point equivalence.
-/
structure HilbertIsometry (Geo : Geometry.Geo) where

  toEquiv : Equiv Geo.Point Geo.Point

  preserves_congruence :
    forall A B : Geo.Point,
      Geo.Congruent
        A B
        (toEquiv A)
        (toEquiv B)


namespace HilbertIsometry

variable {Geo : Geometry.Geo}

/--
The identity point equivalence, provided with a proof that every segment
is congruent to itself.

The congruence proof is supplied explicitly so the carrier itself
remains independent of any particular Hilbert congruence hierarchy.
-/
def refl
    (hRefl :
      forall A B : Geo.Point,
        Geo.Congruent A B A B) :
    HilbertIsometry Geo where

  toEquiv :=
    Equiv.refl Geo.Point

  preserves_congruence := by
    intro A B
    exact hRefl A B


/--
Composition of dimension-free isometry carriers.

The only external ingredient is the exact transitivity rule for segment
congruence needed to compose the two preservation proofs.  Keeping this
rule explicit avoids baking either the plane, old 3D, or corrected E4
congruence hierarchy into `HilbertIsometry`.
-/
def trans
    (hTrans :
      forall A B C D E F : Geo.Point,
        Geo.Congruent A B C D ->
        Geo.Congruent C D E F ->
        Geo.Congruent A B E F)
    (f g : HilbertIsometry Geo) :
    HilbertIsometry Geo where

  toEquiv :=
    f.toEquiv.trans g.toEquiv

  preserves_congruence := by
    intro A B

    exact
      hTrans
        A B
        (f.toEquiv A)
        (f.toEquiv B)
        (g.toEquiv (f.toEquiv A))
        (g.toEquiv (f.toEquiv B))
        (f.preserves_congruence A B)
        (g.preserves_congruence
          (f.toEquiv A)
          (f.toEquiv B))


@[simp]
theorem trans_apply
    (hTrans :
      forall A B C D E F : Geo.Point,
        Geo.Congruent A B C D ->
        Geo.Congruent C D E F ->
        Geo.Congruent A B E F)
    (f g : HilbertIsometry Geo)
    (P : Geo.Point) :
    (trans hTrans f g).toEquiv P =
      g.toEquiv (f.toEquiv P) := by

  rfl

end HilbertIsometry


/-!
## Corrected E4 reflection packaged in the dimension-free carrier
-/

/--
The corrected E4 hyperplane reflection as a dimension-free synthetic
isometry.
-/
noncomputable def hyperplaneReflectionHilbertIsometry4_corrected
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane) :
    HilbertIsometry Geo where

  toEquiv :=
    hyperplaneReflectionEquiv4_corrected
      Geo Sigma

  preserves_congruence := by
    intro A B

    exact
      hyperplaneReflect4_corrected_preserves_congruence
        (Geo := Geo)
        Sigma A B


@[simp]
theorem hyperplaneReflectionHilbertIsometry4_corrected_apply
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    (hyperplaneReflectionHilbertIsometry4_corrected
      Geo Sigma).toEquiv P =
      hyperplaneReflect4_corrected Geo Sigma P := by

  rfl


/--
Corrected ambient E4 segment-congruence transitivity in the exact form
needed by `HilbertIsometry.trans`.
-/
theorem hilbert4D_ambient_congruent_transitive_corrected
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (A B C D E F : Geo.Point)
    (h1 : Geo.Congruent A B C D)
    (h2 : Geo.Congruent C D E F) :
    Geo.Congruent A B E F := by

  have h1sym :
      Geo.Congruent C D A B :=
    hilbert4D_ambient_congruent_symm_corrected
      (Geo := Geo)
      A B C D h1

  exact
    H4C.segment_congruence_common
      C D
      A B
      E F
      h1sym h2


/--
Composition specialized to the corrected E4 congruence layer.
-/
def HilbertIsometry.trans4_corrected
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (f g : HilbertIsometry Geo) :
    HilbertIsometry Geo :=

  HilbertIsometry.trans
    (hilbert4D_ambient_congruent_transitive_corrected
      (Geo := Geo))
    f g


@[simp]
theorem HilbertIsometry.trans4_corrected_apply
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (f g : HilbertIsometry Geo)
    (P : Geo.Point) :
    (HilbertIsometry.trans4_corrected
      Geo f g).toEquiv P =
      g.toEquiv (f.toEquiv P) := by

  rfl

end Geometry

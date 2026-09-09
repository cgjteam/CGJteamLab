import CGJteamLab.Coxeter.E4Incidence
import CGJteamLab.Coxeter.E4HyperplaneReflectionHyperplaneTransport
import CGJteamLab.Coxeter.E4AmbientTriangleSSS
import CGJteamLab.Coxeter.E4HyperplaneReflectionLineTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionOrderTransport

/-!
# Coxeter A4 on the corrected dimension-free E4 Smith/Wyler stack

Production consolidation of the corrected A4 construction.

The four generators are reflections in the perpendicular-bisector
hyperplanes of AB, BC, CD, and DE in a five-vertex E4 simplex frame.
The final API proves, as equalities of ambient point equivalences,

  r_i^2 = 1,

  r1 r2 r1 = r2 r1 r2,
  r2 r3 r2 = r3 r2 r3,
  r3 r4 r3 = r4 r3 r4,

  r1 r3 = r3 r1,
  r1 r4 = r4 r1,
  r2 r4 = r4 r2.

No ambient `HilbertSpaceIncidence Geo` and no finite-anchor rigidity
principle are used.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 restart on the dimension-free Smith/Wyler E4 base

The old A4 experiment reached a five-vertex mirror frame, but its
ambient class hierarchy accidentally inherited the genuinely 3D
`HilbertSpaceIncidence Geo` package.  That made four-anchor rigidity
available in the intended E4 ambient space.

This restart keeps the validated corrected hyperplane-reflection
machinery, but replaces the ambient incidence base by

  HilbertDimensionFreeIncidence
  + Hilbert4DHyperplaneIncidenceCore.

The compatibility instance from `AffineFlat4D_refactor01_dimension_free_bridge`
reconstructs only the corrected E4 ambient API needed by the reflection
proofs.  No ambient `HilbertSpaceIncidence Geo` assumption is used here.

The first checkpoint is the corrected analogue of the opening lemma of
old `AffineFlat4D_test36`: if Sigma is the perpendicular-bisector
hyperplane of AB, then the canonical corrected E4 reflection swaps A
and B.
-/

/--
If F is the midpoint of AB and the corrected normal from A to Sigma has
foot F, then corrected hyperplane reflection sends A to B.
-/
theorem hyperplaneReflect4_corrected_eq_of_perpendicular_midpoint_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A F B : Geo.Point)
    (hAoff : Not (Q.OnHyperplane A Sigma))
    (hPerp :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F A)
    (hMid :
      HilbertIsMidpoint Geo F A B) :
    hyperplaneReflect4_corrected Geo Sigma A = B := by

  have hRel :
      IsHyperplaneReflection4_corrected
        Geo Sigma A B :=
    Or.inr
      <| And.intro hAoff
        <| Exists.intro F
          <| And.intro hPerp hMid

  have hCanonical :
      IsHyperplaneReflection4_corrected
        Geo Sigma A
        (hyperplaneReflect4_corrected Geo Sigma A) :=
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma A

  have hEq :
      B = hyperplaneReflect4_corrected Geo Sigma A :=
    hyperplaneReflection4_unique_corrected
      (Geo := Geo)
      Sigma A
      B
      (hyperplaneReflect4_corrected Geo Sigma A)
      hRel
      hCanonical

  exact hEq.symm

/--
Under the same hypotheses, corrected hyperplane reflection sends B back
to A.

This uses involutivity rather than rebuilding the symmetric reflection
relation.  Thus the A4 adjacent-transposition mechanism is already
available on the corrected dimension-free E4 stack.
-/
theorem hyperplaneReflect4_corrected_swap_of_perpendicular_midpoint_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A F B : Geo.Point)
    (hAoff : Not (Q.OnHyperplane A Sigma))
    (hPerp :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F A)
    (hMid :
      HilbertIsMidpoint Geo F A B) :
    hyperplaneReflect4_corrected Geo Sigma B = A := by

  have hAB :
      hyperplaneReflect4_corrected Geo Sigma A = B :=
    hyperplaneReflect4_corrected_eq_of_perpendicular_midpoint_smith
      (Geo := Geo)
      Sigma A F B
      hAoff hPerp hMid

  have hInv :
      hyperplaneReflect4_corrected Geo Sigma
        (hyperplaneReflect4_corrected Geo Sigma A) = A :=
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo)
      Sigma A

  rw [hAB] at hInv
  exact hInv

/--
The corrected hyperplane reflection is an involutive ambient
equivalence on the dimension-free E4 stack.
-/
theorem hyperplaneReflectionEquiv4_corrected_sq_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane) :
    (hyperplaneReflectionEquiv4_corrected Geo Sigma).trans
        (hyperplaneReflectionEquiv4_corrected Geo Sigma) =
      Equiv.refl Geo.Point := by

  apply Equiv.ext
  intro P
  change
    hyperplaneReflect4_corrected Geo Sigma
        (hyperplaneReflect4_corrected Geo Sigma P) = P

  exact
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo)
      Sigma P

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: five-vertex permutation frame

This is the corrected dimension-free analogue of old
`AffineFlat4D_test36`.

We package five nonhyperplanar vertices A,B,C,D,E and four
perpendicular-bisector hyperplanes Sigma1,...,Sigma4.  The four
corrected E4 hyperplane reflections are then proved to act on the
vertices as the adjacent transpositions

  r1 = (A B),
  r2 = (B C),
  r3 = (C D),
  r4 = (D E).

No ambient `HilbertSpaceIncidence Geo` assumption occurs in this file.
-/

/--
Synthetic five-vertex mirror frame for Coxeter type A4 on the corrected dimension-free E4 stack.
-/
structure CoxeterA4SmithSimplexFrame
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo] where

  A : Geo.Point
  B : Geo.Point
  C : Geo.Point
  D : Geo.Point
  E : Geo.Point

  nonhyperplanar :
    Not (HilbertHyperplanar5 Geo A B C D E)

  Sigma1 : Q.Hyperplane
  F1 : Geo.Point

  A_off_Sigma1 :
    Not (Q.OnHyperplane A Sigma1)

  AB_perp_Sigma1 :
    PerpendicularToHyperplaneThrough4_corrected
      Geo Sigma1 F1 A

  F1_mid_AB :
    HilbertIsMidpoint Geo F1 A B

  C_on_Sigma1 :
    Q.OnHyperplane C Sigma1

  D_on_Sigma1 :
    Q.OnHyperplane D Sigma1

  E_on_Sigma1 :
    Q.OnHyperplane E Sigma1

  Sigma2 : Q.Hyperplane
  F2 : Geo.Point

  B_off_Sigma2 :
    Not (Q.OnHyperplane B Sigma2)

  BC_perp_Sigma2 :
    PerpendicularToHyperplaneThrough4_corrected
      Geo Sigma2 F2 B

  F2_mid_BC :
    HilbertIsMidpoint Geo F2 B C

  A_on_Sigma2 :
    Q.OnHyperplane A Sigma2

  D_on_Sigma2 :
    Q.OnHyperplane D Sigma2

  E_on_Sigma2 :
    Q.OnHyperplane E Sigma2

  Sigma3 : Q.Hyperplane
  F3 : Geo.Point

  C_off_Sigma3 :
    Not (Q.OnHyperplane C Sigma3)

  CD_perp_Sigma3 :
    PerpendicularToHyperplaneThrough4_corrected
      Geo Sigma3 F3 C

  F3_mid_CD :
    HilbertIsMidpoint Geo F3 C D

  A_on_Sigma3 :
    Q.OnHyperplane A Sigma3

  B_on_Sigma3 :
    Q.OnHyperplane B Sigma3

  E_on_Sigma3 :
    Q.OnHyperplane E Sigma3

  Sigma4 : Q.Hyperplane
  F4 : Geo.Point

  D_off_Sigma4 :
    Not (Q.OnHyperplane D Sigma4)

  DE_perp_Sigma4 :
    PerpendicularToHyperplaneThrough4_corrected
      Geo Sigma4 F4 D

  F4_mid_DE :
    HilbertIsMidpoint Geo F4 D E

  A_on_Sigma4 :
    Q.OnHyperplane A Sigma4

  B_on_Sigma4 :
    Q.OnHyperplane B Sigma4

  C_on_Sigma4 :
    Q.OnHyperplane C Sigma4


namespace CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/--
First A4 generator: reflection in the perpendicular-bisector
hyperplane of AB.
-/
noncomputable def r1
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  hyperplaneReflectionEquiv4_corrected Geo T.Sigma1

/--
Second A4 generator: reflection in the perpendicular-bisector
hyperplane of BC.
-/
noncomputable def r2
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  hyperplaneReflectionEquiv4_corrected Geo T.Sigma2

/--
Third A4 generator: reflection in the perpendicular-bisector
hyperplane of CD.
-/
noncomputable def r3
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  hyperplaneReflectionEquiv4_corrected Geo T.Sigma3

/--
Fourth A4 generator: reflection in the perpendicular-bisector
hyperplane of DE.
-/
noncomputable def r4
    (T : CoxeterA4SmithSimplexFrame Geo) :
    Equiv Geo.Point Geo.Point :=
  hyperplaneReflectionEquiv4_corrected Geo T.Sigma4


@[simp]
theorem r1_apply
    (T : CoxeterA4SmithSimplexFrame Geo)
    (P : Geo.Point) :
    r1 (Geo := Geo) T P =
      hyperplaneReflect4_corrected Geo T.Sigma1 P := by
  rfl

@[simp]
theorem r2_apply
    (T : CoxeterA4SmithSimplexFrame Geo)
    (P : Geo.Point) :
    r2 (Geo := Geo) T P =
      hyperplaneReflect4_corrected Geo T.Sigma2 P := by
  rfl

@[simp]
theorem r3_apply
    (T : CoxeterA4SmithSimplexFrame Geo)
    (P : Geo.Point) :
    r3 (Geo := Geo) T P =
      hyperplaneReflect4_corrected Geo T.Sigma3 P := by
  rfl

@[simp]
theorem r4_apply
    (T : CoxeterA4SmithSimplexFrame Geo)
    (P : Geo.Point) :
    r4 (Geo := Geo) T P =
      hyperplaneReflect4_corrected Geo T.Sigma4 P := by
  rfl


/-!
## r1 = (A B)
-/

@[simp]
theorem r1_A
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r1 (Geo := Geo) T T.A = T.B := by

  exact
    hyperplaneReflect4_corrected_eq_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma1
      T.A T.F1 T.B
      T.A_off_Sigma1
      T.AB_perp_Sigma1
      T.F1_mid_AB

@[simp]
theorem r1_B
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r1 (Geo := Geo) T T.B = T.A := by

  exact
    hyperplaneReflect4_corrected_swap_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma1
      T.A T.F1 T.B
      T.A_off_Sigma1
      T.AB_perp_Sigma1
      T.F1_mid_AB

@[simp]
theorem r1_C
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r1 (Geo := Geo) T T.C = T.C := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma1 T.C).mpr
      T.C_on_Sigma1

@[simp]
theorem r1_D
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r1 (Geo := Geo) T T.D = T.D := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma1 T.D).mpr
      T.D_on_Sigma1

@[simp]
theorem r1_E
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r1 (Geo := Geo) T T.E = T.E := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma1 T.E).mpr
      T.E_on_Sigma1


/-!
## r2 = (B C)
-/

@[simp]
theorem r2_A
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r2 (Geo := Geo) T T.A = T.A := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma2 T.A).mpr
      T.A_on_Sigma2

@[simp]
theorem r2_B
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r2 (Geo := Geo) T T.B = T.C := by

  exact
    hyperplaneReflect4_corrected_eq_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma2
      T.B T.F2 T.C
      T.B_off_Sigma2
      T.BC_perp_Sigma2
      T.F2_mid_BC

@[simp]
theorem r2_C
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r2 (Geo := Geo) T T.C = T.B := by

  exact
    hyperplaneReflect4_corrected_swap_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma2
      T.B T.F2 T.C
      T.B_off_Sigma2
      T.BC_perp_Sigma2
      T.F2_mid_BC

@[simp]
theorem r2_D
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r2 (Geo := Geo) T T.D = T.D := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma2 T.D).mpr
      T.D_on_Sigma2

@[simp]
theorem r2_E
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r2 (Geo := Geo) T T.E = T.E := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma2 T.E).mpr
      T.E_on_Sigma2


/-!
## r3 = (C D)
-/

@[simp]
theorem r3_A
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r3 (Geo := Geo) T T.A = T.A := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma3 T.A).mpr
      T.A_on_Sigma3

@[simp]
theorem r3_B
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r3 (Geo := Geo) T T.B = T.B := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma3 T.B).mpr
      T.B_on_Sigma3

@[simp]
theorem r3_C
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r3 (Geo := Geo) T T.C = T.D := by

  exact
    hyperplaneReflect4_corrected_eq_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma3
      T.C T.F3 T.D
      T.C_off_Sigma3
      T.CD_perp_Sigma3
      T.F3_mid_CD

@[simp]
theorem r3_D
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r3 (Geo := Geo) T T.D = T.C := by

  exact
    hyperplaneReflect4_corrected_swap_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma3
      T.C T.F3 T.D
      T.C_off_Sigma3
      T.CD_perp_Sigma3
      T.F3_mid_CD

@[simp]
theorem r3_E
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r3 (Geo := Geo) T T.E = T.E := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma3 T.E).mpr
      T.E_on_Sigma3


/-!
## r4 = (D E)
-/

@[simp]
theorem r4_A
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r4 (Geo := Geo) T T.A = T.A := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma4 T.A).mpr
      T.A_on_Sigma4

@[simp]
theorem r4_B
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r4 (Geo := Geo) T T.B = T.B := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma4 T.B).mpr
      T.B_on_Sigma4

@[simp]
theorem r4_C
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r4 (Geo := Geo) T T.C = T.C := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      T.Sigma4 T.C).mpr
      T.C_on_Sigma4

@[simp]
theorem r4_D
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r4 (Geo := Geo) T T.D = T.E := by

  exact
    hyperplaneReflect4_corrected_eq_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma4
      T.D T.F4 T.E
      T.D_off_Sigma4
      T.DE_perp_Sigma4
      T.F4_mid_DE

@[simp]
theorem r4_E
    (T : CoxeterA4SmithSimplexFrame Geo) :
    r4 (Geo := Geo) T T.E = T.D := by

  exact
    hyperplaneReflect4_corrected_swap_of_perpendicular_midpoint_smith
      (Geo := Geo)
      T.Sigma4
      T.D T.F4 T.E
      T.D_off_Sigma4
      T.DE_perp_Sigma4
      T.F4_mid_DE

end CoxeterA4SmithSimplexFrame

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: adjacent mirror transport

The previous tests established the five-vertex A4 frame and the action

  r1 = (A B),  r2 = (B C),  r3 = (C D),  r4 = (D E)

on the distinguished vertices.

For the first braid relation we do not need a general five-anchor
rigidity theorem.  Since r1 and r2 are reflections, the geometric core
is the equality of the two transported mirrors

  r1(Sigma2) = r2(Sigma1).

Sigma1 and Sigma2 contain the two common distinct points D,E, hence the
corrected E4 incidence theory supplies a common ambient 2-plane Delta.
Both transported hyperplanes contain Delta and B.  The point B is not
in Delta because Delta is contained in Sigma2 while B is external to
Sigma2.  Therefore the corrected uniqueness theorem for a hyperplane
through a plane and one external point identifies the two transported
mirrors.

No ambient HilbertSpaceIncidence assumption and no five-anchor metric
rigidity assumption occurs here.
-/

namespace CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-
The first two A4 mirrors have a common ambient 2-plane through D and E.
-/
omit [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo] in
theorem sigma12_common_plane_exists
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      HilbertPlaneInHyperplane4 Geo Delta T.Sigma1 /\
      HilbertPlaneInHyperplane4 Geo Delta T.Sigma2 := by

  have hDE : Ne T.D T.E :=
    (H4O.between_incidence
      T.D T.F4 T.E T.F4_mid_DE.1).2.2.1

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
        (Geo := Geo)
        T.Sigma1 T.Sigma2
        T.D T.E
        hDE
        T.D_on_Sigma1 T.E_on_Sigma1
        T.D_on_Sigma2 T.E_on_Sigma2 with
    ⟨Delta, _hDDelta, _hEDelta, hDelta1, hDelta2⟩

  exact ⟨Delta, hDelta1, hDelta2⟩

/--
Geometric core of the first A4 braid relation:
reflection in Sigma1 transports Sigma2 to the same hyperplane to which
reflection in Sigma2 transports Sigma1.
-/
theorem braid12_reflected_mirrors_eq
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      exists hDelta1 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma1,
        exists hDelta2 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma2,
          hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma1 T.Sigma2 Delta hDelta1 hDelta2 =
            hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma2 T.Sigma1 Delta hDelta2 hDelta1 := by

  rcases sigma12_common_plane_exists (Geo := Geo) T with
    ⟨Delta, hDelta1, hDelta2⟩

  refine ⟨Delta, hDelta1, hDelta2, ?_⟩

  let Lambda12 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma1 T.Sigma2 Delta hDelta1 hDelta2

  let Lambda21 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma2 T.Sigma1 Delta hDelta2 hDelta1

  have hDelta12 :
      HilbertPlaneInHyperplane4 Geo Delta Lambda12 := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        T.Sigma1 T.Sigma2 Delta hDelta1 hDelta2

  have hDelta21 :
      HilbertPlaneInHyperplane4 Geo Delta Lambda21 := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        T.Sigma2 T.Sigma1 Delta hDelta2 hDelta1

  have hBoffDelta :
      Not (Q.toHilbertSpacePrimitive.OnPlane T.B Delta) := by
    intro hBDelta
    exact T.B_off_Sigma2 (hDelta2 T.B hBDelta)

  have hB12 : Q.OnHyperplane T.B Lambda12 := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        T.Sigma1 T.Sigma2 Delta
        hDelta1 hDelta2
        T.A T.A_on_Sigma2

    have hr1A :
        hyperplaneReflect4_corrected Geo T.Sigma1 T.A = T.B := by
      simpa only [r1_apply] using r1_A (Geo := Geo) T

    simpa only [Lambda12, hr1A] using hImage

  have hB21 : Q.OnHyperplane T.B Lambda21 := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        T.Sigma2 T.Sigma1 Delta
        hDelta2 hDelta1
        T.C T.C_on_Sigma1

    have hr2C :
        hyperplaneReflect4_corrected Geo T.Sigma2 T.C = T.B := by
      simpa only [r2_apply] using r2_C (Geo := Geo) T

    simpa only [Lambda21, hr2C] using hImage

  have hCanon12 :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta T.B hBoffDelta =
        Lambda12 :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta T.B hBoffDelta
      Lambda12 hDelta12 hB12

  have hCanon21 :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta T.B hBoffDelta =
        Lambda21 :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta T.B hBoffDelta
      Lambda21 hDelta21 hB21

  change Lambda12 = Lambda21
  exact hCanon12.symm.trans hCanon21

end CoxeterA4SmithSimplexFrame

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: angle transport under corrected E4 reflection

Test07 identified the common fixed hyperplane of the two conjugate braid
words.  To identify a conjugated reflection with the canonical reflection
in the transported hyperplane, the next geometric ingredient is transport
of perpendicularity.

The first metric step is dimension-safe angle transport.

For a noncollinear ambient triple A,B,C, corrected E4 hyperplane reflection
preserves all three side congruences.  The reflected triple is again
noncollinear.  Put the reflected triple into one explicit Smith plane and
apply the corrected ambient E4 SSS theorem.

No ambient `HilbertCongruence Geo` or `HilbertSpaceIncidence Geo` is used.
-/

/--
Corrected E4 hyperplane reflection preserves a nondegenerate angle.
-/
theorem hyperplaneReflect4_corrected_preserves_angle_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    Geo.AngleCongruent
      A B C
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C) := by

  let A' : Geo.Point :=
    hyperplaneReflect4_corrected Geo Sigma A

  let B' : Geo.Point :=
    hyperplaneReflect4_corrected Geo Sigma B

  let C' : Geo.Point :=
    hyperplaneReflect4_corrected Geo Sigma C

  have hABC' :
      Not (PrimCollinear Geo A' B' C') := by
    dsimp [A', B', C']
    exact
      hyperplaneReflect4_corrected_preserves_noncollinear
        (Geo := Geo)
        Sigma A B C hABC

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hB'A'C' :
      Not (PrimCollinear Geo B' A' C') := by
    intro h
    exact hABC'
      (PrimCollinearSwap Geo B' A' C' h)

  have hPiExists :=
    D.plane_through
      B' A' C' hB'A'C'

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hPiExists

  have hPiData :=
    Classical.choose_spec hPiExists

  have hB'pi :
      Q.toHilbertSpacePrimitive.OnPlane B' pi :=
    hPiData.1

  have hA'pi :
      Q.toHilbertSpacePrimitive.OnPlane A' pi :=
    hPiData.2.1

  have hC'pi :
      Q.toHilbertSpacePrimitive.OnPlane C' pi :=
    hPiData.2.2

  let Bp : PlanePoint Geo pi :=
    ⟨B', hB'pi⟩

  let Ap : PlanePoint Geo pi :=
    ⟨A', hA'pi⟩

  let Cp : PlanePoint Geo pi :=
    ⟨C', hC'pi⟩

  have hBA :
      Geo.Congruent B A B' A' := by
    dsimp [A', B']
    exact
      hyperplaneReflect4_corrected_preserves_congruence
        (Geo := Geo)
        Sigma B A

  have hAC :
      Geo.Congruent A C A' C' := by
    dsimp [A', C']
    exact
      hyperplaneReflect4_corrected_preserves_congruence
        (Geo := Geo)
        Sigma A C

  have hBC :
      Geo.Congruent B C B' C' := by
    dsimp [B', C']
    exact
      hyperplaneReflect4_corrected_preserves_congruence
        (Geo := Geo)
        Sigma B C

  have hAngle :
      Geo.AngleCongruent
        A B C
        A' B' C' := by

    have hSSS :=
      hilbert4D_ambient_sss_angleA_in_plane_corrected
        (Geo := Geo)
        pi
        B A C
        Bp Ap Cp
        hBAC
        hB'A'C'
        hBA
        hAC
        hBC

    simpa only [Bp, Ap, Cp] using hSSS

  simpa only [A', B', C'] using hAngle

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: perpendicularity transport

Test08 proved dimension-safe angle transport for corrected E4 hyperplane
reflection.  The present test upgrades that result in two steps:

1. a nondegenerate Hilbert right angle is preserved;
2. an ambient perpendicular line pair is transported to a perpendicular
   line pair.

No ambient `HilbertCongruence Geo` or `HilbertSpaceIncidence Geo` is used.
-/

/--
Corrected E4 hyperplane reflection preserves a nondegenerate Hilbert
right angle.
-/
theorem hyperplaneReflect4_corrected_preserves_right_angle_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle
      Geo
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma O)
      (hyperplaneReflect4_corrected Geo Sigma B) := by

  rcases hRight with ⟨C, hAOC, hAngle⟩

  have hAOCData :=
    H4O.between_incidence A O C hAOC

  have hOC :
      Ne O C :=
    hAOCData.2.1

  have hAOCcol :
      PrimCollinear Geo A O C :=
    hAOCData.2.2.2.1

  have hBOC :
      Not (PrimCollinear Geo B O C) := by
    intro hBOCcol

    rcases hAOCcol with
      ⟨l, hAl, hOl, hCl⟩

    rcases hBOCcol with
      ⟨m, hBm, hOm, hCm⟩

    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O C hOC l m
        hOl hCl hOm hCm

    apply hAOB

    refine ⟨l, hAl, hOl, ?_⟩

    rw [hlm]
    exact hBm

  have hAOBImage :
      Geo.AngleCongruent
        A O B
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma B) :=
    hyperplaneReflect4_corrected_preserves_angle_smith
      (Geo := Geo)
      Sigma A O B hAOB

  have hBOCImage :
      Geo.AngleCongruent
        B O C
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma C) :=
    hyperplaneReflect4_corrected_preserves_angle_smith
      (Geo := Geo)
      Sigma B O C hBOC

  have hImageAOB_BOC :
      Geo.AngleCongruent
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma C) := by

    have hImageAOB_AOB :
        Geo.AngleCongruent
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma O)
          (hyperplaneReflect4_corrected Geo Sigma B)
          A O B :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A O B
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma B)
        hAOBImage

    have hImageAOB_BOC :
        Geo.AngleCongruent
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma O)
          (hyperplaneReflect4_corrected Geo Sigma B)
          B O C :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma B)
        A O B
        B O C
        hImageAOB_AOB
        hAngle

    exact
      Geometry.Geo.angle_congruent_transitivity
        Geo
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma B)
        B O C
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma C)
        hImageAOB_BOC
        hBOCImage

  have hBetweenImage :
      Geo.Between
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma C) :=
    hyperplaneReflect4_corrected_preserves_between
      (Geo := Geo)
      Sigma A O C hAOC

  exact
    ⟨hyperplaneReflect4_corrected Geo Sigma C,
      hBetweenImage,
      hImageAOB_BOC⟩


/--
A perpendicular ambient line pair is transported by corrected E4
hyperplane reflection to a perpendicular ambient line pair.

The target lines are the exact line images supplied by the existing
line-transport API.
-/
theorem hyperplaneReflectionMapsPerpendicularPair4_corrected_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (l m : Geo.Line)
    (O : Geo.Point)
    (hPerp : HilbertLinesPerpendicularAt Geo l m O) :
    exists l' m' : Geo.Line,
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma l l' /\
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma m m' /\
      HilbertLinesPerpendicularAt
        Geo l' m'
        (hyperplaneReflect4_corrected Geo Sigma O) := by

  have hlExists :=
    hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma l

  let l' : Geo.Line :=
    Classical.choose hlExists

  have hlMap :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma l l' :=
    Classical.choose_spec hlExists

  have hmExists :=
    hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma m

  let m' : Geo.Line :=
    Classical.choose hmExists

  have hmMap :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma m m' :=
    Classical.choose_spec hmExists

  rcases hPerp with
    ⟨hOl, hOm,
     A, B,
     hAO, hBO,
     hAl, hBm,
     hAOB,
     hRight⟩

  have hO'l' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma O)
        l' :=
    (hlMap O).mp hOl

  have hO'm' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma O)
        m' :=
    (hmMap O).mp hOm

  have hA'l' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma A)
        l' :=
    (hlMap A).mp hAl

  have hB'm' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma B)
        m' :=
    (hmMap B).mp hBm

  have hA'O' :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O) := by
    intro hEq
    apply hAO
    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  have hB'O' :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma O) := by
    intro hEq
    apply hBO
    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  have hA'O'B' :
      Not
        (PrimCollinear
          Geo
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma O)
          (hyperplaneReflect4_corrected Geo Sigma B)) :=
    hyperplaneReflect4_corrected_preserves_noncollinear
      (Geo := Geo)
      Sigma A O B hAOB

  have hRightImage :
      HilbertRightAngle
        Geo
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma O)
        (hyperplaneReflect4_corrected Geo Sigma B) :=
    hyperplaneReflect4_corrected_preserves_right_angle_smith
      (Geo := Geo)
      Sigma A O B hAOB hRight

  refine ⟨l', m', hlMap, hmMap, ?_⟩

  exact
    ⟨hO'l', hO'm',
      hyperplaneReflect4_corrected Geo Sigma A,
      hyperplaneReflect4_corrected Geo Sigma B,
      hA'O', hB'O',
      hA'l', hB'm',
      hA'O'B',
      hRightImage⟩

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: normal-line transport

Test09 proved that corrected E4 hyperplane reflection transports an
ambient perpendicular pair of lines to a perpendicular pair.

The present test upgrades this to the genuinely four-dimensional
statement needed for conjugating hyperplane reflections:

  if l is normal to a source hyperplane Tau at F,
  l' is the exact reflected image of l, and
  Lambda is the exact reflected image of Tau,
  then l' is normal to Lambda at r(F).

The proof does not use ambient `HilbertSpaceIncidence Geo` or ambient
`HilbertCongruence Geo`.
-/

/--
Exact corrected reflection transport preserves a normal line to a
hyperplane.
-/
theorem hyperplaneReflectionMapsNormalLine4_corrected_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau Lambda : Q.Hyperplane)
    (l l' : Geo.Line)
    (F : Geo.Point)
    (hTauMap :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo Sigma Tau Lambda)
    (hlMap :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma l l')
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Tau F) :
    HilbertLinePerpendicularHyperplaneAt4_corrected
      Geo l' Lambda
      (hyperplaneReflect4_corrected Geo Sigma F) := by

  let F' : Geo.Point :=
    hyperplaneReflect4_corrected Geo Sigma F

  have hFl : H.OnLine F l :=
    hNormal.1

  have hFTau : Q.OnHyperplane F Tau :=
    hNormal.2.1

  have hF'l' : H.OnLine F' l' := by
    exact (hlMap F).mp hFl

  have hF'Lambda : Q.OnHyperplane F' Lambda := by
    exact (hTauMap F).mp hFTau

  refine ⟨hF'l', hF'Lambda, ?_⟩

  intro m' hm'Lambda hF'm'

  have hmBackExists :=
    hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma m'

  let m : Geo.Line :=
    Classical.choose hmBackExists

  have hmBack :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma m' m :=
    Classical.choose_spec hmBackExists

  have hmForward :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma m m' :=
    hyperplaneReflectionMapsLine4_corrected_symm
      (Geo := Geo)
      Sigma m' m hmBack

  have hmTau : HilbertLineInHyperplane4 Geo m Tau := by
    intro X hXm

    have hRXm' :
        H.OnLine
          (hyperplaneReflect4_corrected Geo Sigma X)
          m' :=
      (hmForward X).mp hXm

    have hRXLambda :
        Q.OnHyperplane
          (hyperplaneReflect4_corrected Geo Sigma X)
          Lambda :=
      hm'Lambda
        (hyperplaneReflect4_corrected Geo Sigma X)
        hRXm'

    exact (hTauMap X).mpr hRXLambda

  have hFm : H.OnLine F m := by
    have hBack :
        H.OnLine
          (hyperplaneReflect4_corrected Geo Sigma F')
          m :=
      (hmBack F').mp hF'm'

    simpa only [
      F',
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma F
    ] using hBack

  have hPerp :
      HilbertLinesPerpendicularAt Geo l m F :=
    hNormal.2.2 m hmTau hFm

  rcases
      hyperplaneReflectionMapsPerpendicularPair4_corrected_smith
        (Geo := Geo)
        Sigma l m F hPerp with
    ⟨l1, m1, hl1Map, hm1Map, hPerpImage⟩

  have hl1eq : l1 = l' :=
    hyperplaneReflectionMapsLine4_corrected_unique
      (Geo := Geo)
      Sigma l l1 l'
      hl1Map hlMap

  have hm1eq : m1 = m' :=
    hyperplaneReflectionMapsLine4_corrected_unique
      (Geo := Geo)
      Sigma m m1 m'
      hm1Map hmForward

  subst l1
  subst m1

  exact hPerpImage

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: conjugation of corrected E4 reflections

Test10 proved that corrected hyperplane reflection transports a normal
line to a source hyperplane into a normal line to the reflected target
hyperplane.

This file uses that fact to transport the full relational reflection
specification.  Hence conjugating reflection in Tau by reflection in
Sigma is exactly reflection in the reflected image Lambda of Tau:

  r_Sigma (r_Tau (r_Sigma X)) = r_Lambda X.

The final theorem applies this to the two adjacent A4 mirrors Sigma1 and
Sigma2.  Test06 already proved that their two transported mirrors agree,
so the first braid relation follows globally on every point of E4.

No ambient HilbertSpaceIncidence and no finite-anchor rigidity theorem is
used.
-/

/--
Corrected reflection transports the relational hyperplane-reflection
specification from Tau to its exact reflected image Lambda.
-/
theorem hyperplaneReflection4_relation_transport_corrected_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau Lambda : Q.Hyperplane)
    (hTauMap :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo Sigma Tau Lambda)
    (P P' : Geo.Point)
    (hRef :
      IsHyperplaneReflection4_corrected
        Geo Tau P P') :
    IsHyperplaneReflection4_corrected
      Geo Lambda
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma P') := by

  rcases hRef with hFixed | hOff

  · rcases hFixed with ⟨hPTau, hP'eq⟩
    subst P'

    exact
      Or.inl
        ⟨(hTauMap P).mp hPTau, rfl⟩

  · rcases hOff with
      ⟨hPoffTau, F, hPerp, hMid⟩

    have hRPoffLambda :
        Not
          (Q.OnHyperplane
            (hyperplaneReflect4_corrected Geo Sigma P)
            Lambda) := by
      intro hRPLambda
      exact hPoffTau ((hTauMap P).mpr hRPLambda)

    rcases hPerp with
      ⟨l, hPl, hNormal⟩

    rcases
        hyperplaneReflectionMapsLine4_corrected_exists
          (Geo := Geo)
          Sigma l with
      ⟨l', hlMap⟩

    have hRPl' :
        H.OnLine
          (hyperplaneReflect4_corrected Geo Sigma P)
          l' :=
      (hlMap P).mp hPl

    have hNormalImage :
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo l' Lambda
          (hyperplaneReflect4_corrected Geo Sigma F) :=
      hyperplaneReflectionMapsNormalLine4_corrected_smith
        (Geo := Geo)
        Sigma Tau Lambda
        l l' F
        hTauMap hlMap hNormal

    have hPerpImage :
        PerpendicularToHyperplaneThrough4_corrected
          Geo Lambda
          (hyperplaneReflect4_corrected Geo Sigma F)
          (hyperplaneReflect4_corrected Geo Sigma P) := by
      exact ⟨l', hRPl', hNormalImage⟩

    have hMidImage :
        HilbertIsMidpoint
          Geo
          (hyperplaneReflect4_corrected Geo Sigma F)
          (hyperplaneReflect4_corrected Geo Sigma P)
          (hyperplaneReflect4_corrected Geo Sigma P') :=
      hyperplaneReflect4_corrected_preserves_midpoint
        (Geo := Geo)
        Sigma F P P' hMid

    exact
      Or.inr
        ⟨hRPoffLambda,
          hyperplaneReflect4_corrected Geo Sigma F,
          hPerpImage,
          hMidImage⟩

/--
Pointwise conjugation formula for corrected E4 hyperplane reflections.
-/
theorem hyperplaneReflect4_corrected_conjugation_pointwise_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau Lambda : Q.Hyperplane)
    (hTauMap :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo Sigma Tau Lambda)
    (X : Geo.Point) :
    hyperplaneReflect4_corrected Geo Sigma
        (hyperplaneReflect4_corrected Geo Tau
          (hyperplaneReflect4_corrected Geo Sigma X)) =
      hyperplaneReflect4_corrected Geo Lambda X := by

  let P : Geo.Point :=
    hyperplaneReflect4_corrected Geo Sigma X

  let P' : Geo.Point :=
    hyperplaneReflect4_corrected Geo Tau P

  have hRefTau :
      IsHyperplaneReflection4_corrected
        Geo Tau P P' := by
    exact
      hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Tau P

  have hTransport :
      IsHyperplaneReflection4_corrected
        Geo Lambda
        (hyperplaneReflect4_corrected Geo Sigma P)
        (hyperplaneReflect4_corrected Geo Sigma P') :=
    hyperplaneReflection4_relation_transport_corrected_smith
      (Geo := Geo)
      Sigma Tau Lambda hTauMap
      P P' hRefTau

  have hCandidate :
      IsHyperplaneReflection4_corrected
        Geo Lambda X
        (hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Tau
            (hyperplaneReflect4_corrected Geo Sigma X))) := by
    simpa only [P, P',
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma X] using hTransport

  have hCanonical :
      IsHyperplaneReflection4_corrected
        Geo Lambda X
        (hyperplaneReflect4_corrected Geo Lambda X) :=
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Lambda X

  exact
    hyperplaneReflection4_unique_corrected
      (Geo := Geo)
      Lambda X
      (hyperplaneReflect4_corrected Geo Sigma
        (hyperplaneReflect4_corrected Geo Tau
          (hyperplaneReflect4_corrected Geo Sigma X)))
      (hyperplaneReflect4_corrected Geo Lambda X)
      hCandidate hCanonical

namespace CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/--
The first A4 braid relation holds globally on every point of E4.
-/
theorem braid12_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    r1 (Geo := Geo) T
        (r2 (Geo := Geo) T
          (r1 (Geo := Geo) T X)) =
      r2 (Geo := Geo) T
        (r1 (Geo := Geo) T
          (r2 (Geo := Geo) T X)) := by

  rcases braid12_reflected_mirrors_eq (Geo := Geo) T with
    ⟨Delta, hDelta1, hDelta2, hLambdaEq⟩

  let Lambda12 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma1 T.Sigma2 Delta hDelta1 hDelta2

  let Lambda21 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma2 T.Sigma1 Delta hDelta2 hDelta1

  have hMap12 :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma1 T.Sigma2 Lambda12 := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma1 T.Sigma2 Delta hDelta1 hDelta2

  have hMap21 :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma2 T.Sigma1 Lambda21 := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma2 T.Sigma1 Delta hDelta2 hDelta1

  have hLeft :
      hyperplaneReflect4_corrected Geo T.Sigma1
          (hyperplaneReflect4_corrected Geo T.Sigma2
            (hyperplaneReflect4_corrected Geo T.Sigma1 X)) =
        hyperplaneReflect4_corrected Geo Lambda12 X :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      T.Sigma1 T.Sigma2 Lambda12 hMap12 X

  have hRight :
      hyperplaneReflect4_corrected Geo T.Sigma2
          (hyperplaneReflect4_corrected Geo T.Sigma1
            (hyperplaneReflect4_corrected Geo T.Sigma2 X)) =
        hyperplaneReflect4_corrected Geo Lambda21 X :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      T.Sigma2 T.Sigma1 Lambda21 hMap21 X

  have hLambda : Lambda12 = Lambda21 := by
    simpa only [Lambda12, Lambda21] using hLambdaEq

  have hRaw :
      hyperplaneReflect4_corrected Geo T.Sigma1
          (hyperplaneReflect4_corrected Geo T.Sigma2
            (hyperplaneReflect4_corrected Geo T.Sigma1 X)) =
        hyperplaneReflect4_corrected Geo T.Sigma2
          (hyperplaneReflect4_corrected Geo T.Sigma1
            (hyperplaneReflect4_corrected Geo T.Sigma2 X)) := by
    calc
      hyperplaneReflect4_corrected Geo T.Sigma1
          (hyperplaneReflect4_corrected Geo T.Sigma2
            (hyperplaneReflect4_corrected Geo T.Sigma1 X))
          = hyperplaneReflect4_corrected Geo Lambda12 X := hLeft
      _ = hyperplaneReflect4_corrected Geo Lambda21 X := by rw [hLambda]
      _ = hyperplaneReflect4_corrected Geo T.Sigma2
          (hyperplaneReflect4_corrected Geo T.Sigma1
            (hyperplaneReflect4_corrected Geo T.Sigma2 X)) := hRight.symm

  simpa only [r1_apply, r2_apply] using hRaw

end CoxeterA4SmithSimplexFrame

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: all adjacent braid relations

Test11 proved the first global A4 braid relation by the corrected E4
conjugation formula for hyperplane reflections and equality of the two
transported mirrors.

This file repeats only the mirror-incidence part for the adjacent pairs

  (Sigma2, Sigma3) and (Sigma3, Sigma4),

then reuses the general conjugation theorem from Test11.

No ambient HilbertSpaceIncidence and no finite-anchor rigidity theorem is
used.
-/

namespace CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/- Sigma2 and Sigma3 have a common ambient plane through A and E. -/
omit [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo] in
theorem sigma23_common_plane_exists
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      HilbertPlaneInHyperplane4 Geo Delta T.Sigma2 /\
      HilbertPlaneInHyperplane4 Geo Delta T.Sigma3 := by

  have hAE : Ne T.A T.E := by
    intro hAE
    apply T.A_off_Sigma1
    rw [hAE]
    exact T.E_on_Sigma1

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
        (Geo := Geo)
        T.Sigma2 T.Sigma3
        T.A T.E
        hAE
        T.A_on_Sigma2 T.E_on_Sigma2
        T.A_on_Sigma3 T.E_on_Sigma3 with
    ⟨Delta, _hADelta, _hEDelta, hDelta2, hDelta3⟩

  exact ⟨Delta, hDelta2, hDelta3⟩

/-- Equality of the two transported mirrors for the pair Sigma2,Sigma3. -/
theorem braid23_reflected_mirrors_eq
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      exists hDelta2 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma2,
        exists hDelta3 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma3,
          hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma2 T.Sigma3 Delta hDelta2 hDelta3 =
            hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma3 T.Sigma2 Delta hDelta3 hDelta2 := by

  rcases sigma23_common_plane_exists (Geo := Geo) T with
    ⟨Delta, hDelta2, hDelta3⟩

  refine ⟨Delta, hDelta2, hDelta3, ?_⟩

  let Lambda23 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma2 T.Sigma3 Delta hDelta2 hDelta3

  let Lambda32 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma3 T.Sigma2 Delta hDelta3 hDelta2

  have hDelta23 :
      HilbertPlaneInHyperplane4 Geo Delta Lambda23 := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        T.Sigma2 T.Sigma3 Delta hDelta2 hDelta3

  have hDelta32 :
      HilbertPlaneInHyperplane4 Geo Delta Lambda32 := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        T.Sigma3 T.Sigma2 Delta hDelta3 hDelta2

  have hCoffDelta :
      Not (Q.toHilbertSpacePrimitive.OnPlane T.C Delta) := by
    intro hCDelta
    exact T.C_off_Sigma3 (hDelta3 T.C hCDelta)

  have hC23 : Q.OnHyperplane T.C Lambda23 := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        T.Sigma2 T.Sigma3 Delta
        hDelta2 hDelta3
        T.B T.B_on_Sigma3

    have hr2B :
        hyperplaneReflect4_corrected Geo T.Sigma2 T.B = T.C := by
      simpa only [r2_apply] using r2_B (Geo := Geo) T

    simpa only [Lambda23, hr2B] using hImage

  have hC32 : Q.OnHyperplane T.C Lambda32 := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        T.Sigma3 T.Sigma2 Delta
        hDelta3 hDelta2
        T.D T.D_on_Sigma2

    have hr3D :
        hyperplaneReflect4_corrected Geo T.Sigma3 T.D = T.C := by
      simpa only [r3_apply] using r3_D (Geo := Geo) T

    simpa only [Lambda32, hr3D] using hImage

  have hCanon23 :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta T.C hCoffDelta =
        Lambda23 :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta T.C hCoffDelta
      Lambda23 hDelta23 hC23

  have hCanon32 :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta T.C hCoffDelta =
        Lambda32 :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta T.C hCoffDelta
      Lambda32 hDelta32 hC32

  change Lambda23 = Lambda32
  exact hCanon23.symm.trans hCanon32

/- Sigma3 and Sigma4 have a common ambient plane through A and B. -/
omit [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo] in
theorem sigma34_common_plane_exists
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      HilbertPlaneInHyperplane4 Geo Delta T.Sigma3 /\
      HilbertPlaneInHyperplane4 Geo Delta T.Sigma4 := by

  have hAB : Ne T.A T.B :=
    (H4O.between_incidence
      T.A T.F1 T.B T.F1_mid_AB.1).2.2.1

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
        (Geo := Geo)
        T.Sigma3 T.Sigma4
        T.A T.B
        hAB
        T.A_on_Sigma3 T.B_on_Sigma3
        T.A_on_Sigma4 T.B_on_Sigma4 with
    ⟨Delta, _hADelta, _hBDelta, hDelta3, hDelta4⟩

  exact ⟨Delta, hDelta3, hDelta4⟩

/-- Equality of the two transported mirrors for the pair Sigma3,Sigma4. -/
theorem braid34_reflected_mirrors_eq
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      exists hDelta3 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma3,
        exists hDelta4 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma4,
          hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma3 T.Sigma4 Delta hDelta3 hDelta4 =
            hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma4 T.Sigma3 Delta hDelta4 hDelta3 := by

  rcases sigma34_common_plane_exists (Geo := Geo) T with
    ⟨Delta, hDelta3, hDelta4⟩

  refine ⟨Delta, hDelta3, hDelta4, ?_⟩

  let Lambda34 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma3 T.Sigma4 Delta hDelta3 hDelta4

  let Lambda43 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma4 T.Sigma3 Delta hDelta4 hDelta3

  have hDelta34 :
      HilbertPlaneInHyperplane4 Geo Delta Lambda34 := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        T.Sigma3 T.Sigma4 Delta hDelta3 hDelta4

  have hDelta43 :
      HilbertPlaneInHyperplane4 Geo Delta Lambda43 := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        T.Sigma4 T.Sigma3 Delta hDelta4 hDelta3

  have hDoffDelta :
      Not (Q.toHilbertSpacePrimitive.OnPlane T.D Delta) := by
    intro hDDelta
    exact T.D_off_Sigma4 (hDelta4 T.D hDDelta)

  have hD34 : Q.OnHyperplane T.D Lambda34 := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        T.Sigma3 T.Sigma4 Delta
        hDelta3 hDelta4
        T.C T.C_on_Sigma4

    have hr3C :
        hyperplaneReflect4_corrected Geo T.Sigma3 T.C = T.D := by
      simpa only [r3_apply] using r3_C (Geo := Geo) T

    simpa only [Lambda34, hr3C] using hImage

  have hD43 : Q.OnHyperplane T.D Lambda43 := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        T.Sigma4 T.Sigma3 Delta
        hDelta4 hDelta3
        T.E T.E_on_Sigma3

    have hr4E :
        hyperplaneReflect4_corrected Geo T.Sigma4 T.E = T.D := by
      simpa only [r4_apply] using r4_E (Geo := Geo) T

    simpa only [Lambda43, hr4E] using hImage

  have hCanon34 :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta T.D hDoffDelta =
        Lambda34 :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta T.D hDoffDelta
      Lambda34 hDelta34 hD34

  have hCanon43 :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta T.D hDoffDelta =
        Lambda43 :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta T.D hDoffDelta
      Lambda43 hDelta43 hD43

  change Lambda34 = Lambda43
  exact hCanon34.symm.trans hCanon43

/-- The second A4 braid relation holds globally on E4. -/
theorem braid23_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    r2 (Geo := Geo) T
        (r3 (Geo := Geo) T
          (r2 (Geo := Geo) T X)) =
      r3 (Geo := Geo) T
        (r2 (Geo := Geo) T
          (r3 (Geo := Geo) T X)) := by

  rcases braid23_reflected_mirrors_eq (Geo := Geo) T with
    ⟨Delta, hDelta2, hDelta3, hLambdaEq⟩

  let Lambda23 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma2 T.Sigma3 Delta hDelta2 hDelta3

  let Lambda32 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma3 T.Sigma2 Delta hDelta3 hDelta2

  have hMap23 :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma2 T.Sigma3 Lambda23 := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma2 T.Sigma3 Delta hDelta2 hDelta3

  have hMap32 :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma3 T.Sigma2 Lambda32 := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma3 T.Sigma2 Delta hDelta3 hDelta2

  have hLeft :
      hyperplaneReflect4_corrected Geo T.Sigma2
          (hyperplaneReflect4_corrected Geo T.Sigma3
            (hyperplaneReflect4_corrected Geo T.Sigma2 X)) =
        hyperplaneReflect4_corrected Geo Lambda23 X :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      T.Sigma2 T.Sigma3 Lambda23 hMap23 X

  have hRight :
      hyperplaneReflect4_corrected Geo T.Sigma3
          (hyperplaneReflect4_corrected Geo T.Sigma2
            (hyperplaneReflect4_corrected Geo T.Sigma3 X)) =
        hyperplaneReflect4_corrected Geo Lambda32 X :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      T.Sigma3 T.Sigma2 Lambda32 hMap32 X

  have hLambda : Lambda23 = Lambda32 := by
    simpa only [Lambda23, Lambda32] using hLambdaEq

  have hRaw :
      hyperplaneReflect4_corrected Geo T.Sigma2
          (hyperplaneReflect4_corrected Geo T.Sigma3
            (hyperplaneReflect4_corrected Geo T.Sigma2 X)) =
        hyperplaneReflect4_corrected Geo T.Sigma3
          (hyperplaneReflect4_corrected Geo T.Sigma2
            (hyperplaneReflect4_corrected Geo T.Sigma3 X)) := by
    calc
      hyperplaneReflect4_corrected Geo T.Sigma2
          (hyperplaneReflect4_corrected Geo T.Sigma3
            (hyperplaneReflect4_corrected Geo T.Sigma2 X))
          = hyperplaneReflect4_corrected Geo Lambda23 X := hLeft
      _ = hyperplaneReflect4_corrected Geo Lambda32 X := by rw [hLambda]
      _ = hyperplaneReflect4_corrected Geo T.Sigma3
          (hyperplaneReflect4_corrected Geo T.Sigma2
            (hyperplaneReflect4_corrected Geo T.Sigma3 X)) := hRight.symm

  simpa only [r2_apply, r3_apply] using hRaw

/-- The third A4 braid relation holds globally on E4. -/
theorem braid34_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    r3 (Geo := Geo) T
        (r4 (Geo := Geo) T
          (r3 (Geo := Geo) T X)) =
      r4 (Geo := Geo) T
        (r3 (Geo := Geo) T
          (r4 (Geo := Geo) T X)) := by

  rcases braid34_reflected_mirrors_eq (Geo := Geo) T with
    ⟨Delta, hDelta3, hDelta4, hLambdaEq⟩

  let Lambda34 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma3 T.Sigma4 Delta hDelta3 hDelta4

  let Lambda43 : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      T.Sigma4 T.Sigma3 Delta hDelta4 hDelta3

  have hMap34 :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma3 T.Sigma4 Lambda34 := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma3 T.Sigma4 Delta hDelta3 hDelta4

  have hMap43 :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma4 T.Sigma3 Lambda43 := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma4 T.Sigma3 Delta hDelta4 hDelta3

  have hLeft :
      hyperplaneReflect4_corrected Geo T.Sigma3
          (hyperplaneReflect4_corrected Geo T.Sigma4
            (hyperplaneReflect4_corrected Geo T.Sigma3 X)) =
        hyperplaneReflect4_corrected Geo Lambda34 X :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      T.Sigma3 T.Sigma4 Lambda34 hMap34 X

  have hRight :
      hyperplaneReflect4_corrected Geo T.Sigma4
          (hyperplaneReflect4_corrected Geo T.Sigma3
            (hyperplaneReflect4_corrected Geo T.Sigma4 X)) =
        hyperplaneReflect4_corrected Geo Lambda43 X :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      T.Sigma4 T.Sigma3 Lambda43 hMap43 X

  have hLambda : Lambda34 = Lambda43 := by
    simpa only [Lambda34, Lambda43] using hLambdaEq

  have hRaw :
      hyperplaneReflect4_corrected Geo T.Sigma3
          (hyperplaneReflect4_corrected Geo T.Sigma4
            (hyperplaneReflect4_corrected Geo T.Sigma3 X)) =
        hyperplaneReflect4_corrected Geo T.Sigma4
          (hyperplaneReflect4_corrected Geo T.Sigma3
            (hyperplaneReflect4_corrected Geo T.Sigma4 X)) := by
    calc
      hyperplaneReflect4_corrected Geo T.Sigma3
          (hyperplaneReflect4_corrected Geo T.Sigma4
            (hyperplaneReflect4_corrected Geo T.Sigma3 X))
          = hyperplaneReflect4_corrected Geo Lambda34 X := hLeft
      _ = hyperplaneReflect4_corrected Geo Lambda43 X := by rw [hLambda]
      _ = hyperplaneReflect4_corrected Geo T.Sigma4
          (hyperplaneReflect4_corrected Geo T.Sigma3
            (hyperplaneReflect4_corrected Geo T.Sigma4 X)) := hRight.symm

  simpa only [r3_apply, r4_apply] using hRaw

/-- All three adjacent A4 braid relations hold pointwise on E4. -/
theorem all_adjacent_braids_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    (r1 (Geo := Geo) T
        (r2 (Geo := Geo) T
          (r1 (Geo := Geo) T X)) =
      r2 (Geo := Geo) T
        (r1 (Geo := Geo) T
          (r2 (Geo := Geo) T X))) /\
    (r2 (Geo := Geo) T
        (r3 (Geo := Geo) T
          (r2 (Geo := Geo) T X)) =
      r3 (Geo := Geo) T
        (r2 (Geo := Geo) T
          (r3 (Geo := Geo) T X))) /\
    (r3 (Geo := Geo) T
        (r4 (Geo := Geo) T
          (r3 (Geo := Geo) T X)) =
      r4 (Geo := Geo) T
        (r3 (Geo := Geo) T
          (r4 (Geo := Geo) T X))) := by

  exact
    ⟨braid12_global_smith (Geo := Geo) T X,
      braid23_global_smith (Geo := Geo) T X,
      braid34_global_smith (Geo := Geo) T X⟩

end CoxeterA4SmithSimplexFrame

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: distant commutation relations

All three adjacent braid relations are already global in Test12.

For distant mirrors we use a simpler conjugation pattern.  If reflection
in Sigma preserves Tau setwise, then

  r_Sigma r_Tau r_Sigma = r_Tau,

and involutivity of r_Sigma immediately gives

  r_Sigma r_Tau = r_Tau r_Sigma.

The only E4 incidence input needed below is:

* two hyperplanes with one known common point have a common 2-plane;
* a reflected hyperplane containing that common plane and one additional
  point outside it is uniquely the original target hyperplane.

No finite-anchor rigidity and no ambient HilbertSpaceIncidence are used.
-/

/--
If two corrected E4 hyperplanes share one point F, then they contain a
common ambient 2-plane.  A second common point is obtained by intersecting
Tau with an internal plane of Sigma through F.
-/
theorem hilbert4D_two_hyperplanes_common_plane_through_one_point_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    (Sigma Tau : Q.Hyperplane)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hFSigma : Q.OnHyperplane F Sigma)
    (hFTau : Q.OnHyperplane F Tau)
    (hGSigma : Q.OnHyperplane G Sigma) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      HilbertPlaneInHyperplane4 Geo Delta Sigma /\
      HilbertPlaneInHyperplane4 Geo Delta Tau := by

  let Fp : HyperplanePoint4 Geo Sigma :=
    ⟨F, hFSigma⟩

  let Gp : HyperplanePoint4 Geo Sigma :=
    ⟨G, hGSigma⟩

  have hFpGp : Ne Fp Gp := by
    intro hEq
    apply hFG
    exact congrArg Subtype.val hEq

  rcases
      hyperplaneGeo4_plane_through_point_avoiding_point_corrected
        (Geo := Geo)
        Sigma Fp Gp hFpGp with
    ⟨pi, hFpi, _hGnotPi⟩

  rcases
      Hilbert4DPlaneHyperplaneIncidence.plane_hyperplane_second_common_point
        (Geo := Geo)
        pi.1 Tau
        F hFpi hFTau with
    ⟨C, hCF, hCpi, hCTau⟩

  have hCSigma :
      Q.OnHyperplane C Sigma :=
    pi.2 C hCpi

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
        (Geo := Geo)
        Sigma Tau
        F C
        hCF.symm
        hFSigma hCSigma
        hFTau hCTau with
    ⟨Delta, _hFDelta, _hCDelta, hDeltaSigma, hDeltaTau⟩

  exact ⟨Delta, hDeltaSigma, hDeltaTau⟩

/--
If a reflected target hyperplane contains the same common plane Delta as
Tau and one reflected source point lands at Y in Tau outside Delta, then
the reflected carrier is exactly Tau.
-/
theorem hyperplaneReflectionCarrier4_corrected_eq_self_of_image_point_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma : HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau : HilbertPlaneInHyperplane4 Geo Delta Tau)
    (X Y : Geo.Point)
    (hXTau : Q.OnHyperplane X Tau)
    (hYTau : Q.OnHyperplane Y Tau)
    (hYoffDelta : Not (Q.toHilbertSpacePrimitive.OnPlane Y Delta))
    (hXY : hyperplaneReflect4_corrected Geo Sigma X = Y) :
    hyperplaneReflectionCarrier4_corrected
        (Geo := Geo)
        Sigma Tau Delta hDeltaSigma hDeltaTau =
      Tau := by

  let Lambda : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      Sigma Tau Delta hDeltaSigma hDeltaTau

  have hDeltaLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda := by
    exact
      hyperplaneReflectionCarrier4_corrected_contains_common_plane
        (Geo := Geo)
        Sigma Tau Delta hDeltaSigma hDeltaTau

  have hYLambda :
      Q.OnHyperplane Y Lambda := by
    have hImage :=
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau
        X hXTau

    simpa only [Lambda, hXY] using hImage

  have hCanonLambda :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta Y hYoffDelta =
        Lambda :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta Y hYoffDelta
      Lambda hDeltaLambda hYLambda

  have hCanonTau :
      hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta Y hYoffDelta =
        Tau :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_eq
      (Geo := Geo)
      Delta Y hYoffDelta
      Tau hDeltaTau hYTau

  change Lambda = Tau
  exact hCanonLambda.symm.trans hCanonTau

/--
A corrected reflection commutes with reflection in Tau whenever it maps
Tau exactly to itself.
-/
theorem hyperplaneReflect4_corrected_commute_of_maps_self_smith
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
    (Sigma Tau : Q.Hyperplane)
    (hMap :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo Sigma Tau Tau)
    (X : Geo.Point) :
    hyperplaneReflect4_corrected Geo Sigma
        (hyperplaneReflect4_corrected Geo Tau X) =
      hyperplaneReflect4_corrected Geo Tau
        (hyperplaneReflect4_corrected Geo Sigma X) := by

  have hConj :=
    hyperplaneReflect4_corrected_conjugation_pointwise_smith
      (Geo := Geo)
      Sigma Tau Tau hMap
      (hyperplaneReflect4_corrected Geo Sigma X)

  simpa only [
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo) Sigma X
  ] using hConj

namespace CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/-- Reflection in Sigma1 preserves the distant mirror Sigma3. -/
theorem sigma13_reflection_preserves_sigma3
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      exists hDelta1 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma1,
        exists hDelta3 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma3,
          hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma1 T.Sigma3 Delta hDelta1 hDelta3 =
            T.Sigma3 := by

  have hCE : Ne T.C T.E := by
    intro hCE
    apply T.C_off_Sigma3
    rw [hCE]
    exact T.E_on_Sigma3

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_one_point_smith
        (Geo := Geo)
        T.Sigma1 T.Sigma3
        T.E T.C
        hCE.symm
        T.E_on_Sigma1 T.E_on_Sigma3 T.C_on_Sigma1 with
    ⟨Delta, hDelta1, hDelta3⟩

  refine ⟨Delta, hDelta1, hDelta3, ?_⟩

  have hAoffDelta :
      Not (Q.toHilbertSpacePrimitive.OnPlane T.A Delta) := by
    intro hADelta
    exact T.A_off_Sigma1 (hDelta1 T.A hADelta)

  have hr1B :
      hyperplaneReflect4_corrected Geo T.Sigma1 T.B = T.A := by
    simpa only [r1_apply] using r1_B (Geo := Geo) T

  exact
    hyperplaneReflectionCarrier4_corrected_eq_self_of_image_point_smith
      (Geo := Geo)
      T.Sigma1 T.Sigma3 Delta
      hDelta1 hDelta3
      T.B T.A
      T.B_on_Sigma3 T.A_on_Sigma3
      hAoffDelta hr1B

/-- Reflection in Sigma1 preserves the distant mirror Sigma4. -/
theorem sigma14_reflection_preserves_sigma4
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      exists hDelta1 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma1,
        exists hDelta4 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma4,
          hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma1 T.Sigma4 Delta hDelta1 hDelta4 =
            T.Sigma4 := by

  have hCE : Ne T.C T.E := by
    intro hCE
    apply T.C_off_Sigma3
    rw [hCE]
    exact T.E_on_Sigma3

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_one_point_smith
        (Geo := Geo)
        T.Sigma1 T.Sigma4
        T.C T.E
        hCE
        T.C_on_Sigma1 T.C_on_Sigma4 T.E_on_Sigma1 with
    ⟨Delta, hDelta1, hDelta4⟩

  refine ⟨Delta, hDelta1, hDelta4, ?_⟩

  have hAoffDelta :
      Not (Q.toHilbertSpacePrimitive.OnPlane T.A Delta) := by
    intro hADelta
    exact T.A_off_Sigma1 (hDelta1 T.A hADelta)

  have hr1B :
      hyperplaneReflect4_corrected Geo T.Sigma1 T.B = T.A := by
    simpa only [r1_apply] using r1_B (Geo := Geo) T

  exact
    hyperplaneReflectionCarrier4_corrected_eq_self_of_image_point_smith
      (Geo := Geo)
      T.Sigma1 T.Sigma4 Delta
      hDelta1 hDelta4
      T.B T.A
      T.B_on_Sigma4 T.A_on_Sigma4
      hAoffDelta hr1B

/-- Reflection in Sigma2 preserves the distant mirror Sigma4. -/
theorem sigma24_reflection_preserves_sigma4
    (T : CoxeterA4SmithSimplexFrame Geo) :
    exists Delta : Q.toHilbertSpacePrimitive.Plane,
      exists hDelta2 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma2,
        exists hDelta4 : HilbertPlaneInHyperplane4 Geo Delta T.Sigma4,
          hyperplaneReflectionCarrier4_corrected
              (Geo := Geo)
              T.Sigma2 T.Sigma4 Delta hDelta2 hDelta4 =
            T.Sigma4 := by

  have hAD : Ne T.A T.D := by
    intro hAD
    apply T.D_off_Sigma4
    rw [← hAD]
    exact T.A_on_Sigma4

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_one_point_smith
        (Geo := Geo)
        T.Sigma2 T.Sigma4
        T.A T.D
        hAD
        T.A_on_Sigma2 T.A_on_Sigma4 T.D_on_Sigma2 with
    ⟨Delta, hDelta2, hDelta4⟩

  refine ⟨Delta, hDelta2, hDelta4, ?_⟩

  have hBoffDelta :
      Not (Q.toHilbertSpacePrimitive.OnPlane T.B Delta) := by
    intro hBDelta
    exact T.B_off_Sigma2 (hDelta2 T.B hBDelta)

  have hr2C :
      hyperplaneReflect4_corrected Geo T.Sigma2 T.C = T.B := by
    simpa only [r2_apply] using r2_C (Geo := Geo) T

  exact
    hyperplaneReflectionCarrier4_corrected_eq_self_of_image_point_smith
      (Geo := Geo)
      T.Sigma2 T.Sigma4 Delta
      hDelta2 hDelta4
      T.C T.B
      T.C_on_Sigma4 T.B_on_Sigma4
      hBoffDelta hr2C

/-- The distant generators r1 and r3 commute globally on E4. -/
theorem commute13_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    r1 (Geo := Geo) T (r3 (Geo := Geo) T X) =
      r3 (Geo := Geo) T (r1 (Geo := Geo) T X) := by

  rcases sigma13_reflection_preserves_sigma3 (Geo := Geo) T with
    ⟨Delta, hDelta1, hDelta3, hCarrierEq⟩

  have hMapCarrier :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma1 T.Sigma3
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          T.Sigma1 T.Sigma3 Delta hDelta1 hDelta3) := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma1 T.Sigma3 Delta hDelta1 hDelta3

  have hMapSelf :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma1 T.Sigma3 T.Sigma3 := by
    simpa only [hCarrierEq] using hMapCarrier

  have hRaw :=
    hyperplaneReflect4_corrected_commute_of_maps_self_smith
      (Geo := Geo)
      T.Sigma1 T.Sigma3 hMapSelf X

  simpa only [r1_apply, r3_apply] using hRaw

/-- The distant generators r1 and r4 commute globally on E4. -/
theorem commute14_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    r1 (Geo := Geo) T (r4 (Geo := Geo) T X) =
      r4 (Geo := Geo) T (r1 (Geo := Geo) T X) := by

  rcases sigma14_reflection_preserves_sigma4 (Geo := Geo) T with
    ⟨Delta, hDelta1, hDelta4, hCarrierEq⟩

  have hMapCarrier :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma1 T.Sigma4
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          T.Sigma1 T.Sigma4 Delta hDelta1 hDelta4) := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma1 T.Sigma4 Delta hDelta1 hDelta4

  have hMapSelf :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma1 T.Sigma4 T.Sigma4 := by
    simpa only [hCarrierEq] using hMapCarrier

  have hRaw :=
    hyperplaneReflect4_corrected_commute_of_maps_self_smith
      (Geo := Geo)
      T.Sigma1 T.Sigma4 hMapSelf X

  simpa only [r1_apply, r4_apply] using hRaw

/-- The distant generators r2 and r4 commute globally on E4. -/
theorem commute24_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    r2 (Geo := Geo) T (r4 (Geo := Geo) T X) =
      r4 (Geo := Geo) T (r2 (Geo := Geo) T X) := by

  rcases sigma24_reflection_preserves_sigma4 (Geo := Geo) T with
    ⟨Delta, hDelta2, hDelta4, hCarrierEq⟩

  have hMapCarrier :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma2 T.Sigma4
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          T.Sigma2 T.Sigma4 Delta hDelta2 hDelta4) := by
    exact
      hyperplaneReflectionCarrier4_corrected_maps
        (Geo := Geo)
        T.Sigma2 T.Sigma4 Delta hDelta2 hDelta4

  have hMapSelf :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo T.Sigma2 T.Sigma4 T.Sigma4 := by
    simpa only [hCarrierEq] using hMapCarrier

  have hRaw :=
    hyperplaneReflect4_corrected_commute_of_maps_self_smith
      (Geo := Geo)
      T.Sigma2 T.Sigma4 hMapSelf X

  simpa only [r2_apply, r4_apply] using hRaw

/-- All three distant A4 commutation relations hold pointwise on E4. -/
theorem all_distant_commutations_global_smith
    (T : CoxeterA4SmithSimplexFrame Geo)
    (X : Geo.Point) :
    (r1 (Geo := Geo) T (r3 (Geo := Geo) T X) =
      r3 (Geo := Geo) T (r1 (Geo := Geo) T X)) /\
    (r1 (Geo := Geo) T (r4 (Geo := Geo) T X) =
      r4 (Geo := Geo) T (r1 (Geo := Geo) T X)) /\
    (r2 (Geo := Geo) T (r4 (Geo := Geo) T X) =
      r4 (Geo := Geo) T (r2 (Geo := Geo) T X)) := by

  exact
    ⟨commute13_global_smith (Geo := Geo) T X,
      commute14_global_smith (Geo := Geo) T X,
      commute24_global_smith (Geo := Geo) T X⟩

end CoxeterA4SmithSimplexFrame

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A4 Smith restart: global Equiv presentation

Tests11-13 established all A4 relations pointwise on the corrected,
dimension-free E4 stack.  This file packages them as equalities of ambient
point equivalences.

The resulting presentation is

  r1^2 = r2^2 = r3^2 = r4^2 = 1,

  r1 r2 r1 = r2 r1 r2,
  r2 r3 r2 = r3 r2 r3,
  r3 r4 r3 = r4 r3 r4,

  r1 r3 = r3 r1,
  r1 r4 = r4 r1,
  r2 r4 = r4 r2.

No finite-anchor rigidity and no ambient HilbertSpaceIncidence are used.
-/

namespace CoxeterA4SmithSimplexFrame

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]

/- The first corrected A4 generator is an involution as an ambient Equiv. -/
omit [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientEuclidean Geo] in
theorem r1_sq_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r1 (Geo := Geo) T).trans (r1 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by
  simpa only [r1] using
    (hyperplaneReflectionEquiv4_corrected_sq_smith
      (Geo := Geo) T.Sigma1)

/- The second corrected A4 generator is an involution as an ambient Equiv. -/
omit [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientEuclidean Geo] in
theorem r2_sq_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r2 (Geo := Geo) T).trans (r2 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by
  simpa only [r2] using
    (hyperplaneReflectionEquiv4_corrected_sq_smith
      (Geo := Geo) T.Sigma2)

/- The third corrected A4 generator is an involution as an ambient Equiv. -/
omit [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientEuclidean Geo] in
theorem r3_sq_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r3 (Geo := Geo) T).trans (r3 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by
  simpa only [r3] using
    (hyperplaneReflectionEquiv4_corrected_sq_smith
      (Geo := Geo) T.Sigma3)

/- The fourth corrected A4 generator is an involution as an ambient Equiv. -/
omit [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientEuclidean Geo] in
theorem r4_sq_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r4 (Geo := Geo) T).trans (r4 (Geo := Geo) T) =
      Equiv.refl Geo.Point := by
  simpa only [r4] using
    (hyperplaneReflectionEquiv4_corrected_sq_smith
      (Geo := Geo) T.Sigma4)

/-- First adjacent braid as equality of ambient Equiv's. -/
theorem braid12_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    ((r1 (Geo := Geo) T).trans (r2 (Geo := Geo) T)).trans
        (r1 (Geo := Geo) T) =
      ((r2 (Geo := Geo) T).trans (r1 (Geo := Geo) T)).trans
        (r2 (Geo := Geo) T) := by
  apply Equiv.ext
  intro X
  change
    r1 (Geo := Geo) T
        (r2 (Geo := Geo) T
          (r1 (Geo := Geo) T X)) =
      r2 (Geo := Geo) T
        (r1 (Geo := Geo) T
          (r2 (Geo := Geo) T X))
  exact braid12_global_smith (Geo := Geo) T X

/-- Second adjacent braid as equality of ambient Equiv's. -/
theorem braid23_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    ((r2 (Geo := Geo) T).trans (r3 (Geo := Geo) T)).trans
        (r2 (Geo := Geo) T) =
      ((r3 (Geo := Geo) T).trans (r2 (Geo := Geo) T)).trans
        (r3 (Geo := Geo) T) := by
  apply Equiv.ext
  intro X
  change
    r2 (Geo := Geo) T
        (r3 (Geo := Geo) T
          (r2 (Geo := Geo) T X)) =
      r3 (Geo := Geo) T
        (r2 (Geo := Geo) T
          (r3 (Geo := Geo) T X))
  exact braid23_global_smith (Geo := Geo) T X

/-- Third adjacent braid as equality of ambient Equiv's. -/
theorem braid34_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    ((r3 (Geo := Geo) T).trans (r4 (Geo := Geo) T)).trans
        (r3 (Geo := Geo) T) =
      ((r4 (Geo := Geo) T).trans (r3 (Geo := Geo) T)).trans
        (r4 (Geo := Geo) T) := by
  apply Equiv.ext
  intro X
  change
    r3 (Geo := Geo) T
        (r4 (Geo := Geo) T
          (r3 (Geo := Geo) T X)) =
      r4 (Geo := Geo) T
        (r3 (Geo := Geo) T
          (r4 (Geo := Geo) T X))
  exact braid34_global_smith (Geo := Geo) T X

/-- Distant generators r1 and r3 commute as ambient Equiv's. -/
theorem commute13_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r1 (Geo := Geo) T).trans (r3 (Geo := Geo) T) =
      (r3 (Geo := Geo) T).trans (r1 (Geo := Geo) T) := by
  apply Equiv.ext
  intro X
  change
    r3 (Geo := Geo) T (r1 (Geo := Geo) T X) =
      r1 (Geo := Geo) T (r3 (Geo := Geo) T X)
  exact (commute13_global_smith (Geo := Geo) T X).symm

/-- Distant generators r1 and r4 commute as ambient Equiv's. -/
theorem commute14_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r1 (Geo := Geo) T).trans (r4 (Geo := Geo) T) =
      (r4 (Geo := Geo) T).trans (r1 (Geo := Geo) T) := by
  apply Equiv.ext
  intro X
  change
    r4 (Geo := Geo) T (r1 (Geo := Geo) T X) =
      r1 (Geo := Geo) T (r4 (Geo := Geo) T X)
  exact (commute14_global_smith (Geo := Geo) T X).symm

/-- Distant generators r2 and r4 commute as ambient Equiv's. -/
theorem commute24_equiv_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    (r2 (Geo := Geo) T).trans (r4 (Geo := Geo) T) =
      (r4 (Geo := Geo) T).trans (r2 (Geo := Geo) T) := by
  apply Equiv.ext
  intro X
  change
    r4 (Geo := Geo) T (r2 (Geo := Geo) T X) =
      r2 (Geo := Geo) T (r4 (Geo := Geo) T X)
  exact (commute24_global_smith (Geo := Geo) T X).symm

/--
A compact proposition packaging the complete global Coxeter A4 presentation
for the four corrected E4 hyperplane reflections.
-/
structure CoxeterA4GlobalRelations
    (T : CoxeterA4SmithSimplexFrame Geo) : Prop where
  sq1 :
    (r1 (Geo := Geo) T).trans (r1 (Geo := Geo) T) =
      Equiv.refl Geo.Point
  sq2 :
    (r2 (Geo := Geo) T).trans (r2 (Geo := Geo) T) =
      Equiv.refl Geo.Point
  sq3 :
    (r3 (Geo := Geo) T).trans (r3 (Geo := Geo) T) =
      Equiv.refl Geo.Point
  sq4 :
    (r4 (Geo := Geo) T).trans (r4 (Geo := Geo) T) =
      Equiv.refl Geo.Point
  braid12 :
    ((r1 (Geo := Geo) T).trans (r2 (Geo := Geo) T)).trans
        (r1 (Geo := Geo) T) =
      ((r2 (Geo := Geo) T).trans (r1 (Geo := Geo) T)).trans
        (r2 (Geo := Geo) T)
  braid23 :
    ((r2 (Geo := Geo) T).trans (r3 (Geo := Geo) T)).trans
        (r2 (Geo := Geo) T) =
      ((r3 (Geo := Geo) T).trans (r2 (Geo := Geo) T)).trans
        (r3 (Geo := Geo) T)
  braid34 :
    ((r3 (Geo := Geo) T).trans (r4 (Geo := Geo) T)).trans
        (r3 (Geo := Geo) T) =
      ((r4 (Geo := Geo) T).trans (r3 (Geo := Geo) T)).trans
        (r4 (Geo := Geo) T)
  commute13 :
    (r1 (Geo := Geo) T).trans (r3 (Geo := Geo) T) =
      (r3 (Geo := Geo) T).trans (r1 (Geo := Geo) T)
  commute14 :
    (r1 (Geo := Geo) T).trans (r4 (Geo := Geo) T) =
      (r4 (Geo := Geo) T).trans (r1 (Geo := Geo) T)
  commute24 :
    (r2 (Geo := Geo) T).trans (r4 (Geo := Geo) T) =
      (r4 (Geo := Geo) T).trans (r2 (Geo := Geo) T)

/-- The corrected Smith/Wyler E4 simplex frame satisfies the full A4 presentation. -/
theorem coxeter_A4_global_relations_smith
    (T : CoxeterA4SmithSimplexFrame Geo) :
    CoxeterA4GlobalRelations (Geo := Geo) T := by
  exact
    { sq1 := r1_sq_equiv_smith (Geo := Geo) T
      sq2 := r2_sq_equiv_smith (Geo := Geo) T
      sq3 := r3_sq_equiv_smith (Geo := Geo) T
      sq4 := r4_sq_equiv_smith (Geo := Geo) T
      braid12 := braid12_equiv_smith (Geo := Geo) T
      braid23 := braid23_equiv_smith (Geo := Geo) T
      braid34 := braid34_equiv_smith (Geo := Geo) T
      commute13 := commute13_equiv_smith (Geo := Geo) T
      commute14 := commute14_equiv_smith (Geo := Geo) T
      commute24 := commute24_equiv_smith (Geo := Geo) T }

end CoxeterA4SmithSimplexFrame

end Geometry


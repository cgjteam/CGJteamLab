import CGJteamLab.HilbertAxioms

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]

/-!
# HilbertGrundlagen

Self-contained extraction of the material in `HilbertInterface` tied
explicitly to Hilbert's *Grundlagen der Geometrie*, Chapter IV, sec. 18.

This file imports only `CGJteamLab.HilbertAxioms`.

The four declarations collected first are the minimal local prerequisites
from `HilbertInterface` needed by the Grundlagen block itself.
-/

------------------------------------------------------------------------
-- Local prerequisites
------------------------------------------------------------------------

abbrev Collinear
    (A B C : Geo.Point) : Prop :=
  PrimCollinear Geo A B C


/--
Symmetry of segment congruence, derived from Hilbert III.1--III.2 as
described immediately after III.2 in the second English edition.
-/
theorem CongruentSymmetry
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D ->
    Geo.Congruent C D A B := by
  exact hilbert_congruent_symmetry Geo A B C D


structure TriangleCongruenceResult
    (A B C D E F : Geo.Point) where
  sideAB : Geo.Congruent A B D E
  sideBC : Geo.Congruent B C E F
  sideAC : Geo.Congruent A C D F
  angleA : Geo.AngleCongruent B A C E D F
  angleB : Geo.AngleCongruent A B C D E F
  angleC : Geo.AngleCongruent A C B D F E


/--
If A-B-D and C is not on line AD, then A and B lie on the same
side of line CD.

This is a pure incidence/order fact.
-/
theorem hilbert_between_points_sameSide_transversal
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hNC : ¬ PrimCollinear Geo A D C) :
    ∃ l : Geo.Line,
      HilbertIncidence.OnLine C l ∧
      HilbertIncidence.OnLine D l ∧
      HilbertSameSide Geo A B l := by

  have hAD : A ≠ D :=
    (HilbertOrder.between_incidence A B D hABD).2.2.1

  have hCD : C ≠ D := by
    intro hCD
    subst C
    apply hNC
    rcases HilbertPlaneIncidence.line_through A D hAD with
      ⟨l, hAl, hDl⟩
    exact PrimCollinear.mk (Geo := Geo) hAl hDl hDl

  rcases HilbertPlaneIncidence.line_through A D hAD with
    ⟨base, hAbase, hDbase⟩

  rcases HilbertPlaneIncidence.line_through C D hCD with
    ⟨cross, hCcross, hDcross⟩

  have hBbase : HilbertIncidence.OnLine B base :=
    hilbert_between_on_line
      Geo A B D base hAbase hDbase hABD

  have hLines : base ≠ cross := by
    intro hEq
    subst cross
    apply hNC
    exact PrimCollinear.mk
      (Geo := Geo) hAbase hDbase hCcross

  have hAnotcross :
      ¬ HilbertIncidence.OnLine A cross := by
    intro hAcross

    have hEq : base = cross :=
      HilbertPlaneIncidence.line_unique
        A D hAD
        base cross
        hAbase hDbase
        hAcross hDcross

    exact hLines hEq

  have hBD : B ≠ D :=
    (HilbertOrder.between_incidence A B D hABD).2.1

  have hBnotcross :
      ¬ HilbertIncidence.OnLine B cross := by
    intro hBcross

    have hEq : base = cross :=
      HilbertPlaneIncidence.line_unique
        B D hBD
        base cross
        hBbase hDbase
        hBcross hDcross

    exact hLines hEq

  have hABDcol : PrimCollinear Geo A B D :=
    (HilbertOrder.between_incidence
      A B D hABD).2.2.2.1

  have hNotBetween : ¬ Geo.Between A D B :=
    (HilbertOrder.between_unique
      A B D hABDcol hABD).2

  have hNoMeet :
      ¬ HilbertSegmentMeetsLine Geo A B cross :=
    hilbert_segment_not_meets_crossing_line
      Geo
      A B D
      base cross
      hLines
      hAbase
      hBbase
      hDbase
      hDcross
      hNotBetween

  have hSame : HilbertSameSide Geo A B cross := by
    exact
      ⟨hAnotcross,
       hBnotcross,
       Relation.ReflTransGen.single
         ⟨hAnotcross, hBnotcross, hNoMeet⟩⟩

  exact ⟨cross, hCcross, hDcross, hSame⟩


-- Part X. Equidecomposability and Equicomplementability
------------------------------------------------------------------------
-- Reference: Hilbert, Grundlagen der Geometrie,
-- Chapter IV, sec. 18.
--

structure HilbertTriangle
    (Geo : Geometry.Geo) where
  A : Geo.Point
  B : Geo.Point
  C : Geo.Point


def HilbertTriangleCongruent
    [HilbertCongruence Geo]
    (T U : HilbertTriangle Geo) : Prop :=
  TriangleCongruenceResult
    Geo
    T.A T.B T.C
    U.A U.B U.C


abbrev HilbertTriangulatedFigure
    (Geo : Geometry.Geo) :=
  List (HilbertTriangle Geo)

/--
Two triangulations represent the same polygonal figure.

The basic move subdivides one triangle ABC by choosing a point X
between B and C and replacing ABC by the two triangles ABX and AXC.
The relation is closed under symmetry and transitivity.
-/
inductive HilbertSameFigure
    [HilbertOrder Geo] :
    HilbertTriangulatedFigure Geo →
    HilbertTriangulatedFigure Geo →
    Prop

  | refl
      (P : HilbertTriangulatedFigure Geo) :
      HilbertSameFigure P P

  | split
      (L R : HilbertTriangulatedFigure Geo)
      (A B C X : Geo.Point)
      (hBXC : Geo.Between B X C) :
      HilbertSameFigure
        (L ++ [⟨A, B, C⟩] ++ R)
        (L ++ [⟨A, B, X⟩, ⟨A, X, C⟩] ++ R)

  | triangleSwapFirst
      (L R : HilbertTriangulatedFigure Geo)
      (A B C : Geo.Point) :
      HilbertSameFigure
        (L ++ [⟨A, B, C⟩] ++ R)
        (L ++ [⟨B, A, C⟩] ++ R)

  | triangleSwapLast
      (L R : HilbertTriangulatedFigure Geo)
      (A B C : Geo.Point) :
      HilbertSameFigure
        (L ++ [⟨A, B, C⟩] ++ R)
        (L ++ [⟨A, C, B⟩] ++ R)

  | symm
      {P Q : HilbertTriangulatedFigure Geo}
      (h : HilbertSameFigure P Q) :
      HilbertSameFigure Q P

  | trans
      {P Q R : HilbertTriangulatedFigure Geo}
      (hPQ : HilbertSameFigure P Q)
      (hQR : HilbertSameFigure Q R) :
      HilbertSameFigure P R

inductive HilbertTriangleListCongruent
    [HilbertCongruence Geo] :
    HilbertTriangulatedFigure Geo →
    HilbertTriangulatedFigure Geo →
    Prop
  | nil :
      HilbertTriangleListCongruent [] []
  | cons
      {T U : HilbertTriangle Geo}
      {P Q : HilbertTriangulatedFigure Geo}
      (hTU : HilbertTriangleCongruent Geo T U)
      (hPQ : HilbertTriangleListCongruent P Q) :
      HilbertTriangleListCongruent (T :: P) (U :: Q)

def HilbertEquidecomposable
    [HilbertCongruence Geo]
    (P Q : HilbertTriangulatedFigure Geo) : Prop :=
  ∃ Q' : HilbertTriangulatedFigure Geo,
    Q'.Perm Q ∧
    HilbertTriangleListCongruent Geo P Q'

/--
Hilbert equidecomposability of polygonal figures.

The representatives P and Q may first be replaced by arbitrary
triangulations P' and Q' of the same respective figures.  The resulting
triangulations must then consist of pairwise congruent triangles,
up to permutation.
-/
inductive HilbertFigureEquidecomposable
    [HilbertCongruence Geo] :
    HilbertTriangulatedFigure Geo ->
    HilbertTriangulatedFigure Geo ->
    Prop

  | sameFigure
      {P Q : HilbertTriangulatedFigure Geo}
      (h : HilbertSameFigure Geo P Q) :
      HilbertFigureEquidecomposable P Q

  | congruentTriangulations
      {P Q : HilbertTriangulatedFigure Geo}
      (h : HilbertEquidecomposable Geo P Q) :
      HilbertFigureEquidecomposable P Q

  | symm
      {P Q : HilbertTriangulatedFigure Geo}
      (h : HilbertFigureEquidecomposable P Q) :
      HilbertFigureEquidecomposable Q P

  | trans
      {P Q R : HilbertTriangulatedFigure Geo}
      (hPQ : HilbertFigureEquidecomposable P Q)
      (hQR : HilbertFigureEquidecomposable Q R) :
      HilbertFigureEquidecomposable P R



theorem hilbert_singleton_equidecomposable
    [HilbertCongruence Geo]
    (T U : HilbertTriangle Geo)
    (hTU : HilbertTriangleCongruent Geo T U) :
    HilbertEquidecomposable Geo [T] [U] := by

  refine ⟨[U], ?_, ?_⟩

  · exact List.Perm.refl [U]

  · exact
      HilbertTriangleListCongruent.cons
        hTU
        HilbertTriangleListCongruent.nil

theorem hilbert_triangleListCongruent_append
    [HilbertCongruence Geo]
    {P₁ P₂ Q₁ Q₂ : HilbertTriangulatedFigure Geo}
    (h₁ : HilbertTriangleListCongruent Geo P₁ Q₁)
    (h₂ : HilbertTriangleListCongruent Geo P₂ Q₂) :
    HilbertTriangleListCongruent Geo
      (P₁ ++ P₂) (Q₁ ++ Q₂) := by

  induction h₁ with
  | nil =>
      simpa using h₂

  | cons hTU hPQ ih =>
      exact
        HilbertTriangleListCongruent.cons
          hTU
          ih

theorem hilbert_equidecomposable_append
    [HilbertCongruence Geo]
    {P₁ P₂ Q₁ Q₂ : HilbertTriangulatedFigure Geo}
    (h₁ : HilbertEquidecomposable Geo P₁ Q₁)
    (h₂ : HilbertEquidecomposable Geo P₂ Q₂) :
    HilbertEquidecomposable Geo
      (P₁ ++ P₂) (Q₁ ++ Q₂) := by

  rcases h₁ with ⟨Q₁', hPerm₁, hCong₁⟩
  rcases h₂ with ⟨Q₂', hPerm₂, hCong₂⟩

  refine ⟨Q₁' ++ Q₂', ?_, ?_⟩

  · exact hPerm₁.append hPerm₂

  · exact
      hilbert_triangleListCongruent_append
        Geo hCong₁ hCong₂

theorem hilbert_triangleCongruent_symm
    [HilbertCongruence Geo]
    {T U : HilbertTriangle Geo}
    (hTU : HilbertTriangleCongruent Geo T U) :
    HilbertTriangleCongruent Geo U T := by

  rcases hTU with
    ⟨hAB, hBC, hAC, hA, hB, hC⟩

  exact
    {
      sideAB := CongruentSymmetry Geo _ _ _ _ hAB
      sideBC := CongruentSymmetry Geo _ _ _ _ hBC
      sideAC := CongruentSymmetry Geo _ _ _ _ hAC
      angleA :=
        Geometry.Geo.angle_congruent_symmetry
          Geo _ _ _ _ _ _ hA
      angleB :=
        Geometry.Geo.angle_congruent_symmetry
          Geo _ _ _ _ _ _ hB
      angleC :=
        Geometry.Geo.angle_congruent_symmetry
          Geo _ _ _ _ _ _ hC
    }

theorem hilbert_triangleListCongruent_symm
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertTriangleListCongruent Geo P Q) :
    HilbertTriangleListCongruent Geo Q P := by

  induction hPQ with
  | nil =>
      exact HilbertTriangleListCongruent.nil

  | cons hTU hPQ ih =>
      exact
        HilbertTriangleListCongruent.cons
          (hilbert_triangleCongruent_symm Geo hTU)
          ih

theorem hilbert_triangleListCongruent_perm_right
    [HilbertCongruence Geo]
    {P Q Q' : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertTriangleListCongruent Geo P Q)
    (hPerm : Q.Perm Q') :
    ∃ P' : HilbertTriangulatedFigure Geo,
      P'.Perm P ∧
      HilbertTriangleListCongruent Geo P' Q' := by

  induction hPerm generalizing P with
  | nil =>
      cases hPQ
      exact ⟨[], List.Perm.refl [], HilbertTriangleListCongruent.nil⟩

  | cons x hPerm ih =>
      cases hPQ with
      | cons hTU hTail =>
          rcases ih hTail with ⟨P', hPperm, hCong⟩
          exact
            ⟨_ :: P',
              List.Perm.cons _ hPperm,
              HilbertTriangleListCongruent.cons hTU hCong⟩

  | swap x y l =>
      cases hPQ with
      | cons hx hRest =>
          cases hRest with
          | cons hy hTail =>
              exact
                ⟨_ :: _ :: _,
                  List.Perm.swap _ _ _,
                  HilbertTriangleListCongruent.cons
                    hy
                    (HilbertTriangleListCongruent.cons hx hTail)⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ hPQ with ⟨P₁, hPerm₁, hCong₁⟩
      rcases ih₂ hCong₁ with ⟨P₂, hPerm₂, hCong₂⟩
      exact
        ⟨P₂,
          hPerm₂.trans hPerm₁,
          hCong₂⟩

theorem hilbert_equidecomposable_symm
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertEquidecomposable Geo P Q) :
    HilbertEquidecomposable Geo Q P := by

  rcases hPQ with ⟨Q', hPerm, hCong⟩

  rcases
      hilbert_triangleListCongruent_perm_right
        Geo hCong hPerm
    with ⟨P', hPperm, hCong'⟩

  exact
    ⟨P',
      hPperm,
      hilbert_triangleListCongruent_symm Geo hCong'⟩

theorem hilbert_triangleCongruent_trans
    [HilbertCongruence Geo]
    {T U V : HilbertTriangle Geo}
    (hTU : HilbertTriangleCongruent Geo T U)
    (hUV : HilbertTriangleCongruent Geo U V) :
    HilbertTriangleCongruent Geo T V := by

  rcases hTU with
    ⟨hAB₁, hBC₁, hAC₁, hA₁, hB₁, hC₁⟩

  rcases hUV with
    ⟨hAB₂, hBC₂, hAC₂, hA₂, hB₂, hC₂⟩

  exact
    {
      sideAB :=
        hilbert_congruent_transitivity
          Geo _ _ _ _ _ _ hAB₁ hAB₂

      sideBC :=
        hilbert_congruent_transitivity
          Geo _ _ _ _ _ _ hBC₁ hBC₂

      sideAC :=
        hilbert_congruent_transitivity
          Geo _ _ _ _ _ _ hAC₁ hAC₂

      angleA :=
        Geometry.Geo.angle_congruent_transitivity
          Geo _ _ _ _ _ _ _ _ _
          hA₁ hA₂

      angleB :=
        Geometry.Geo.angle_congruent_transitivity
          Geo _ _ _ _ _ _ _ _ _
          hB₁ hB₂

      angleC :=
        Geometry.Geo.angle_congruent_transitivity
          Geo _ _ _ _ _ _ _ _ _
          hC₁ hC₂
    }

theorem hilbert_triangleListCongruent_trans
    [HilbertCongruence Geo]
    {P Q R : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertTriangleListCongruent Geo P Q)
    (hQR : HilbertTriangleListCongruent Geo Q R) :
    HilbertTriangleListCongruent Geo P R := by

  induction hPQ generalizing R with
  | nil =>
      cases hQR
      exact HilbertTriangleListCongruent.nil

  | cons hTU hPQ ih =>
      cases hQR with
      | cons hUV hQR =>
          exact
            HilbertTriangleListCongruent.cons
              (hilbert_triangleCongruent_trans
                Geo hTU hUV)
              (ih hQR)

theorem hilbert_equidecomposable_trans
    [HilbertCongruence Geo]
    {P Q R : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertEquidecomposable Geo P Q)
    (hQR : HilbertEquidecomposable Geo Q R) :
    HilbertEquidecomposable Geo P R := by

  rcases hPQ with
    ⟨Q', hQperm, hPQcong⟩

  rcases hQR with
    ⟨R', hRperm, hQRcong⟩

  have hRQcong :
      HilbertTriangleListCongruent Geo R' Q :=
    hilbert_triangleListCongruent_symm
      Geo hQRcong

  rcases
      hilbert_triangleListCongruent_perm_right
        Geo
        hRQcong
        hQperm.symm
    with
    ⟨R'', hR''perm, hR''Q'cong⟩

  have hQ'R''cong :
      HilbertTriangleListCongruent Geo Q' R'' :=
    hilbert_triangleListCongruent_symm
      Geo hR''Q'cong

  have hPR''cong :
      HilbertTriangleListCongruent Geo P R'' :=
    hilbert_triangleListCongruent_trans
      Geo
      hPQcong
      hQ'R''cong

  have hR''R :
      R''.Perm R :=
    hR''perm.trans hRperm

  exact
    ⟨R'', hR''R, hPR''cong⟩


theorem hilbert_triangleCongruent_refl
    [HilbertCongruence Geo]
    (T : HilbertTriangle Geo) :
    HilbertTriangleCongruent Geo T T := by

  exact
    {
      sideAB := hilbert_congruent_reflexive Geo T.A T.B
      sideBC := hilbert_congruent_reflexive Geo T.B T.C
      sideAC := hilbert_congruent_reflexive Geo T.A T.C
      angleA := Geometry.Geo.angle_congruent_reflexive Geo T.B T.A T.C
      angleB := Geometry.Geo.angle_congruent_reflexive Geo T.A T.B T.C
      angleC := Geometry.Geo.angle_congruent_reflexive Geo T.A T.C T.B
    }

theorem hilbert_equidecomposable_refl
    [HilbertCongruence Geo]
    (P : HilbertTriangulatedFigure Geo) :
    HilbertEquidecomposable Geo P P := by

  refine ⟨P, List.Perm.refl P, ?_⟩

  induction P with
  | nil =>
      exact HilbertTriangleListCongruent.nil

  | cons T P ih =>
      exact
        HilbertTriangleListCongruent.cons
          (hilbert_triangleCongruent_refl Geo T)
          ih


theorem hilbert_figureEquidecomposable_refl
    [HilbertCongruence Geo]
    (P : HilbertTriangulatedFigure Geo) :
    HilbertFigureEquidecomposable Geo P P := by

  exact
    HilbertFigureEquidecomposable.sameFigure
      (HilbertSameFigure.refl P)


theorem hilbert_figureEquidecomposable_symm
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertFigureEquidecomposable Geo P Q) :
    HilbertFigureEquidecomposable Geo Q P := by

  exact
    HilbertFigureEquidecomposable.symm hPQ


theorem hilbert_figureEquidecomposable_trans
    [HilbertCongruence Geo]
    {P Q R : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertFigureEquidecomposable Geo P Q)
    (hQR : HilbertFigureEquidecomposable Geo Q R) :
    HilbertFigureEquidecomposable Geo P R := by

  exact
    HilbertFigureEquidecomposable.trans hPQ hQR


theorem hilbert_sameFigure_append_right
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertSameFigure Geo P Q)
    (R : HilbertTriangulatedFigure Geo) :
    HilbertSameFigure Geo (P ++ R) (Q ++ R) := by

  induction hPQ with
  | refl P =>
      exact HilbertSameFigure.refl (P ++ R)

  | split L S A B C X hBXC =>
      simpa [List.append_assoc] using
        (HilbertSameFigure.split
          L (S ++ R) A B C X hBXC)

  | triangleSwapFirst L S A B C =>
      simpa [List.append_assoc] using
        (HilbertSameFigure.triangleSwapFirst
          L (S ++ R) A B C)

  | triangleSwapLast L S A B C =>
      simpa [List.append_assoc] using
        (HilbertSameFigure.triangleSwapLast
          L (S ++ R) A B C)

  | symm h ih =>
      exact HilbertSameFigure.symm ih

  | trans hPQ hQS ihPQ ihQS =>
      exact HilbertSameFigure.trans ihPQ ihQS


theorem hilbert_sameFigure_append_left
    [HilbertCongruence Geo]
    (L : HilbertTriangulatedFigure Geo)
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertSameFigure Geo P Q) :
    HilbertSameFigure Geo (L ++ P) (L ++ Q) := by

  induction hPQ with
  | refl P =>
      exact HilbertSameFigure.refl (L ++ P)

  | split M R A B C X hBXC =>
      simpa [List.append_assoc] using
        (HilbertSameFigure.split
          (L ++ M) R A B C X hBXC)

  | triangleSwapFirst M R A B C =>
      simpa [List.append_assoc] using
        (HilbertSameFigure.triangleSwapFirst
          (L ++ M) R A B C)

  | triangleSwapLast M R A B C =>
      simpa [List.append_assoc] using
        (HilbertSameFigure.triangleSwapLast
          (L ++ M) R A B C)

  | symm h ih =>
      exact HilbertSameFigure.symm ih

  | trans hPQ hQR ihPQ ihQR =>
      exact HilbertSameFigure.trans ihPQ ihQR


theorem hilbert_figureEquidecomposable_append_right
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertFigureEquidecomposable Geo P Q)
    (R : HilbertTriangulatedFigure Geo) :
    HilbertFigureEquidecomposable Geo
      (P ++ R) (Q ++ R) := by

  induction hPQ with
  | sameFigure h =>
      exact
        HilbertFigureEquidecomposable.sameFigure
          (hilbert_sameFigure_append_right Geo h R)

  | congruentTriangulations h =>
      exact
        HilbertFigureEquidecomposable.congruentTriangulations
          (hilbert_equidecomposable_append
            Geo h (hilbert_equidecomposable_refl Geo R))

  | symm h ih =>
      exact HilbertFigureEquidecomposable.symm ih

  | trans hPQ hQR ihPQ ihQR =>
      exact HilbertFigureEquidecomposable.trans ihPQ ihQR


theorem hilbert_figureEquidecomposable_append_left
    [HilbertCongruence Geo]
    (L : HilbertTriangulatedFigure Geo)
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertFigureEquidecomposable Geo P Q) :
    HilbertFigureEquidecomposable Geo
      (L ++ P) (L ++ Q) := by

  induction hPQ with
  | sameFigure h =>
      exact
        HilbertFigureEquidecomposable.sameFigure
          (hilbert_sameFigure_append_left Geo L h)

  | congruentTriangulations h =>
      exact
        HilbertFigureEquidecomposable.congruentTriangulations
          (hilbert_equidecomposable_append
            Geo (hilbert_equidecomposable_refl Geo L) h)

  | symm h ih =>
      exact HilbertFigureEquidecomposable.symm ih

  | trans hPQ hQR ihPQ ihQR =>
      exact HilbertFigureEquidecomposable.trans ihPQ ihQR


theorem hilbert_figureEquidecomposable_append
    [HilbertCongruence Geo]
    {P1 P2 Q1 Q2 : HilbertTriangulatedFigure Geo}
    (h1 : HilbertFigureEquidecomposable Geo P1 Q1)
    (h2 : HilbertFigureEquidecomposable Geo P2 Q2) :
    HilbertFigureEquidecomposable Geo
      (P1 ++ P2) (Q1 ++ Q2) := by

  have hLeft :
      HilbertFigureEquidecomposable Geo
        (P1 ++ P2) (Q1 ++ P2) :=
    hilbert_figureEquidecomposable_append_right
      Geo h1 P2

  have hRight :
      HilbertFigureEquidecomposable Geo
        (Q1 ++ P2) (Q1 ++ Q2) :=
    hilbert_figureEquidecomposable_append_left
      Geo Q1 h2

  exact
    HilbertFigureEquidecomposable.trans
      hLeft hRight


theorem hilbert_figureEquidecomposable_append_comm
    [HilbertCongruence Geo]
    (P Q : HilbertTriangulatedFigure Geo) :
    HilbertFigureEquidecomposable Geo
      (P ++ Q) (Q ++ P) := by

  have hOld :
      HilbertEquidecomposable Geo
        (P ++ Q) (Q ++ P) := by

    have hRefl :
        HilbertTriangleListCongruent Geo
          (P ++ Q) (P ++ Q) := by
      induction (P ++ Q) with
      | nil =>
          exact HilbertTriangleListCongruent.nil
      | cons T S ih =>
          exact
            HilbertTriangleListCongruent.cons
              (hilbert_triangleCongruent_refl Geo T)
              ih

    exact
      ⟨P ++ Q,
        List.perm_append_comm,
        hRefl⟩

  exact
    HilbertFigureEquidecomposable.congruentTriangulations
      hOld


def HilbertEquicomplementable
    [HilbertCongruence Geo]
    (P Q : HilbertTriangulatedFigure Geo) : Prop :=
  ∃ P' Q' : HilbertTriangulatedFigure Geo,
    HilbertFigureEquidecomposable Geo P' Q' ∧
    HilbertFigureEquidecomposable Geo
      (P ++ P')
      (Q ++ Q')


theorem hilbert_equidecomposable_implies_equicomplementable
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertEquidecomposable Geo P Q) :
    HilbertEquicomplementable Geo P Q := by

  refine ⟨[], [], ?_, ?_⟩

  · exact
      hilbert_figureEquidecomposable_refl Geo []

  · simpa using
      (HilbertFigureEquidecomposable.congruentTriangulations hPQ)


theorem hilbert_equicomplementable_symm
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertEquicomplementable Geo P Q) :
    HilbertEquicomplementable Geo Q P := by

  rcases hPQ with
    ⟨P', Q', hComp, hWhole⟩

  refine ⟨Q', P', ?_, ?_⟩

  · exact
      hilbert_figureEquidecomposable_symm
        Geo hComp

  · exact
      hilbert_figureEquidecomposable_symm
        Geo hWhole


theorem hilbert_equicomplementable_trans
    [HilbertCongruence Geo]
    {P Q R : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertEquicomplementable Geo P Q)
    (hQR : HilbertEquicomplementable Geo Q R) :
    HilbertEquicomplementable Geo P R := by

  rcases hPQ with
    ⟨P1, Q1, hP1Q1, hPQwhole⟩

  rcases hQR with
    ⟨Q2, R2, hQ2R2, hQRwhole⟩

  refine ⟨P1 ++ Q2, R2 ++ Q1, ?_, ?_⟩

  ·
    have hComp :
        HilbertFigureEquidecomposable Geo
          (P1 ++ Q2)
          (Q1 ++ R2) :=
      hilbert_figureEquidecomposable_append
        Geo hP1Q1 hQ2R2

    have hSwap :
        HilbertFigureEquidecomposable Geo
          (Q1 ++ R2)
          (R2 ++ Q1) :=
      hilbert_figureEquidecomposable_append_comm
        Geo Q1 R2

    exact
      hilbert_figureEquidecomposable_trans
        Geo hComp hSwap

  ·
    have hStep1 :
        HilbertFigureEquidecomposable Geo
          ((P ++ P1) ++ Q2)
          ((Q ++ Q1) ++ Q2) :=
      hilbert_figureEquidecomposable_append_right
        Geo hPQwhole Q2

    have hSwap12 :
        HilbertFigureEquidecomposable Geo
          (Q1 ++ Q2)
          (Q2 ++ Q1) :=
      hilbert_figureEquidecomposable_append_comm
        Geo Q1 Q2

    have hStep2 :
        HilbertFigureEquidecomposable Geo
          (Q ++ (Q1 ++ Q2))
          (Q ++ (Q2 ++ Q1)) :=
      hilbert_figureEquidecomposable_append_left
        Geo Q hSwap12

    have hStep3 :
        HilbertFigureEquidecomposable Geo
          ((Q ++ Q2) ++ Q1)
          ((R ++ R2) ++ Q1) :=
      hilbert_figureEquidecomposable_append_right
        Geo hQRwhole Q1

    have hStep1' :
        HilbertFigureEquidecomposable Geo
          (P ++ (P1 ++ Q2))
          (Q ++ (Q1 ++ Q2)) := by
      simpa [List.append_assoc] using hStep1

    have hStep3' :
        HilbertFigureEquidecomposable Geo
          (Q ++ (Q2 ++ Q1))
          (R ++ (R2 ++ Q1)) := by
      simpa [List.append_assoc] using hStep3

    exact
      hilbert_figureEquidecomposable_trans
        Geo
        hStep1'
        (hilbert_figureEquidecomposable_trans
          Geo hStep2 hStep3')



theorem hilbert_equidecomposable_of_perm
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPerm : P.Perm Q) :
    HilbertEquidecomposable Geo P Q := by

  have hRefl :
      HilbertTriangleListCongruent Geo P P := by
    clear hPerm
    induction P with
    | nil =>
        exact HilbertTriangleListCongruent.nil
    | cons T P ih =>
        exact
          HilbertTriangleListCongruent.cons
            (hilbert_triangleCongruent_refl Geo T)
            ih

  exact
    ⟨P, hPerm, hRefl⟩




theorem hilbert_figureEquidecomposable_split
    [HilbertCongruence Geo]
    (L R : HilbertTriangulatedFigure Geo)
    (A B C X : Geo.Point)
    (hBXC : Geo.Between B X C) :
    HilbertFigureEquidecomposable Geo
      (L ++ [⟨A, B, C⟩] ++ R)
      (L ++ [⟨A, B, X⟩, ⟨A, X, C⟩] ++ R) := by

  exact
    HilbertFigureEquidecomposable.sameFigure
      (HilbertSameFigure.split
        L R A B C X hBXC)

theorem hilbert_sameFigure_implies_figureEquidecomposable
    [HilbertCongruence Geo]
    {P Q : HilbertTriangulatedFigure Geo}
    (hPQ : HilbertSameFigure Geo P Q) :
    HilbertFigureEquidecomposable Geo P Q := by

  exact
    HilbertFigureEquidecomposable.sameFigure hPQ

theorem hilbert_equidecomposable_append_comm
    [HilbertCongruence Geo]
    (P Q : HilbertTriangulatedFigure Geo) :
    HilbertEquidecomposable Geo
      (P ++ Q)
      (Q ++ P) := by

  exact
    hilbert_equidecomposable_of_perm
      Geo
      (List.perm_append_comm)



def HilbertParallelogramFigure
    (A B C D : Geo.Point) :
    HilbertTriangulatedFigure Geo :=
  [
    ⟨A, B, C⟩,
    ⟨A, C, D⟩
  ]

/--
Test reconstruction of the outer Pasch step used in Beeson Prop35A.

Configuration:
  A-D-F
  B-M-D
  A,F,B noncollinear

Conclusion:
there exists Q with B-Q-F and A-M-Q.

This is developed in a test file first. Nothing is moved to
HilbertInterface until the proof is complete and builds without sorry.
-/
theorem hilbert_outer_pasch
    [HilbertOrder Geo]
    (A B D F M : Geo.Point)
    (hAFB : ¬ Collinear Geo A F B)
    (hADF : Geo.Between A D F)
    (hBMD : Geo.Between B M D) :
    ∃ Q : Geo.Point,
      Geo.Between B Q F ∧
      Geo.Between A M Q := by
  have hAF :
      A ≠ F :=
    (HilbertOrder.between_incidence
      A D F hADF).2.2.1

  have hDF :
      D ≠ F :=
    (HilbertOrder.between_incidence
      A D F hADF).2.1

  have hBM :
      B ≠ M :=
    (HilbertOrder.between_incidence
      B M D hBMD).1

  have hMD :
      M ≠ D :=
    (HilbertOrder.between_incidence
      B M D hBMD).2.1

  have hAM :
      A ≠ M := by
    intro hEq
    subst M

    have hBAD :
        Collinear Geo B A D :=
      (HilbertOrder.between_incidence
        B A D hBMD).2.2.2.1

    have hADFcol :
        Collinear Geo A D F :=
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1

    have hBAF :
        Collinear Geo B A F :=
      hilbert_primCollinear_trans
        Geo
        B A D F
        hMD
        hBAD
        hADFcol

    exact hAFB
      (PrimCollinearCycle
        Geo B A F hBAF)

  rcases
      HilbertPlaneIncidence.line_through
        A M hAM
    with
    ⟨lineAM, hAlineAM, hMlineAM⟩

  have hMeetsBD :
      HilbertSegmentMeetsLine Geo B D lineAM :=
    ⟨M, hBMD, hMlineAM⟩

  rcases
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1
    with
    ⟨lineAF, hAlineAF, hDlineAF, hFlineAF⟩

  have hDoffAM :
      ¬ HilbertIncidence.OnLine D lineAM := by
    intro hDlineAM

    have hADM :
        Collinear Geo A D M :=
      ⟨lineAM, hAlineAM, hDlineAM, hMlineAM⟩

    have hBMDcol :
        Collinear Geo B M D :=
      (HilbertOrder.between_incidence
        B M D hBMD).2.2.2.1

    have hDMB :
        Collinear Geo D M B :=
      PrimCollinearSwap
        Geo M D B
        (PrimCollinearCycle
          Geo B M D hBMDcol)

    have hADB :
        Collinear Geo A D B :=
      hilbert_primCollinear_trans
        Geo
        A D M B
        hMD.symm
        hADM
        hDMB

    have hADFcol :
        Collinear Geo A D F :=
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1

    have hFDA :
        Collinear Geo F D A :=
      PrimCollinearSymm
        Geo A D F hADFcol

    have hDAB :
        Collinear Geo D A B :=
      PrimCollinearSwap
        Geo A D B hADB

    have hDA :
        D ≠ A :=
      (HilbertOrder.between_incidence
        A D F hADF).1.symm

    have hFDB :
        Collinear Geo F D B :=
      hilbert_primCollinear_trans
        Geo
        F D A B
        hDA
        hFDA
        hDAB

    have hAFD :
        Collinear Geo A F D :=
      PrimCollinearRotate
        Geo A D F hADFcol

    have hAFB' :
        Collinear Geo A F B :=
      hilbert_primCollinear_trans
        Geo
        A F D B
        hDF.symm
        hAFD
        hFDB

    exact hAFB hAFB'

  have hLinesAF_AM :
      lineAF ≠ lineAM := by
    intro hEq

    have hDlineAM :
        HilbertIncidence.OnLine D lineAM := by
      rw [← hEq]
      exact hDlineAF

    exact hDoffAM hDlineAM

  have hNotDAF :
      ¬ Geo.Between D A F := by
    intro hDAF

    have hADFcol :
        Collinear Geo A D F :=
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1

    exact
      (HilbertOrder.between_unique
        A D F hADFcol hADF).1
        hDAF
  have hBDF :
      ¬ Collinear Geo B D F := by
    intro hBDFcol

    have hDFB :
        Collinear Geo D F B :=
      PrimCollinearCycle
        Geo B D F hBDFcol

    have hADFcol :
        Collinear Geo A D F :=
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1

    have hADB :
        Collinear Geo A D B :=
      hilbert_primCollinear_trans
        Geo
        A D F B
        hDF
        hADFcol
        hDFB

    have hFDA :
        Collinear Geo F D A :=
      PrimCollinearSymm
        Geo A D F hADFcol

    have hDAB :
        Collinear Geo D A B :=
      PrimCollinearSwap
        Geo A D B hADB

    have hDA :
        D ≠ A :=
      (HilbertOrder.between_incidence
        A D F hADF).1.symm

    have hFDB :
        Collinear Geo F D B :=
      hilbert_primCollinear_trans
        Geo
        F D A B
        hDA
        hFDA
        hDAB

    have hAFB' :
        Collinear Geo A F B :=
      hilbert_primCollinear_trans
        Geo
        A F D B
        hDF.symm
        (PrimCollinearRotate
          Geo A D F hADFcol)
        hFDB

    exact hAFB hAFB'

  have hNotMeetsDF :
      ¬ HilbertSegmentMeetsLine Geo D F lineAM :=
    hilbert_segment_not_meets_crossing_line
      Geo
      D F A
      lineAF lineAM
      hLinesAF_AM
      hDlineAF
      hFlineAF
      hAlineAF
      hAlineAM
      hNotDAF

  have hBoffAM :
      ¬ HilbertIncidence.OnLine B lineAM := by
    intro hBlineAM

    have hDlineAM :
        HilbertIncidence.OnLine D lineAM :=
      hilbert_collinear_on_line
        Geo
        B M D
        lineAM
        hBM
        hBlineAM
        hMlineAM
        (HilbertOrder.between_incidence
          B M D hBMD).2.2.2.1

    exact hDoffAM hDlineAM

  have hFoffAM :
      ¬ HilbertIncidence.OnLine F lineAM := by
    intro hFlineAM

    have hDlineAM :
        HilbertIncidence.OnLine D lineAM :=
      hilbert_collinear_on_line
        Geo
        A F D
        lineAM
        hAF
        hAlineAM
        hFlineAM
        (PrimCollinearRotate
          Geo A D F
          (HilbertOrder.between_incidence
            A D F hADF).2.2.2.1)

    exact hDoffAM hDlineAM

  rcases
      hilbert_pasch_forced
        Geo
        B D F
        lineAM
        hBDF
        hBoffAM
        hDoffAM
        hFoffAM
        hMeetsBD
        hNotMeetsDF
    with
    ⟨Q, hBQF, hQlineAM⟩

  have hAQ :
      A ≠ Q := by
    intro hAQeq
    subst Q

    have hBAF :
        Collinear Geo B A F :=
      (HilbertOrder.between_incidence
        B A F hBQF).2.2.2.1

    exact hAFB
      (PrimCollinearCycle
        Geo B A F hBAF)

  have hMQ :
      M ≠ Q := by
    intro hMQeq
    subst Q

    have hBMDcol :
        Collinear Geo B M D :=
      (HilbertOrder.between_incidence
        B M D hBMD).2.2.2.1

    have hBMFcol :
        Collinear Geo B M F :=
      (HilbertOrder.between_incidence
        B M F hBQF).2.2.2.1

    have hDBM :
        Collinear Geo D B M :=
      PrimCollinearCycle
        Geo M D B
        (PrimCollinearCycle
          Geo B M D hBMDcol)

    have hDBF :
        Collinear Geo D B F :=
      hilbert_primCollinear_trans
        Geo
        D B M F
        hBM
        hDBM
        hBMFcol

    have hBDF' :
        Collinear Geo B D F :=
      PrimCollinearSwap
        Geo D B F hDBF

    exact hBDF hBDF'

  have hAMQcol :
      Collinear Geo A M Q :=
    ⟨lineAM, hAlineAM, hMlineAM, hQlineAM⟩

  rcases
      hilbert_between_trichotomy
        Geo
        A M Q
        hAM
        hMQ
        hAQ
        hAMQcol
    with
    hAMQ | hMAQ | hAQM

  · exact ⟨Q, hBQF, hAMQ⟩

  ·
    rcases
        hilbert_between_points_sameSide_transversal
          Geo
          B M F D
          hBMD
          hBDF
      with
      ⟨lineFD₁, hFlineFD₁, hDlineFD₁, hSameBM₁⟩

    have hFD :
        F ≠ D :=
      hDF.symm

    have hEqFD₁ :
        lineFD₁ = lineAF :=
      HilbertPlaneIncidence.line_unique
        F D hFD
        lineFD₁ lineAF
        hFlineFD₁ hDlineFD₁
        hFlineAF hDlineAF

    have hSameBM :
        HilbertSameSide Geo B M lineAF := by
      rw [← hEqFD₁]
      exact hSameBM₁

    have hBFD :
        ¬ Collinear Geo B F D := by
      intro h
      exact hBDF
        (PrimCollinearRotate Geo B F D h)

    rcases
        hilbert_between_points_sameSide_transversal
          Geo
          B Q D F
          hBQF
          hBFD
      with
      ⟨lineDF₂, hDlineDF₂, hFlineDF₂, hSameBQ₂⟩

    have hEqDF₂ :
        lineDF₂ = lineAF :=
      HilbertPlaneIncidence.line_unique
        D F hDF
        lineDF₂ lineAF
        hDlineDF₂ hFlineDF₂
        hDlineAF hFlineAF

    have hSameBQ :
        HilbertSameSide Geo B Q lineAF := by
      rw [← hEqDF₂]
      exact hSameBQ₂

    have hSameMB :
        HilbertSameSide Geo M B lineAF :=
      hilbert_sameSide_symm
        Geo B M lineAF hSameBM

    have hSameMQ :
        HilbertSameSide Geo M Q lineAF :=
      hilbert_sameSide_trans
        Geo M B Q lineAF
        hSameMB hSameBQ

    have hOppMQ :
        HilbertOppositeSide Geo M Q lineAF :=
      ⟨hSameMQ.1,
       hSameMQ.2.1,
       ⟨A, hMAQ, hAlineAF⟩⟩

    have hFalse : False :=
      (hilbert_oppositeSide_not_sameSide
        Geo M Q lineAF hOppMQ)
        hSameMQ

    exact hFalse.elim

  ·
    -- A-D-F, while B is off AF:
    -- A and D are on the same side of BF.
    rcases
        hilbert_between_points_sameSide_transversal
          Geo
          A D B F
          hADF
          hAFB
      with
      ⟨lineBF₁, hBlineBF₁, hFlineBF₁, hSameAD₁⟩

    -- Reverse B-M-D to D-M-B.
    have hDMB :
        Geo.Between D M B :=
      (HilbertOrder.between_incidence
        B M D hBMD).2.2.2.2

    have hDBF :
        ¬ Collinear Geo D B F := by
      intro h
      exact hBDF
        (PrimCollinearSwap
          Geo D B F h)

    -- D-M-B, while F is off DB:
    -- D and M are on the same side of FB.
    rcases
        hilbert_between_points_sameSide_transversal
          Geo
          D M F B
          hDMB
          hDBF
      with
      ⟨lineFB₂, hFlineFB₂, hBlineFB₂, hSameDM₂⟩

    have hBF :
        B ≠ F :=
      (HilbertOrder.between_incidence
        B Q F hBQF).2.2.1

    -- Both witness lines are the line BF.
    have hEqLines :
        lineFB₂ = lineBF₁ :=
      HilbertPlaneIncidence.line_unique
        B F hBF
        lineFB₂ lineBF₁
        hBlineFB₂ hFlineFB₂
        hBlineBF₁ hFlineBF₁

    have hSameDM :
        HilbertSameSide Geo D M lineBF₁ := by
      rw [← hEqLines]
      exact hSameDM₂

    -- Hence A and M lie on the same side of BF.
    have hSameAM :
        HilbertSameSide Geo A M lineBF₁ :=
      hilbert_sameSide_trans
        Geo
        A D M
        lineBF₁
        hSameAD₁
        hSameDM

    -- But Q is on BF.
    have hQlineBF :
        HilbertIncidence.OnLine Q lineBF₁ :=
      hilbert_between_on_line
        Geo
        B Q F
        lineBF₁
        hBlineBF₁
        hFlineBF₁
        hBQF

    -- A-Q-M therefore puts A and M on opposite sides of BF.
    have hOppAM :
        HilbertOppositeSide Geo A M lineBF₁ :=
      ⟨hSameAM.1,
       hSameAM.2.1,
       ⟨Q, hAQM, hQlineBF⟩⟩

    have hFalse : False :=
      (hilbert_oppositeSide_not_sameSide
        Geo A M lineBF₁ hOppAM)
        hSameAM

    exact hFalse.elim

/--
If FA is parallel to CB, Q lies between F and B,
and A, C, Q are collinear, then Q lies between A and C.

This is the Hilbert counterpart of Beeson's `collinearbetween`
used in Euclid I.35.
-/
theorem hilbert_collinear_between_of_parallel
    [HilbertOrder Geo]
    (F A C B Q : Geo.Point)
    (hParallel : Geo.Parallel F A C B)
    (hFQB : Geo.Between F Q B)
    (hACQ : Collinear Geo A C Q) :
    Geo.Between A Q C := by

  have hFA :
      F ≠ A :=
    hParallel.1

  have hCB :
      C ≠ B :=
    hParallel.2.1

  have hFQ :
      F ≠ Q :=
    (HilbertOrder.between_incidence
      F Q B hFQB).1

  have hQB :
      Q ≠ B :=
    (HilbertOrder.between_incidence
      F Q B hFQB).2.1

  have hFB :
      F ≠ B :=
    (HilbertOrder.between_incidence
      F Q B hFQB).2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        F A hFA
    with
    ⟨lineFA, hFlineFA, hAlineFA⟩

  rcases
      HilbertPlaneIncidence.line_through
        C B hCB
    with
    ⟨lineCB, hClineCB, hBlineCB⟩

  have hAC :
      A ≠ C := by
    intro hACeq

    have hAlineCB :
        HilbertIncidence.OnLine A lineCB := by
      rw [hACeq]
      exact hClineCB

    have hA_FA :
        A ∈ Geo.PointLine F A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F A A lineFA
        hFA
        hFlineFA
        hAlineFA).mpr hAlineFA

    have hA_CB :
        A ∈ Geo.PointLine C B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C B A lineCB
        hCB
        hClineCB
        hBlineCB).mpr hAlineCB

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hA_FA
        hA_CB

  have hAQ :
      A ≠ Q := by
    intro hAQeq
    subst Q

    have hFABcol :
        Collinear Geo F A B :=
      (HilbertOrder.between_incidence
        F A B hFQB).2.2.2.1

    have hBlineFA :
        HilbertIncidence.OnLine B lineFA :=
      hilbert_collinear_on_line
        Geo
        F A B
        lineFA
        hFA
        hFlineFA
        hAlineFA
        hFABcol

    have hB_FA :
        B ∈ Geo.PointLine F A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F A B lineFA
        hFA
        hFlineFA
        hAlineFA).mpr hBlineFA

    have hB_CB :
        B ∈ Geo.PointLine C B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C B B lineCB
        hCB
        hClineCB
        hBlineCB).mpr hBlineCB

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hB_FA
        hB_CB

  have hQC :
      Q ≠ C := by
    intro hQCeq
    subst Q

    have hFCBcol :
        Collinear Geo F C B :=
      (HilbertOrder.between_incidence
        F C B hFQB).2.2.2.1

    have hFlineCB :
        HilbertIncidence.OnLine F lineCB :=
      hilbert_collinear_on_line
        Geo
        C B F
        lineCB
        hCB
        hClineCB
        hBlineCB
        (PrimCollinearCycle
          Geo F C B hFCBcol)

    have hF_FA :
        F ∈ Geo.PointLine F A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F A F lineFA
        hFA
        hFlineFA
        hAlineFA).mpr hFlineFA

    have hF_CB :
        F ∈ Geo.PointLine C B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C B F lineCB
        hCB
        hClineCB
        hBlineCB).mpr hFlineCB

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hF_FA
        hF_CB

  rcases
      hilbert_between_trichotomy
        Geo
        A Q C
        hAQ
        hQC
        hAC
        (PrimCollinearRotate
          Geo A C Q hACQ)
    with
    hAQC | hQAC | hACQorder

  · exact hAQC

  ·
    have hCAQ :
        Geo.Between C A Q :=
      (HilbertOrder.between_incidence
        Q A C hQAC).2.2.2.2

    have hFBC :
        ¬ Collinear Geo F B C := by
      intro hFBCcol

      have hCBF :
          Collinear Geo C B F :=
        PrimCollinearSwap
          Geo B C F
          (PrimCollinearCycle
            Geo F B C hFBCcol)

      have hFlineCB :
          HilbertIncidence.OnLine F lineCB :=
        hilbert_collinear_on_line
          Geo
          C B F
          lineCB
          hCB
          hClineCB
          hBlineCB
          hCBF

      have hF_FA :
          F ∈ Geo.PointLine F A :=
        (hilbert_mem_pointLine_iff_onLine
          Geo F A F lineFA
          hFA
          hFlineFA
          hAlineFA).mpr hFlineFA

      have hF_CB :
          F ∈ Geo.PointLine C B :=
        (hilbert_mem_pointLine_iff_onLine
          Geo C B F lineCB
          hCB
          hClineCB
          hBlineCB).mpr hFlineCB

      have hFalse : False :=
        Set.disjoint_left.mp
          hParallel.2.2
          hF_FA
          hF_CB

      exact hFalse.elim

    rcases
        hilbert_outer_pasch
          Geo
          F C Q B A
          hFBC
          hFQB
          hCAQ
      with
      ⟨R, hCRB, hFAR⟩

    have hRlineFA :
        HilbertIncidence.OnLine R lineFA :=
      hilbert_collinear_on_line
        Geo
        F A R
        lineFA
        hFA
        hFlineFA
        hAlineFA
        (HilbertOrder.between_incidence
          F A R hFAR).2.2.2.1

    have hRlineCB :
        HilbertIncidence.OnLine R lineCB :=
      hilbert_collinear_on_line
        Geo
        C B R
        lineCB
        hCB
        hClineCB
        hBlineCB
        (PrimCollinearRotate
          Geo C R B
          (HilbertOrder.between_incidence
            C R B hCRB).2.2.2.1)

    have hR_FA :
        R ∈ Geo.PointLine F A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F A R lineFA
        hFA
        hFlineFA
        hAlineFA).mpr hRlineFA

    have hR_CB :
        R ∈ Geo.PointLine C B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C B R lineCB
        hCB
        hClineCB
        hBlineCB).mpr hRlineCB

    have hFalse : False :=
      Set.disjoint_left.mp
        hParallel.2.2
        hR_FA
        hR_CB

    exact hFalse.elim

  ·
    have hBQF :
        Geo.Between B Q F :=
      (HilbertOrder.between_incidence
        F Q B hFQB).2.2.2.2

    have hBFA :
        ¬ Collinear Geo B F A := by
      intro hBFAcol

      have hFAB :
          Collinear Geo F A B :=
        PrimCollinearCycle
          Geo B F A hBFAcol

      have hBlineFA :
          HilbertIncidence.OnLine B lineFA :=
        hilbert_collinear_on_line
          Geo
          F A B
          lineFA
          hFA
          hFlineFA
          hAlineFA
          hFAB

      have hB_FA :
          B ∈ Geo.PointLine F A :=
        (hilbert_mem_pointLine_iff_onLine
          Geo F A B lineFA
          hFA
          hFlineFA
          hAlineFA).mpr hBlineFA

      have hB_CB :
          B ∈ Geo.PointLine C B :=
        (hilbert_mem_pointLine_iff_onLine
          Geo C B B lineCB
          hCB
          hClineCB
          hBlineCB).mpr hBlineCB

      have hFalse : False :=
        Set.disjoint_left.mp
          hParallel.2.2
          hB_FA
          hB_CB

      exact hFalse.elim

    rcases
        hilbert_outer_pasch
          Geo
          B A Q F C
          hBFA
          hBQF
          hACQorder
      with
      ⟨R, hARF, hBCR⟩

    have hRlineFA :
        HilbertIncidence.OnLine R lineFA :=
      hilbert_between_on_line
        Geo
        A R F
        lineFA
        hAlineFA
        hFlineFA
        hARF

    have hBCRcol :
        Collinear Geo B C R :=
      (HilbertOrder.between_incidence
        B C R hBCR).2.2.2.1

    have hCBR :
        Collinear Geo C B R :=
      PrimCollinearSwap
        Geo B C R hBCRcol

    have hRlineCB :
        HilbertIncidence.OnLine R lineCB :=
      hilbert_collinear_on_line
        Geo
        C B R
        lineCB
        hCB
        hClineCB
        hBlineCB
        hCBR

    have hR_FA :
        R ∈ Geo.PointLine F A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F A R lineFA
        hFA
        hFlineFA
        hAlineFA).mpr hRlineFA

    have hR_CB :
        R ∈ Geo.PointLine C B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C B R lineCB
        hCB
        hClineCB
        hBlineCB).mpr hRlineCB

    have hFalse : False :=
      Set.disjoint_left.mp
        hParallel.2.2
        hR_FA
        hR_CB

    exact hFalse.elim


theorem quadrilateral_diagonal_flip
    [HilbertCongruence Geo]
    (A B C D X : Geo.Point)
    (hAXC : Geo.Between A X C)
    (hBXD : Geo.Between B X D) :
    HilbertFigureEquidecomposable Geo
      [⟨A, B, C⟩, ⟨A, C, D⟩]
      [⟨A, B, D⟩, ⟨B, C, D⟩] := by

  have hLeftSwap1 :
      HilbertSameFigure Geo
        [⟨A, B, C⟩, ⟨A, C, D⟩]
        [⟨B, A, C⟩, ⟨A, C, D⟩] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        []
        [⟨A, C, D⟩]
        A B C)

  have hLeftSplit1 :
      HilbertSameFigure Geo
        [⟨B, A, C⟩, ⟨A, C, D⟩]
        [⟨B, A, X⟩, ⟨B, X, C⟩, ⟨A, C, D⟩] := by
    simpa using
      (HilbertSameFigure.split
        []
        [⟨A, C, D⟩]
        B A C X
        hAXC)
  have hLeftSwap2a :
      HilbertSameFigure Geo
        [⟨B, A, X⟩, ⟨B, X, C⟩, ⟨A, C, D⟩]
        [⟨B, A, X⟩, ⟨B, X, C⟩, ⟨A, D, C⟩] := by
    simpa using
      (HilbertSameFigure.triangleSwapLast
        [⟨B, A, X⟩, ⟨B, X, C⟩]
        []
        A C D)

  have hLeftSwap2b :
      HilbertSameFigure Geo
        [⟨B, A, X⟩, ⟨B, X, C⟩, ⟨A, D, C⟩]
        [⟨B, A, X⟩, ⟨B, X, C⟩, ⟨D, A, C⟩] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [⟨B, A, X⟩, ⟨B, X, C⟩]
        []
        A D C)

  have hLeftSplit2 :
      HilbertSameFigure Geo
        [⟨B, A, X⟩, ⟨B, X, C⟩, ⟨D, A, C⟩]
        [
          ⟨B, A, X⟩,
          ⟨B, X, C⟩,
          ⟨D, A, X⟩,
          ⟨D, X, C⟩
        ] := by
    simpa using
      (HilbertSameFigure.split
        [⟨B, A, X⟩, ⟨B, X, C⟩]
        []
        D A C X
        hAXC)

  have hLeft :
      HilbertSameFigure Geo
        [⟨A, B, C⟩, ⟨A, C, D⟩]
        [
          ⟨B, A, X⟩,
          ⟨B, X, C⟩,
          ⟨D, A, X⟩,
          ⟨D, X, C⟩
        ] :=
    HilbertSameFigure.trans
      hLeftSwap1
      (HilbertSameFigure.trans
        hLeftSplit1
        (HilbertSameFigure.trans
          hLeftSwap2a
          (HilbertSameFigure.trans
            hLeftSwap2b
            hLeftSplit2)))

  have hRightSplit1 :
      HilbertSameFigure Geo
        [⟨A, B, D⟩, ⟨B, C, D⟩]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, C, D⟩
        ] := by
    simpa using
      (HilbertSameFigure.split
        []
        [⟨B, C, D⟩]
        A B D X
        hBXD)

  have hRightSwap2 :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, C, D⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨C, B, D⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [⟨A, B, X⟩, ⟨A, X, D⟩]
        []
        B C D)

  have hRightSplit2 :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨C, B, D⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨C, B, X⟩,
          ⟨C, X, D⟩
        ] := by
    simpa using
      (HilbertSameFigure.split
        [⟨A, B, X⟩, ⟨A, X, D⟩]
        []
        C B D X
        hBXD)

  have hRight :
      HilbertSameFigure Geo
        [⟨A, B, D⟩, ⟨B, C, D⟩]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨C, B, X⟩,
          ⟨C, X, D⟩
        ] :=
    HilbertSameFigure.trans
      hRightSplit1
      (HilbertSameFigure.trans
        hRightSwap2
        hRightSplit2)

  have hLeftOrient1 :
      HilbertSameFigure Geo
        [
          ⟨B, A, X⟩,
          ⟨B, X, C⟩,
          ⟨D, A, X⟩,
          ⟨D, X, C⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨D, A, X⟩,
          ⟨D, X, C⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        []
        [
          ⟨B, X, C⟩,
          ⟨D, A, X⟩,
          ⟨D, X, C⟩
        ]
        B A X)

  have hLeftOrient2 :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨D, A, X⟩,
          ⟨D, X, C⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨A, D, X⟩,
          ⟨D, X, C⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩
        ]
        [⟨D, X, C⟩]
        D A X)

  have hLeftOriented :
      HilbertSameFigure Geo
        [⟨A, B, C⟩, ⟨A, C, D⟩]
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨A, D, X⟩,
          ⟨D, X, C⟩
        ] :=
    HilbertSameFigure.trans
      hLeft
      (HilbertSameFigure.trans
        hLeftOrient1
        hLeftOrient2)

  have hRightOrient1 :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨C, B, X⟩,
          ⟨C, X, D⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, C, X⟩,
          ⟨C, X, D⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩
        ]
        [⟨C, X, D⟩]
        C B X)

  have hRightOrient2 :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, C, X⟩,
          ⟨C, X, D⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨C, X, D⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapLast
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩
        ]
        [⟨C, X, D⟩]
        B C X)

  have hRightOrient3a :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨C, X, D⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨C, D, X⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapLast
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩
        ]
        []
        C X D)

  have hRightOrient3b :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨C, D, X⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨D, C, X⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩
        ]
        []
        C D X)

  have hRightOrient3c :
      HilbertSameFigure Geo
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨D, C, X⟩
        ]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨D, X, C⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapLast
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩
        ]
        []
        D C X)

  have hRightOriented :
      HilbertSameFigure Geo
        [⟨A, B, D⟩, ⟨B, C, D⟩]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨D, X, C⟩
        ] :=
    HilbertSameFigure.trans
      hRight
      (HilbertSameFigure.trans
        hRightOrient1
        (HilbertSameFigure.trans
          hRightOrient2
          (HilbertSameFigure.trans
            hRightOrient3a
            (HilbertSameFigure.trans
              hRightOrient3b
              hRightOrient3c))))

  have hLeftFig :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, C⟩, ⟨A, C, D⟩]
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨A, D, X⟩,
          ⟨D, X, C⟩
        ] :=
    HilbertFigureEquidecomposable.sameFigure
      hLeftOriented

  have hRightFig :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, D⟩, ⟨B, C, D⟩]
        [
          ⟨A, B, X⟩,
          ⟨A, X, D⟩,
          ⟨B, X, C⟩,
          ⟨D, X, C⟩
        ] :=
    HilbertFigureEquidecomposable.sameFigure
      hRightOriented

  let Lleft : HilbertTriangulatedFigure Geo :=
    [
      ⟨A, B, X⟩,
      ⟨B, X, C⟩,
      ⟨A, D, X⟩,
      ⟨D, X, C⟩
    ]

  let Lright : HilbertTriangulatedFigure Geo :=
    [
      ⟨A, B, X⟩,
      ⟨A, X, D⟩,
      ⟨B, X, C⟩,
      ⟨D, X, C⟩
    ]

  have hADX_AXD :
      HilbertSameFigure Geo
        Lleft
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨A, X, D⟩,
          ⟨D, X, C⟩
        ] := by
    dsimp [Lleft]

    simpa using
      (HilbertSameFigure.triangleSwapLast
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩
        ]
        [⟨D, X, C⟩]
        A D X)

  have hLeftToLleft :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, C⟩, ⟨A, C, D⟩]
        Lleft := by
    simpa [Lleft] using hLeftFig

  have hOrientFig :
      HilbertFigureEquidecomposable Geo
        Lleft
        [
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨A, X, D⟩,
          ⟨D, X, C⟩
        ] :=
    HilbertFigureEquidecomposable.sameFigure
      hADX_AXD

  have hPerm :
      ([
        ⟨A, B, X⟩,
        ⟨B, X, C⟩,
        ⟨A, X, D⟩,
        ⟨D, X, C⟩
      ] : HilbertTriangulatedFigure Geo).Perm
      Lright := by
    dsimp [Lright]

    exact
      List.Perm.cons
        (⟨A, B, X⟩ : HilbertTriangle Geo)
        (List.Perm.swap
          (⟨B, X, C⟩ : HilbertTriangle Geo)
          (⟨A, X, D⟩ : HilbertTriangle Geo)
          [(⟨D, X, C⟩ : HilbertTriangle Geo)]).symm

  have hPermFig :
      HilbertFigureEquidecomposable Geo
        ([
          ⟨A, B, X⟩,
          ⟨B, X, C⟩,
          ⟨A, X, D⟩,
          ⟨D, X, C⟩
        ] : HilbertTriangulatedFigure Geo)
        Lright :=
    HilbertFigureEquidecomposable.congruentTriangulations
      (hilbert_equidecomposable_of_perm
        Geo hPerm)

  have hRightToLright :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, D⟩, ⟨B, C, D⟩]
        Lright := by
    simpa [Lright] using hRightFig

  exact
    HilbertFigureEquidecomposable.trans
      hLeftToLleft
      (HilbertFigureEquidecomposable.trans
        hOrientFig
        (HilbertFigureEquidecomposable.trans
          hPermFig
          (HilbertFigureEquidecomposable.symm
            hRightToLright)))

end Geometry

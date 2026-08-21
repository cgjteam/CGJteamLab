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

/-!
# Hilbert Grundlagen - Theorem 31 transfer block

This file contains exactly the declarations needed to move the completed
Hilbert Theorem 31 development from `HilbertGrundlagenPascalTest` into
`HilbertGrundlagen.lean`.

Paste the declarations below inside the existing `namespace Geometry`,
before the final `end Geometry`.

The temporary name `HilbertGrundlagenRayMeetsSegment` has already been
normalized to `HilbertRayMeetsSegment`.
-/



------------------------------------------------------------------------
-- Ray/segment helper for the local Theorem 15 development
------------------------------------------------------------------------

/--
The ray from O through R meets the open segment AB.

Temporary test version for the Pascal development.
-/
def HilbertRayMeetsSegment
    (O R A B : Geo.Point) : Prop :=
  Exists fun X : Geo.Point =>
    Geo.Between A X B /\
    HilbertSameRay Geo O R X


------------------------------------------------------------------------
-- Chapter I, sec. 5
-- Interior of an angle
------------------------------------------------------------------------

/--
Hilbert's definition of a point lying in the interior of an angle.

For the angle AOB, a point X is interior when

* X and A lie on the same side of the line OB,
* X and B lie on the same side of the line OA.

The boundary lines are included explicitly as witnesses.
The same-side conditions force the angle to be nondegenerate.
-/
def HilbertInsideAngle
    (O A B X : Geo.Point) : Prop :=
  Exists fun lineOA : Geo.Line =>
  Exists fun lineOB : Geo.Line =>
    HilbertIncidence.OnLine O lineOA /\
    HilbertIncidence.OnLine A lineOA /\
    HilbertIncidence.OnLine O lineOB /\
    HilbertIncidence.OnLine B lineOB /\
    HilbertSameSide Geo X A lineOB /\
    HilbertSameSide Geo X B lineOA


------------------------------------------------------------------------
-- Chapter I, sec. 5
-- Interior points of a segment and a boundary line
------------------------------------------------------------------------

/--
Let A-X-B and let B lie on a line l while A lies off l.
Then A and the interior point X lie on the same side of l.

Geometrically, the segment AX cannot reach l before the endpoint B.
-/
theorem hilbert_between_sameSide_of_endpoint_on_line
    [HilbertOrder Geo]
    (A X B : Geo.Point)
    (l : Geo.Line)
    (hAXB : Geo.Between A X B)
    (hBl : HilbertIncidence.OnLine B l)
    (hAoff : Not (HilbertIncidence.OnLine A l)) :
    HilbertSameSide Geo A X l := by

  have hData :=
    HilbertOrder.between_incidence
      A X B hAXB

  have hAB : A ≠ B :=
    hData.2.2.1

  have hXB : X ≠ B :=
    hData.2.1

  have hCol :
      PrimCollinear Geo A X B :=
    hData.2.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        A B hAB with
    ⟨base, hAbase, hBbase⟩

  have hXbase :
      HilbertIncidence.OnLine X base :=
    hilbert_between_on_line
      Geo
      A X B
      base
      hAbase hBbase
      hAXB

  have hLines :
      base ≠ l := by
    intro hEq
    subst l
    exact hAoff hAbase

  have hXoff :
      Not (HilbertIncidence.OnLine X l) := by
    intro hXl

    have hEq :
        base = l :=
      HilbertPlaneIncidence.line_unique
        B X
        hXB.symm
        base l
        hBbase hXbase
        hBl hXl

    exact hLines hEq

  have hNotABX :
      Not (Geo.Between A B X) :=
    (HilbertOrder.between_unique
      A X B
      hCol
      hAXB).2

  have hNoMeet :
      Not (HilbertSegmentMeetsLine Geo A X l) :=
    hilbert_segment_not_meets_crossing_line
      Geo
      A X B
      base l
      hLines
      hAbase
      hXbase
      hBbase
      hBl
      hNotABX

  exact
    ⟨hAoff,
     hXoff,
     Relation.ReflTransGen.single
       ⟨hAoff, hXoff, hNoMeet⟩⟩


------------------------------------------------------------------------
-- Chapter I, sec. 5
-- Crossbar theorem
------------------------------------------------------------------------

/--
Hilbert's crossbar theorem.

If X lies in the interior of angle AOB, then the ray OX meets
the open segment AB.
-/
theorem hilbert_insideAngle_ray_meets_segment
    [HilbertOrder Geo]
    (O A B X : Geo.Point)
    (hInside : HilbertInsideAngle Geo O A B X) :
    HilbertRayMeetsSegment Geo O X A B := by

  rcases hInside with
    ⟨lineOA,
     lineOB,
     hOlineOA,
     hAlineOA,
     hOlineOB,
     hBlineOB,
     hXA,
     hXB⟩

  have hXoffOB :
      Not (HilbertIncidence.OnLine X lineOB) :=
    hXA.1

  have hAoffOB :
      Not (HilbertIncidence.OnLine A lineOB) :=
    hXA.2.1

  have hXoffOA :
      Not (HilbertIncidence.OnLine X lineOA) :=
    hXB.1

  have hBoffOA :
      Not (HilbertIncidence.OnLine B lineOA) :=
    hXB.2.1

  have hXO : X ≠ O := by
    intro hEq
    subst X
    exact hXoffOB hOlineOB

  have hAO : A ≠ O := by
    intro hEq
    subst A
    exact hAoffOB hOlineOB

  have hBO : B ≠ O := by
    intro hEq
    subst B
    exact hBoffOA hOlineOA

  --------------------------------------------------------------------
  -- The crossbar line n = OX.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O X hXO.symm with
    ⟨n, hOn, hXn⟩

  --------------------------------------------------------------------
  -- Extend BO beyond O:
  --
  --     B - O - E.
  --
  -- Thus E lies on the ray opposite OB.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        B O hBO with
    ⟨E, hBOE⟩

  have hBOEdata :=
    HilbertOrder.between_incidence
      B O E hBOE

  have hOE : O ≠ E :=
    hBOEdata.2.1

  have hBE : B ≠ E :=
    hBOEdata.2.2.1

  have hEOB :
      Geo.Between E O B :=
    hBOEdata.2.2.2.2

  have hElineOB :
      HilbertIncidence.OnLine E lineOB :=
    hilbert_collinear_on_line
      Geo
      B O E
      lineOB
      hBO
      hBlineOB
      hOlineOB
      hBOEdata.2.2.2.1

  --------------------------------------------------------------------
  -- A, B, E are not collinear.
  --------------------------------------------------------------------

  have hBEA :
      Not (PrimCollinear Geo B E A) :=
    hilbert_not_collinear_of_off_line
      Geo
      B E A
      lineOB
      hBE
      hBlineOB
      hElineOB
      hAoffOB

  --------------------------------------------------------------------
  -- None of A, B, E lies on the crossbar line n.
  --------------------------------------------------------------------

  have hAoffn :
      Not (HilbertIncidence.OnLine A n) := by

    intro hAn

    have hEq :
        n = lineOA :=
      HilbertPlaneIncidence.line_unique
        O A
        hAO.symm
        n lineOA
        hOn hAn
        hOlineOA hAlineOA

    have hXlineOA :
        HilbertIncidence.OnLine X lineOA := by
      rw [← hEq]
      exact hXn

    exact hXoffOA hXlineOA

  have hBoffn :
      Not (HilbertIncidence.OnLine B n) := by

    intro hBn

    have hEq :
        n = lineOB :=
      HilbertPlaneIncidence.line_unique
        O B
        hBO.symm
        n lineOB
        hOn hBn
        hOlineOB hBlineOB

    have hXlineOB :
        HilbertIncidence.OnLine X lineOB := by
      rw [← hEq]
      exact hXn

    exact hXoffOB hXlineOB

  have hEoffn :
      Not (HilbertIncidence.OnLine E n) := by

    intro hEn

    have hEq :
        n = lineOB :=
      HilbertPlaneIncidence.line_unique
        O E
        hOE
        n lineOB
        hOn hEn
        hOlineOB hElineOB

    have hXlineOB :
        HilbertIncidence.OnLine X lineOB := by
      rw [← hEq]
      exact hXn

    exact hXoffOB hXlineOB

  --------------------------------------------------------------------
  -- E and B are on opposite sides of OA.
  --------------------------------------------------------------------

  have hEoffOA :
      Not (HilbertIncidence.OnLine E lineOA) := by

    intro hElineOA

    have hEq :
        lineOA = lineOB :=
      HilbertPlaneIncidence.line_unique
        O E
        hOE
        lineOA lineOB
        hOlineOA hElineOA
        hOlineOB hElineOB

    have hBlineOA :
        HilbertIncidence.OnLine B lineOA := by
      rw [hEq]
      exact hBlineOB

    exact hBoffOA hBlineOA

  have hOppEB :
      HilbertOppositeSide Geo E B lineOA :=
    ⟨hEoffOA,
     hBoffOA,
     ⟨O, hEOB, hOlineOA⟩⟩

  --------------------------------------------------------------------
  -- n meets BE at O.
  --------------------------------------------------------------------

  have hMeetsBE :
      HilbertSegmentMeetsLine Geo B E n :=
    ⟨O, hBOE, hOn⟩

  --------------------------------------------------------------------
  -- n cannot meet EA.
  --------------------------------------------------------------------

  have hNotMeetsEA :
      Not (HilbertSegmentMeetsLine Geo E A n) := by

    rintro ⟨Y, hEYA, hYn⟩

    have hAYE :
        Geo.Between A Y E :=
      (HilbertOrder.between_incidence
        E Y A hEYA).2.2.2.2

    --------------------------------------------------------------
    -- Because A-Y-E and E lies on OB, A and Y are on the
    -- same side of OB.  Hence X and Y are on the same side of OB.
    --------------------------------------------------------------

    have hAYsameOB :
        HilbertSameSide Geo A Y lineOB :=
      hilbert_between_sameSide_of_endpoint_on_line
        Geo
        A Y E
        lineOB
        hAYE
        hElineOB
        hAoffOB

    have hXYsameOB :
        HilbertSameSide Geo X Y lineOB :=
      hilbert_sameSide_trans
        Geo
        X A Y
        lineOB
        hXA
        hAYsameOB

    have hYoffOB :
        Not (HilbertIncidence.OnLine Y lineOB) :=
      hXYsameOB.2.1

    have hYO : Y ≠ O := by
      intro hEq
      subst Y
      exact hYoffOB hOlineOB

    --------------------------------------------------------------
    -- Y cannot lie on the opposite ray from X, since then
    -- segment XY would cross OB at O.
    --------------------------------------------------------------

    have hNotXOY :
        Not (Geo.Between X O Y) := by

      intro hXOY

      have hOppXY :
          HilbertOppositeSide Geo X Y lineOB :=
        ⟨hXoffOB,
         hYoffOB,
         ⟨O, hXOY, hOlineOB⟩⟩

      exact
        (hilbert_oppositeSide_not_sameSide
          Geo X Y lineOB hOppXY)
          hXYsameOB

    have hOXYcol :
        PrimCollinear Geo O X Y :=
      ⟨n, hOn, hXn, hYn⟩

    have hRayOXY :
        HilbertSameRay Geo O X Y :=
      ⟨hXO,
       hYO,
       hOXYcol,
       hNotXOY⟩

    --------------------------------------------------------------
    -- Points X and Y on this ray are on the same side of OA.
    --------------------------------------------------------------

    have hRayOXX :
        HilbertSameRay Geo O X X :=
      hilbert_sameRay_refl
        Geo O X hXO

    have hXYsameOA :
        HilbertSameSide Geo X Y lineOA :=
      hilbert_sameRay_points_sameSide
        Geo
        O X
        X Y
        A
        n lineOA
        hOn
        hXn
        hOlineOA
        hAlineOA
        hAoffn
        hRayOXX
        hRayOXY

    have hYXsameOA :
        HilbertSameSide Geo Y X lineOA :=
      hilbert_sameSide_symm
        Geo X Y lineOA hXYsameOA

    have hYBsameOA :
        HilbertSameSide Geo Y B lineOA :=
      hilbert_sameSide_trans
        Geo
        Y X B
        lineOA
        hYXsameOA
        hXB

    --------------------------------------------------------------
    -- Since E-Y-A and A lies on OA, E and Y are on the same
    -- side of OA.
    --------------------------------------------------------------

    have hEYsameOA :
        HilbertSameSide Geo E Y lineOA :=
      hilbert_between_sameSide_of_endpoint_on_line
        Geo
        E Y A
        lineOA
        hEYA
        hAlineOA
        hEoffOA

    have hEBsameOA :
        HilbertSameSide Geo E B lineOA :=
      hilbert_sameSide_trans
        Geo
        E Y B
        lineOA
        hEYsameOA
        hYBsameOA

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo E B lineOA hOppEB)
        hEBsameOA

  --------------------------------------------------------------------
  -- Pasch in triangle B-E-A:
  --
  -- n enters through BE and cannot leave through EA,
  -- therefore it meets BA.
  --------------------------------------------------------------------

  have hMeetsBA :
      HilbertSegmentMeetsLine Geo B A n :=
    hilbert_pasch_forced
      Geo
      B E A
      n
      hBEA
      hBoffn
      hEoffn
      hAoffn
      hMeetsBE
      hNotMeetsEA

  rcases hMeetsBA with
    ⟨H, hBHA, hHn⟩

  have hAHB :
      Geo.Between A H B :=
    (HilbertOrder.between_incidence
      B H A hBHA).2.2.2.2

  --------------------------------------------------------------------
  -- The intersection lies on the ray OX, not on its opposite ray.
  --------------------------------------------------------------------

  have hAHsameOB :
      HilbertSameSide Geo A H lineOB :=
    hilbert_between_sameSide_of_endpoint_on_line
      Geo
      A H B
      lineOB
      hAHB
      hBlineOB
      hAoffOB

  have hXHsameOB :
      HilbertSameSide Geo X H lineOB :=
    hilbert_sameSide_trans
      Geo
      X A H
      lineOB
      hXA
      hAHsameOB

  have hHoffOB :
      Not (HilbertIncidence.OnLine H lineOB) :=
    hXHsameOB.2.1

  have hHO : H ≠ O := by
    intro hEq
    subst H
    exact hHoffOB hOlineOB

  have hOXHcol :
      PrimCollinear Geo O X H :=
    ⟨n, hOn, hXn, hHn⟩

  have hNotXOH :
      Not (Geo.Between X O H) := by

    intro hXOH

    have hOppXH :
        HilbertOppositeSide Geo X H lineOB :=
      ⟨hXoffOB,
       hHoffOB,
       ⟨O, hXOH, hOlineOB⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo X H lineOB hOppXH)
        hXHsameOB

  have hRayOXH :
      HilbertSameRay Geo O X H :=
    ⟨hXO,
     hHO,
     hOXHcol,
     hNotXOH⟩

  exact
    ⟨H, hAHB, hRayOXH⟩


------------------------------------------------------------------------
-- Hilbert Theorem 31
-- Parallel ray through a vertex
------------------------------------------------------------------------

/--
First geometric step in Hilbert Theorem 31.

For a noncollinear triangle ABC and the line AB, construct a point D
on the side of AB opposite to C such that

  angle ABC ~= angle BAD

and hence

  AD || BC.

Only Groups I--III are used here. The Euclidean direction of
Theorem 30 is not yet needed.
-/
theorem hilbert_triangle_parallel_ray
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base) :
    Exists fun D : Geo.Point =>
      HilbertOppositeSide Geo C D base /\
      Geo.AngleCongruent A B C B A D /\
      Geo.Parallel A D B C := by

  have hAB : Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC : Not (A = C) :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  have hCA : Not (C = A) :=
    Ne.symm hAC

  --------------------------------------------------------------------
  -- C is off AB.
  --------------------------------------------------------------------

  have hCoff :
      Not (HilbertIncidence.OnLine C base) := by
    intro hCbase
    exact
      hABC
        <| PrimCollinear.mk
          (Geo := Geo)
          hAbase
          hBbase
          hCbase

  --------------------------------------------------------------------
  -- Extend CA beyond A:
  --
  --     C - A - S.
  --
  -- Thus S is on the side of AB opposite to C.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        C A hCA with
    ⟨S, hCAS⟩

  have hCASData :=
    HilbertOrder.between_incidence
      C A S hCAS

  have hAS : Not (A = S) :=
    hCASData.2.1

  have hSoff :
      Not (HilbertIncidence.OnLine S base) := by
    intro hSbase

    have hASC :
        Collinear Geo A S C :=
      PrimCollinearCycle
        Geo C A S
        hCASData.2.2.2.1

    have hCbase :
        HilbertIncidence.OnLine C base :=
      hilbert_collinear_on_line
        Geo
        A S C
        base
        hAS
        hAbase
        hSbase
        hASC

    exact hCoff hCbase

  have hOppCS :
      HilbertOppositeSide Geo C S base :=
    ⟨hCoff,
     hSoff,
     ⟨A, hCAS, hAbase⟩⟩

  --------------------------------------------------------------------
  -- Copy angle ABC at A, using AB as the first ray and choosing
  -- the side containing S.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A B C
        B A S
        hABC
        (Ne.symm hAB)
        base
        hBbase
        hAbase
        hSoff with
    ⟨D, hDSsame, hAngleABC_BAD, _⟩

  have hSDsame :
      HilbertSameSide Geo S D base :=
    hilbert_sameSide_symm
      Geo D S base hDSsame

  have hOppCD :
      HilbertOppositeSide Geo C D base :=
    hilbert_oppositeSide_transport_right
      Geo
      C S D
      base
      hOppCS
      hSDsame

  --------------------------------------------------------------------
  -- Choose an interior point M of AB to name the transversal rays.
  --------------------------------------------------------------------

  rcases
      hilbert_between_exists
        Geo A B hAB with
    ⟨M, hAMB⟩

  have hBMA :
      Geo.Between B M A :=
    (HilbertOrder.between_incidence
      A M B hAMB).2.2.2.2

  have hRayAMB :
      HilbertSameRay Geo A M B :=
    hilbert_sameRay_of_between
      Geo A M B hAMB

  have hRayBMA :
      HilbertSameRay Geo B M A :=
    hilbert_sameRay_of_between
      Geo B M A hBMA

  --------------------------------------------------------------------
  -- Rewrite the copied angle as the alternate-angle statement
  --
  --     angle MAD ~= angle MBC.
  --------------------------------------------------------------------

  have hBAD_ABC :
      Geo.AngleCongruent B A D A B C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B C
      B A D
      hAngleABC_BAD

  have hLeft :
      Geo.Angle M A D =
      Geo.Angle B A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A M B D hRayAMB

  have hRight :
      Geo.Angle M B C =
      Geo.Angle A B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B M A C hRayBMA

  have hAlternate :
      Geo.AngleCongruent M A D M B C := by
    unfold Geometry.Geo.AngleCongruent
      at hBAD_ABC |-
    rw [hLeft, hRight]
    exact hBAD_ABC

  --------------------------------------------------------------------
  -- D and C lie on opposite sides of transversal AB.
  -- Equal alternate angles therefore give AD || BC.
  --------------------------------------------------------------------

  have hOppDC :
      HilbertOppositeSide Geo D C base :=
    hilbert_oppositeSide_symm
      Geo C D base hOppCD

  have hParallel :
      Geo.Parallel A D B C :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      A D
      B M C
      base
      hAMB
      hAbase
      hBbase
      hOppDC
      hAlternate
  exact
    ⟨D,
     hOppCD,
     hAngleABC_BAD,
     hParallel⟩


------------------------------------------------------------------------
-- Hilbert Theorem 31
-- Opposite extension of the parallel through A
------------------------------------------------------------------------

/--
If AD is parallel to BC, extend DA beyond A to E.

Then D-A-E and AE is still parallel to BC.
-/
theorem hilbert_parallel_opposite_extension
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hParallel : Geo.Parallel A D B C) :
    Exists fun E : Geo.Point =>
      Geo.Between D A E /\
      Geo.Parallel A E B C := by

  have hDA : Not (D = A) :=
    Ne.symm hParallel.1

  rcases
      HilbertOrder.between_extension
        D A hDA with
    ⟨E, hDAE⟩

  have hDAEData :=
    HilbertOrder.between_incidence
      D A E hDAE

  have hAE : Not (A = E) :=
    hDAEData.2.1

  rcases hDAEData.2.2.2.1 with
    ⟨lineADE, hDline, hAline, hEline⟩

  have hPointLine :
      Geo.PointLine A D =
      Geo.PointLine A E :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      A D
      A E
      lineADE
      hParallel.1
      hAE
      hAline
      hDline
      hAline
      hEline

  have hParallelAE :
      Geo.Parallel A E B C := by
    refine
      ⟨hAE,
       hParallel.2.1,
       ?_⟩

    rw [← hPointLine]
    exact hParallel.2.2

  exact
    ⟨E,
     hDAE,
     hParallelAE⟩


------------------------------------------------------------------------
-- Hilbert Theorem 31
-- Second angle from the parallel through A
------------------------------------------------------------------------

/--
If AE is parallel to BC and E,B lie on opposite sides of the
transversal AC, then

  angle CAE ~= angle ACB.

This is exactly the Euclidean direction of Hilbert Theorem 30.
-/
theorem hilbert_triangle_parallel_second_angle
    [HilbertEuclideanPlane Geo]
    (A B C E : Geo.Point)
    (trans : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hAtrans : HilbertIncidence.OnLine A trans)
    (hCtrans : HilbertIncidence.OnLine C trans)
    (hOppEB : HilbertOppositeSide Geo E B trans)
    (hParallel : Geo.Parallel A E B C) :
    Geo.AngleCongruent C A E A C B := by

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC : Not (A = C) :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  rcases
      hilbert_between_exists
        Geo A C hAC with
    ⟨M, hAMC⟩

  have hCMA :
      Geo.Between C M A :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.2

  have hRayAMC :
      HilbertSameRay Geo A M C :=
    hilbert_sameRay_of_between
      Geo A M C hAMC

  have hRayCMA :
      HilbertSameRay Geo C M A :=
    hilbert_sameRay_of_between
      Geo C M A hCMA

  have hParallel' :
      Geo.Parallel A E C B :=
    (Geo.parallel_swap_second
      A E B C).mp hParallel

  have hRaw :
      Geo.AngleCongruent
        M A E
        M C B :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo
      A E
      C M B
      trans
      hAMC
      hAtrans
      hCtrans
      hOppEB
      hParallel'

  have hLeft :
      Geo.Angle M A E =
      Geo.Angle C A E :=
    hilbert_angle_eq_of_sameRay_first
      Geo A M C E hRayAMC

  have hRight :
      Geo.Angle M C B =
      Geo.Angle A C B :=
    hilbert_angle_eq_of_sameRay_first
      Geo C M A B hRayCMA

  unfold Geometry.Geo.AngleCongruent
    at hRaw ⊢

  rw [hLeft, hRight] at hRaw

  exact hRaw


------------------------------------------------------------------------
-- Parallel lines and side separation
------------------------------------------------------------------------

/--
If AB is parallel to CD, then C and D lie on the same side
of the incidence line through A and B.
-/
theorem hilbert_parallel_second_endpoints_sameSide
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hParallel : Geo.Parallel A B C D) :
    Exists fun l : Geo.Line =>
      HilbertIncidence.OnLine A l /\
      HilbertIncidence.OnLine B l /\
      HilbertSameSide Geo C D l := by

  rcases
      HilbertPlaneIncidence.line_through
        A B hParallel.1 with
    ⟨lineAB, hAab, hBab⟩

  rcases
      HilbertPlaneIncidence.line_through
        C D hParallel.2.1 with
    ⟨lineCD, hCcd, hDcd⟩

  have hCoff :
      Not (HilbertIncidence.OnLine C lineAB) := by
    intro hCab

    have hCleft :
        C ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A B C
        lineAB
        hParallel.1
        hAab
        hBab).mpr hCab

    have hCright :
        C ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        C D C
        lineCD
        hParallel.2.1
        hCcd
        hDcd).mpr hCcd

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hCleft
        hCright

  have hDoff :
      Not (HilbertIncidence.OnLine D lineAB) := by
    intro hDab

    have hDleft :
        D ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A B D
        lineAB
        hParallel.1
        hAab
        hBab).mpr hDab

    have hDright :
        D ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        C D D
        lineCD
        hParallel.2.1
        hCcd
        hDcd).mpr hDcd

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hDleft
        hDright

  have hNoMeet :
      Not (HilbertSegmentMeetsLine Geo C D lineAB) := by
    rintro ⟨X, hCXD, hXab⟩

    have hXcd :
        HilbertIncidence.OnLine X lineCD :=
      hilbert_between_on_line
        Geo
        C X D
        lineCD
        hCcd
        hDcd
        hCXD

    have hXleft :
        X ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A B X
        lineAB
        hParallel.1
        hAab
        hBab).mpr hXab

    have hXright :
        X ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        C D X
        lineCD
        hParallel.2.1
        hCcd
        hDcd).mpr hXcd

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hXleft
        hXright

  have hSame :
      HilbertSameSide Geo C D lineAB :=
    ⟨hCoff,
     hDoff,
     Relation.ReflTransGen.single
       ⟨hCoff, hDoff, hNoMeet⟩⟩

  exact
    ⟨lineAB,
     hAab,
     hBab,
     hSame⟩


------------------------------------------------------------------------
-- Hilbert Theorem 31
-- C and E lie on the same side of AB
------------------------------------------------------------------------

/--
Assume C and D are on opposite sides of the line AB,
D-A-E, and AE is parallel to BC.

Then C and E lie on the same side of AB.
-/
theorem hilbert_triangle_parallel_extension_sameSide
    [HilbertOrder Geo]
    (A B C D E : Geo.Point)
    (base : Geo.Line)
    (hAbase : HilbertIncidence.OnLine A base)
    (hOppCD : HilbertOppositeSide Geo C D base)
    (hDAE : Geo.Between D A E)
    (hParallel : Geo.Parallel A E B C) :
    HilbertSameSide Geo C E base := by

  --------------------------------------------------------------------
  -- The segment CD crosses the base at some X.
  --------------------------------------------------------------------

  rcases hOppCD.2.2 with
    ⟨X, hCXD, hXbase⟩

  have hDXC :
      Geo.Between D X C :=
    (HilbertOrder.between_incidence
      C X D hCXD).2.2.2.2

  --------------------------------------------------------------------
  -- Triangle DCE is noncollinear.
  --
  -- Otherwise C would lie on AE.  But C also lies on BC,
  -- contradicting AE || BC.
  --------------------------------------------------------------------

  have hDAEData :=
    HilbertOrder.between_incidence
      D A E hDAE

  have hAE : A ≠ E :=
    hDAEData.2.1

  have hDE : D ≠ E :=
    hDAEData.2.2.1

  have hDCE :
      ¬ PrimCollinear Geo D C E := by
    intro hDCEcol

    have hAED :
        PrimCollinear Geo A E D :=
      PrimCollinearCycle
        Geo D A E
        hDAEData.2.2.2.1

    have hEDC :
        PrimCollinear Geo E D C :=
      PrimCollinearRotate
        Geo E C D
        (PrimCollinearSymm
          Geo D C E hDCEcol)

    have hAEC :
        PrimCollinear Geo A E C :=
      hilbert_primCollinear_trans
        Geo
        A E D C
        hDE.symm
        hAED
        hEDC

    rcases
        HilbertPlaneIncidence.line_through
          A E hAE with
      ⟨lineAE, hAae, hEae⟩

    have hCae :
        HilbertIncidence.OnLine C lineAE :=
      hilbert_collinear_on_line
        Geo
        A E C
        lineAE
        hAE
        hAae
        hEae
        hAEC

    rcases
        HilbertPlaneIncidence.line_through
          B C hParallel.2.1 with
      ⟨lineBC, hBbc, hCbc⟩

    have hCleft :
        C ∈ Geo.PointLine A E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A E C
        lineAE
        hParallel.1
        hAae
        hEae).mpr hCae

    have hCright :
        C ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        B C C
        lineBC
        hParallel.2.1
        hBbc
        hCbc).mpr hCbc

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hCleft
        hCright

  --------------------------------------------------------------------
  -- In triangle DCE the base line meets DC at X and DE at A.
  -- Hence the remaining vertices C and E are on the same side.
  --------------------------------------------------------------------

  exact
    hilbert_third_side_endpoints_sameSide
      Geo
      D C E
      X A
      base
      hDCE
      hDXC
      hDAE
      hXbase
      hAbase


------------------------------------------------------------------------
-- Hilbert Theorem 31
-- Crossbar gives the required opposite-side configuration
------------------------------------------------------------------------

/--
Let AE be parallel to BC.

If C and E lie on the same side of AB, then C lies inside angle EAB.
Hence the ray AC meets the open segment EB. Therefore E and B lie
on opposite sides of the line AC.
-/
theorem hilbert_triangle_parallel_crossbar_oppositeSide
    [HilbertOrder Geo]
    (A B C E : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCEsame : HilbertSameSide Geo C E base)
    (hParallel : Geo.Parallel A E B C) :
    Exists fun lineAC : Geo.Line =>
      HilbertIncidence.OnLine A lineAC /\
      HilbertIncidence.OnLine C lineAC /\
      HilbertOppositeSide Geo E B lineAC := by

  --------------------------------------------------------------------
  -- AE is an incidence line, and B,C lie on the same side of it.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_second_endpoints_sameSide
        Geo A E B C hParallel with
    ⟨lineAE, hAae, hEae, hBCsame⟩

  have hCBsame :
      HilbertSameSide Geo C B lineAE :=
    hilbert_sameSide_symm
      Geo B C lineAE hBCsame

  --------------------------------------------------------------------
  -- Thus C is inside angle EAB.
  --
  -- lineOA = AE
  -- lineOB = AB
  --------------------------------------------------------------------

  have hInside :
      HilbertInsideAngle Geo A E B C :=
    ⟨lineAE,
     base,
     hAae,
     hEae,
     hAbase,
     hBbase,
     hCEsame,
     hCBsame⟩

  --------------------------------------------------------------------
  -- Crossbar: ray AC meets the open segment EB.
  --------------------------------------------------------------------

  have hCross :
      HilbertRayMeetsSegment
        Geo A C E B :=
    hilbert_insideAngle_ray_meets_segment
      Geo A E B C hInside

  rcases hCross with
    ⟨H, hEHB, hRayACH⟩

  --------------------------------------------------------------------
  -- Construct the incidence line AC.
  --------------------------------------------------------------------

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC : Not (A = C) :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC with
    ⟨lineAC, hAac, hCac⟩

  have hHac :
      HilbertIncidence.OnLine H lineAC :=
    hilbert_collinear_on_line
      Geo
      A C H
      lineAC
      hAC
      hAac
      hCac
      (hilbert_sameRay_collinear
        Geo A C H hRayACH)

  --------------------------------------------------------------------
  -- B is off AC by noncollinearity of triangle ABC.
  --------------------------------------------------------------------

  have hBoff :
      Not (HilbertIncidence.OnLine B lineAC) := by
    intro hBac
    exact
      hABC
        ⟨lineAC,
         hAac,
         hBac,
         hCac⟩

  --------------------------------------------------------------------
  -- E is also off AC.
  --
  -- Otherwise AE = AC, so C lies on AE.  Since C also lies on BC,
  -- the parallel lines AE and BC would have the common point C.
  --------------------------------------------------------------------

  have hAE : Not (A = E) :=
    hParallel.1

  have hEoff :
      Not (HilbertIncidence.OnLine E lineAC) := by
    intro hEac

    have hEq :
        lineAE = lineAC :=
      HilbertPlaneIncidence.line_unique
        A E hAE
        lineAE lineAC
        hAae hEae
        hAac hEac

    have hCae :
        HilbertIncidence.OnLine C lineAE := by
      rw [hEq]
      exact hCac

    have hCleft :
        C ∈ Geo.PointLine A E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A E C
        lineAE
        hParallel.1
        hAae
        hEae).mpr hCae

    rcases
        HilbertPlaneIncidence.line_through
          B C hParallel.2.1 with
      ⟨lineBC, hBbc, hCbc⟩

    have hCright :
        C ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        B C C
        lineBC
        hParallel.2.1
        hBbc
        hCbc).mpr hCbc

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hCleft
        hCright

  --------------------------------------------------------------------
  -- H lies between E and B and lies on AC.
  --------------------------------------------------------------------

  have hOppEB :
      HilbertOppositeSide Geo E B lineAC :=
    ⟨hEoff,
     hBoff,
     ⟨H, hEHB, hHac⟩⟩

  exact
    ⟨lineAC,
     hAac,
     hCac,
     hOppEB⟩


------------------------------------------------------------------------
-- Hilbert Theorem 31
------------------------------------------------------------------------

/--
Hilbert Theorem 31 in the geometric form appropriate to the current
angle language.

For every noncollinear triangle ABC there exist points D,E with

  D - A - E,

such that

  angle ABC ~= angle BAD
  angle ACB ~= angle CAE.

Thus the three angles of triangle ABC are represented by the three
adjacent angles

  BAD, BAC, CAE

which together form the straight angle DAE.

This is the content of Hilbert's statement that the sum of the angles
of a triangle is equal to two right angles, without introducing a
separate arithmetic of angles.
-/
theorem hilbert_triangle_angle_sum_straight_data
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C)) :
    Exists fun D : Geo.Point =>
    Exists fun E : Geo.Point =>
      Geo.Between D A E /\
      Geo.AngleCongruent A B C B A D /\
      Geo.AngleCongruent A C B C A E := by

  --------------------------------------------------------------------
  -- The base line AB.
  --------------------------------------------------------------------

  have hAB : Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  rcases
      HilbertPlaneIncidence.line_through
        A B hAB with
    ⟨base, hAbase, hBbase⟩

  --------------------------------------------------------------------
  -- Construct D on the opposite side of AB from C such that
  --
  --     angle ABC ~= angle BAD
  --     AD || BC.
  --------------------------------------------------------------------

  rcases
      hilbert_triangle_parallel_ray
        Geo
        A B C
        base
        hABC
        hAbase
        hBbase with
    ⟨D, hOppCD, hAngleB, hParallelAD⟩

  --------------------------------------------------------------------
  -- Extend DA beyond A:
  --
  --     D - A - E,
  --
  -- with AE still parallel to BC.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_opposite_extension
        Geo
        A B C D
        hParallelAD with
    ⟨E, hDAE, hParallelAE⟩

  --------------------------------------------------------------------
  -- C and E lie on the same side of AB.
  --------------------------------------------------------------------

  have hCEsame :
      HilbertSameSide Geo C E base :=
    hilbert_triangle_parallel_extension_sameSide
      Geo
      A B C D E
      base
      hAbase
      hOppCD
      hDAE
      hParallelAE

  --------------------------------------------------------------------
  -- Crossbar gives the orientation needed for Theorem 30:
  -- E and B lie on opposite sides of AC.
  --------------------------------------------------------------------

  rcases
      hilbert_triangle_parallel_crossbar_oppositeSide
        Geo
        A B C E
        base
        hABC
        hAbase
        hBbase
        hCEsame
        hParallelAE with
    ⟨lineAC, hAac, hCac, hOppEB⟩

  --------------------------------------------------------------------
  -- Euclidean direction of Theorem 30:
  --
  --     angle CAE ~= angle ACB.
  --------------------------------------------------------------------

  have hAngleCraw :
      Geo.AngleCongruent C A E A C B :=
    hilbert_triangle_parallel_second_angle
      Geo
      A B C E
      lineAC
      hABC
      hAac
      hCac
      hOppEB
      hParallelAE

  have hAngleC :
      Geo.AngleCongruent A C B C A E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C A E
      A C B
      hAngleCraw

  exact
    ⟨D,
     E,
     hDAE,
     hAngleB,
     hAngleC⟩

------------------------------------------------------------------------
-- Hilbert Grundlagen transfer block II
--
-- General Hilbert theory extracted from HilbertGrundlagenPascalTest.
-- Paste INSIDE namespace Geometry, before the final `end Geometry`.
--
-- This block contains no special-Pascal declarations.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Chapter I, sec. 6
-- Hilbert Theorem 11
------------------------------------------------------------------------

/--
Hilbert Theorem 11.

If AB is congruent to AC in a noncollinear triangle ABC,
then the base angles at B and C are congruent.

The proof uses Hilbert III.5 directly and has no dependency
on HilbertInterface.
-/
theorem hilbert_theorem_11_isosceles_base_angles
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hNC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C) :
    Geo.AngleCongruent A B C A C B := by

  have hNC' : Not (Collinear Geo A C B) := by
    intro hACB
    exact hNC (PrimCollinearRotate Geo A C B hACB)

  have hBAC : Not (PrimCollinear Geo B A C) := by
    intro hBAC
    exact hNC (PrimCollinearSwap Geo B A C hBAC)

  have hAngleA :
      Geo.AngleCongruent B A C C A B := by
    have hRefl :
        Geo.AngleCongruent B A C B A C :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) B A C hBAC

    exact
      (Geo.angle_congruent_reverse_second
        B A C B A C).mp hRefl

  have hACAB :
      Geo.Congruent A C A B :=
    hilbert_congruent_symmetry
      Geo A B A C hABAC

  exact
    HilbertCongruence.sas
      (Geo := Geo)
      A B C
      A C B
      hNC
      hNC'
      hABAC
      hACAB
      hAngleA



------------------------------------------------------------------------
-- Hilbert Theorem 12
-- Full SAS consequence needed by Theorem 15
------------------------------------------------------------------------

/--
The primitive axiom III.5 gives the angle consequences.
The already derived HilbertAxioms lemmas supply the third side
and the remaining angle.

-/
theorem hilbert_theorem_12_SAS
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hDEF : Not (Collinear Geo D E F))
    (hAB : Geo.Congruent A B D E)
    (hAngleA : Geo.AngleCongruent B A C E D F)
    (hAC : Geo.Congruent A C D F) :
    TriangleCongruenceResult Geo A B C D E F := by

  have hAngles :=
    hilbert_sas_remaining_angles
      Geo
      A B C
      D E F
      hABC
      hDEF
      hAB
      hAC
      hAngleA

  have hNeeded :=
    hilbert_sas_third_side_and_angle
      Geo
      A B C
      D E F
      hABC
      hDEF
      hAB
      hAC
      hAngleA

  exact
    {
      sideAB := hAB
      sideBC := hNeeded.1
      sideAC := hAC
      angleA := hAngleA
      angleB := hAngles.1
      angleC := hNeeded.2
    }


/--
If P and Q lie on the same ray determined by O and X,
then P and Q lie on the same ray from O.

This is a pure order/incidence consequence.
-/
theorem hilbert_sameRay_common_reference
    [HilbertOrder Geo]
    (O X P Q : Geo.Point)
    (hXP : HilbertSameRay Geo O X P)
    (hXQ : HilbertSameRay Geo O X Q) :
    HilbertSameRay Geo O P Q := by

  rcases hXP.2.2.1 with
    ⟨l, hOl, hXl, hPl⟩

  rcases hXQ.2.2.1 with
    ⟨m, hOm, hXm, hQm⟩

  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      O X hXP.1.symm
      l m
      hOl hXl
      hOm hXm

  subst m

  refine
    ⟨hXP.2.1,
     hXQ.2.1,
     ⟨l, hOl, hPl, hQm⟩,
     ?_⟩

  intro hPOQ

  have hPX :
      HilbertSameRay Geo O P X :=
    hilbert_sameRay_symm
      Geo O X P hXP

  have hQX :
      HilbertSameRay Geo O Q X :=
    hilbert_sameRay_symm
      Geo O X Q hXQ

  have hXOX :
      Geo.Between X O X :=
    hilbert_between_transport_sameRays
      Geo
      P O Q
      X X
      hPOQ
      hPX
      hQX

  exact
    (HilbertOrder.between_incidence
      X O X hXOX).2.2.1 rfl

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Auxiliary construction
------------------------------------------------------------------------

/--
Auxiliary construction for the first same-side case of Hilbert
Theorem 15.

H is the point where ray OA meets segment CB.

On the corresponding rays from O' we construct:

  O'K' congruent OC,
  O'L' congruent OB,
  O'H' congruent OH.

No angle argument is used yet.
-/
theorem hilbert_theorem_15_case1_construct
    [HilbertCongruence Geo]
    (O A B C O' A' B' C' : Geo.Point)
    (l' : Geo.Line)
    (hO'B' : O' ≠ B')
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hA'off : Not (HilbertIncidence.OnLine A' l'))
    (hC'off : Not (HilbertIncidence.OnLine C' l'))
    (hRay :
      HilbertRayMeetsSegment Geo O A C B) :
    Exists fun H : Geo.Point =>
    Exists fun K' : Geo.Point =>
    Exists fun L' : Geo.Point =>
    Exists fun H' : Geo.Point =>
      Geo.Between C H B /\
      HilbertSameRay Geo O A H /\
      HilbertSameRay Geo O' C' K' /\
      HilbertSameRay Geo O' B' L' /\
      HilbertSameRay Geo O' A' H' /\
      Geo.Congruent O C O' K' /\
      Geo.Congruent O B O' L' /\
      Geo.Congruent O H O' H' := by

  rcases hRay with
    ⟨H, hCHB, hRayAH⟩

  have hO'C' : O' ≠ C' := by
    intro hEq
    subst C'
    exact hC'off hO'l'

  have hO'A' : O' ≠ A' := by
    intro hEq
    subst A'
    exact hA'off hO'l'

  --------------------------------------------------------------------
  -- Construct K' on ray O'C' with O'K' congruent OC.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O C
        O' C'
        hO'C' with
    ⟨K', hRayC'K', hO'K'_OC⟩

  have hOC_O'K' :
      Geo.Congruent O C O' K' :=
    hilbert_congruent_symmetry
      Geo O' K' O C hO'K'_OC

  --------------------------------------------------------------------
  -- Construct L' on ray O'B' with O'L' congruent OB.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O B
        O' B'
        hO'B' with
    ⟨L', hRayB'L', hO'L'_OB⟩

  have hOB_O'L' :
      Geo.Congruent O B O' L' :=
    hilbert_congruent_symmetry
      Geo O' L' O B hO'L'_OB

  --------------------------------------------------------------------
  -- Construct H' on ray O'A' with O'H' congruent OH.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O H
        O' A'
        hO'A' with
    ⟨H', hRayA'H', hO'H'_OH⟩

  have hOH_O'H' :
      Geo.Congruent O H O' H' :=
    hilbert_congruent_symmetry
      Geo O' H' O H hO'H'_OH

  exact
    ⟨H,
     K',
     L',
     H',
     hCHB,
     hRayAH,
     hRayC'K',
     hRayB'L',
     hRayA'H',
     hOC_O'K',
     hOB_O'L',
     hOH_O'H'⟩

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Transport of the two component angles
------------------------------------------------------------------------

/--
Transport the two component-angle congruences to the auxiliary
points constructed on the corresponding rays.

No SAS argument is used here.
-/
theorem hilbert_theorem_15_case1_transport
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' H K' L' H' : Geo.Point)
    (hRayAH : HilbertSameRay Geo O A H)
    (hRayC'K' : HilbertSameRay Geo O' C' K')
    (hRayB'L' : HilbertSameRay Geo O' B' L')
    (hRayA'H' : HilbertSameRay Geo O' A' H')
    (hAB :
      Geo.AngleCongruent A O B A' O' B')
    (hBC :
      Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent H O B H' O' L' /\
    Geo.AngleCongruent B O C L' O' K' := by

  --------------------------------------------------------------------
  -- First component:
  --
  --   angle AOB = angle A'O'B'
  --
  -- becomes
  --
  --   angle HOB = angle H'O'L'.
  --------------------------------------------------------------------

  have hAngleHOB :
      Geo.AngleCongruent H O B H' O' L' := by

    have hLeft :
        Geo.Angle A O B =
        Geo.Angle H O B :=
      hilbert_angle_eq_of_sameRay_first
        Geo O A H B hRayAH

    have hRightFirst :
        Geo.Angle A' O' B' =
        Geo.Angle H' O' B' :=
      hilbert_angle_eq_of_sameRay_first
        Geo O' A' H' B' hRayA'H'

    have hRightSecond :
        Geo.Angle H' O' B' =
        Geo.Angle H' O' L' :=
      hilbert_angle_eq_of_sameRay_second
        Geo O' H' B' L' hRayB'L'

    have hRight :
        Geo.Angle A' O' B' =
        Geo.Angle H' O' L' :=
      hRightFirst.trans hRightSecond

    unfold Geometry.Geo.AngleCongruent at hAB
    unfold Geometry.Geo.AngleCongruent

    rw [← hLeft, ← hRight]

    exact hAB

  --------------------------------------------------------------------
  -- Second component:
  --
  --   angle BOC = angle B'O'C'
  --
  -- becomes
  --
  --   angle BOC = angle L'O'K'.
  --------------------------------------------------------------------

  have hAngleBOC :
      Geo.AngleCongruent B O C L' O' K' := by

    have hRightFirst :
        Geo.Angle B' O' C' =
        Geo.Angle L' O' C' :=
      hilbert_angle_eq_of_sameRay_first
        Geo O' B' L' C' hRayB'L'

    have hRightSecond :
        Geo.Angle L' O' C' =
        Geo.Angle L' O' K' :=
      hilbert_angle_eq_of_sameRay_second
        Geo O' L' C' K' hRayC'K'

    have hRight :
        Geo.Angle B' O' C' =
        Geo.Angle L' O' K' :=
      hRightFirst.trans hRightSecond

    unfold Geometry.Geo.AngleCongruent at hBC
    unfold Geometry.Geo.AngleCongruent

    rw [← hRight]

    exact hBC

  exact
    ⟨hAngleHOB, hAngleBOC⟩

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Noncollinearity of the four SAS triangles
------------------------------------------------------------------------

/--
The auxiliary construction in the first same-side case of Hilbert
Theorem 15 produces four noncollinear triangles needed for two
applications of Theorem 12.
-/
theorem hilbert_theorem_15_case1_noncollinear
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' H K' L' H' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : Not (HilbertIncidence.OnLine A l))
    (hCoff : Not (HilbertIncidence.OnLine C l))
    (hA'off : Not (HilbertIncidence.OnLine A' l'))
    (hC'off : Not (HilbertIncidence.OnLine C' l'))
    (hRayAH : HilbertSameRay Geo O A H)
    (hRayC'K' : HilbertSameRay Geo O' C' K')
    (hRayB'L' : HilbertSameRay Geo O' B' L')
    (hRayA'H' : HilbertSameRay Geo O' A' H') :
    Not (Collinear Geo O B H) /\
    Not (Collinear Geo O' L' H') /\
    Not (Collinear Geo O B C) /\
    Not (Collinear Geo O' L' K') := by

  --------------------------------------------------------------------
  -- First establish that L' lies on l'.
  --------------------------------------------------------------------

  have hO'L' : O' ≠ L' :=
    hRayB'L'.2.1.symm

  have hL'line :
      HilbertIncidence.OnLine L' l' := by

    rcases hRayB'L'.2.2.1 with
      ⟨m, hO'm, hB'm, hL'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        m l'
        hO'm hB'm
        hO'l' hB'l'

    rw [← hEq]

    exact hL'm

  --------------------------------------------------------------------
  -- H' is off l'.
  --------------------------------------------------------------------

  have hO'H' : O' ≠ H' :=
    hRayA'H'.2.1.symm

  have hH'off :
      Not (HilbertIncidence.OnLine H' l') := by

    intro hH'line

    rcases hRayA'H'.2.2.1 with
      ⟨m, hO'm, hA'm, hH'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' H' hO'H'
        m l'
        hO'm hH'm
        hO'l' hH'line

    have hA'line :
        HilbertIncidence.OnLine A' l' := by
      rw [← hEq]
      exact hA'm

    exact hA'off hA'line

  --------------------------------------------------------------------
  -- K' is off l'.
  --------------------------------------------------------------------

  have hO'K' : O' ≠ K' :=
    hRayC'K'.2.1.symm

  have hK'off :
      Not (HilbertIncidence.OnLine K' l') := by

    intro hK'line

    rcases hRayC'K'.2.2.1 with
      ⟨m, hO'm, hC'm, hK'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' K' hO'K'
        m l'
        hO'm hK'm
        hO'l' hK'line

    have hC'line :
        HilbertIncidence.OnLine C' l' := by
      rw [← hEq]
      exact hC'm

    exact hC'off hC'line

  --------------------------------------------------------------------
  -- H is off l.
  --------------------------------------------------------------------

  have hOH : O ≠ H :=
    hRayAH.2.1.symm

  have hHoff :
      Not (HilbertIncidence.OnLine H l) := by

    intro hHline

    rcases hRayAH.2.2.1 with
      ⟨m, hOm, hAm, hHm⟩

    have hEq : m = l :=
      HilbertPlaneIncidence.line_unique
        O H hOH
        m l
        hOm hHm
        hOl hHline

    have hAline :
        HilbertIncidence.OnLine A l := by
      rw [← hEq]
      exact hAm

    exact hAoff hAline

  --------------------------------------------------------------------
  -- Triangle O-B-H.
  --------------------------------------------------------------------

  have hOBH :
      Not (Collinear Geo O B H) := by

    rintro ⟨m, hOm, hBm, hHm⟩

    have hEq : m = l :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        m l
        hOm hBm
        hOl hBl

    exact hHoff (hEq ▸ hHm)

  --------------------------------------------------------------------
  -- Triangle O'-L'-H'.
  --------------------------------------------------------------------

  have hO'L'H' :
      Not (Collinear Geo O' L' H') := by

    rintro ⟨m, hO'm, hL'm, hH'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' L' hO'L'
        m l'
        hO'm hL'm
        hO'l' hL'line

    exact hH'off (hEq ▸ hH'm)

  --------------------------------------------------------------------
  -- Triangle O-B-C.
  --------------------------------------------------------------------

  have hOBC :
      Not (Collinear Geo O B C) := by

    rintro ⟨m, hOm, hBm, hCm⟩

    have hEq : m = l :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        m l
        hOm hBm
        hOl hBl

    exact hCoff (hEq ▸ hCm)

  --------------------------------------------------------------------
  -- Triangle O'-L'-K'.
  --------------------------------------------------------------------

  have hO'L'K' :
      Not (Collinear Geo O' L' K') := by

    rintro ⟨m, hO'm, hL'm, hK'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' L' hO'L'
        m l'
        hO'm hL'm
        hO'l' hL'line

    exact hK'off (hEq ▸ hK'm)

  exact
    ⟨hOBH, hO'L'H', hOBC, hO'L'K'⟩

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Two applications of Theorem 12
------------------------------------------------------------------------

/--
Metric consequences of the auxiliary construction in the first
same-side case of Hilbert Theorem 15.

The two transported component angles and the constructed segment
congruences give two applications of Hilbert Theorem 12.
-/
theorem hilbert_theorem_15_case1_SAS
    [HilbertCongruence Geo]
    (O B C O' H K' L' H' : Geo.Point)
    (hOBH : Not (Collinear Geo O B H))
    (hO'L'H' : Not (Collinear Geo O' L' H'))
    (hOBC : Not (Collinear Geo O B C))
    (hO'L'K' : Not (Collinear Geo O' L' K'))
    (hOB_O'L' : Geo.Congruent O B O' L')
    (hOH_O'H' : Geo.Congruent O H O' H')
    (hOC_O'K' : Geo.Congruent O C O' K')
    (hAngleHOB :
      Geo.AngleCongruent H O B H' O' L')
    (hAngleBOC :
      Geo.AngleCongruent B O C L' O' K') :
    Geo.Congruent B H L' H' /\
    Geo.Congruent B C L' K' /\
    Geo.AngleCongruent O B H O' L' H' /\
    Geo.AngleCongruent O B C O' L' K' /\
    Geo.AngleCongruent O H B O' H' L' := by

  have hAngleBOH_1 :
      Geo.AngleCongruent B O H H' O' L' :=
    (Geo.angle_congruent_reverse_first
      H O B
      H' O' L').mp hAngleHOB

  have hAngleBOH :
      Geo.AngleCongruent B O H L' O' H' :=
    (Geo.angle_congruent_reverse_second
      B O H
      H' O' L').mp hAngleBOH_1

  have hTrianglesOBH :=
    hilbert_theorem_12_SAS
      Geo
      O B H
      O' L' H'
      hOBH
      hO'L'H'
      hOB_O'L'
      hAngleBOH
      hOH_O'H'

  have hTrianglesOBC :=
    hilbert_theorem_12_SAS
      Geo
      O B C
      O' L' K'
      hOBC
      hO'L'K'
      hOB_O'L'
      hAngleBOC
      hOC_O'K'

  exact
    ⟨hTrianglesOBH.sideBC,
     hTrianglesOBC.sideBC,
     hTrianglesOBH.angleB,
     hTrianglesOBC.angleB,
     hTrianglesOBH.angleC⟩

------------------------------------------------------------------------
-- Hilbert III.4
-- Uniqueness of angle construction
------------------------------------------------------------------------

/--
Local test version of the uniqueness consequence of Hilbert III.4.

If H and K lie on the same side of the reference line OL and
the angles OLH and OLK are congruent, then the rays LH and LK
are the same ray.
-/
theorem hilbert_theorem_15_angle_unique_common_ray
    [HilbertCongruence Geo]
    (O L H K : Geo.Point)
    (line : Geo.Line)
    (hOL : O ≠ L)
    (hOline : HilbertIncidence.OnLine O line)
    (hLline : HilbertIncidence.OnLine L line)
    (hHoff : Not (HilbertIncidence.OnLine H line))
    (hSameHK : HilbertSameSide Geo H K line)
    (hAngle :
      Geo.AngleCongruent O L H O L K) :
    Exists fun X : Geo.Point =>
      HilbertSameRay Geo L X H /\
      HilbertSameRay Geo L X K := by

  have hOLH :
      Not (Collinear Geo O L H) := by

    rintro ⟨m, hOm, hLm, hHm⟩

    have hEq : m = line :=
      HilbertPlaneIncidence.line_unique
        O L hOL
        m line
        hOm hLm
        hOline hLline

    exact hHoff (hEq ▸ hHm)

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        O L H
        O L H
        hOLH
        hOL
        line
        hOline
        hLline
        hHoff with
    ⟨X, hXHSame, hAngleX, hUnique⟩

  have hHHSame :
      HilbertSameSide Geo H H line :=
    hilbert_sameSide_refl
      Geo H line hHoff

  have hRayXH :
      HilbertSameRay Geo L X H :=
    hUnique
      H
      hHHSame
      (HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        O L H
        hOLH)

  have hKHSame :
      HilbertSameSide Geo K H line :=
    hilbert_sameSide_symm
      Geo H K line hSameHK

  have hRayXK :
      HilbertSameRay Geo L X K :=
    hUnique
      K
      hKHSame
      hAngle

  exact
    ⟨X, hRayXH, hRayXK⟩

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- H' and K' lie on the same ray from L'
------------------------------------------------------------------------

/--
In the first same-side case of Hilbert Theorem 15, the two SAS
conclusions imply that H' and K' determine the same ray from L'.

This is the last step before the order comparison of H' and K'.
-/
theorem hilbert_theorem_15_case1_sameRay
    [HilbertCongruence Geo]
    (O B C A' O' B' C' H K' L' H' : Geo.Point)
    (l' : Geo.Line)
    (hO'B' : O' ≠ B')
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hA'off : Not (HilbertIncidence.OnLine A' l'))
    (hC'off : Not (HilbertIncidence.OnLine C' l'))
    (hSame' : HilbertSameSide Geo A' C' l')
    (hRayA'H' : HilbertSameRay Geo O' A' H')
    (hRayC'K' : HilbertSameRay Geo O' C' K')
    (hRayB'L' : HilbertSameRay Geo O' B' L')
    (hCHB : Geo.Between C H B)
    (hAngleOBH :
      Geo.AngleCongruent O B H O' L' H')
    (hAngleOBC :
      Geo.AngleCongruent O B C O' L' K') :
    HilbertSameRay Geo L' H' K' := by

  --------------------------------------------------------------------
  -- H and C determine the same ray from B.
  --------------------------------------------------------------------

  have hBHC :
      Geo.Between B H C :=
    (HilbertOrder.between_incidence
      C H B hCHB).2.2.2.2

  have hRayBHC :
      HilbertSameRay Geo B H C :=
    hilbert_sameRay_of_between
      Geo B H C hBHC

  have hAngleOBH_eq_OBC :
      Geo.Angle O B H =
      Geo.Angle O B C :=
    hilbert_angle_eq_of_sameRay_second
      Geo B O H C hRayBHC

  --------------------------------------------------------------------
  -- Replace BH by BC in the first SAS angle conclusion.
  --------------------------------------------------------------------

  have hAngleOBC_L'H' :
      Geo.AngleCongruent O B C O' L' H' := by

    unfold Geometry.Geo.AngleCongruent at hAngleOBH ⊢

    rw [← hAngleOBH_eq_OBC]

    exact hAngleOBH

  --------------------------------------------------------------------
  -- Therefore the two angles at L' are congruent:
  --
  --   angle O'L'H' = angle O'L'K'.
  --------------------------------------------------------------------

  have hAngleL'H'_L'K' :
      Geo.AngleCongruent O' L' H' O' L' K' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O' L' H'
      O B C
      O' L' K'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        O B C
        O' L' H'
        hAngleOBC_L'H')
      hAngleOBC

  --------------------------------------------------------------------
  -- Basic nondegeneracy.
  --------------------------------------------------------------------

  have hO'A' : O' ≠ A' := by
    intro hEq
    subst A'
    exact hA'off hO'l'

  have hO'C' : O' ≠ C' := by
    intro hEq
    subst C'
    exact hC'off hO'l'

  have hO'L' : O' ≠ L' :=
    hRayB'L'.2.1.symm

  --------------------------------------------------------------------
  -- L' lies on l'.
  --------------------------------------------------------------------

  have hL'line :
      HilbertIncidence.OnLine L' l' := by

    rcases hRayB'L'.2.2.1 with
      ⟨m, hO'm, hB'm, hL'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        m l'
        hO'm hB'm
        hO'l' hB'l'

    rw [← hEq]

    exact hL'm

  --------------------------------------------------------------------
  -- H' is off l'.
  --------------------------------------------------------------------

  have hO'H' : O' ≠ H' :=
    hRayA'H'.2.1.symm

  have hH'off :
      Not (HilbertIncidence.OnLine H' l') := by

    intro hH'line

    rcases hRayA'H'.2.2.1 with
      ⟨m, hO'm, hA'm, hH'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' H' hO'H'
        m l'
        hO'm hH'm
        hO'l' hH'line

    have hA'line :
        HilbertIncidence.OnLine A' l' := by
      rw [← hEq]
      exact hA'm

    exact hA'off hA'line

  --------------------------------------------------------------------
  -- A' and H' lie on the same side of l'.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O' A' hO'A' with
    ⟨lineA', hO'lineA', hA'lineA'⟩

  have hB'notLineA' :
      Not (HilbertIncidence.OnLine B' lineA') := by

    intro hB'lineA'

    have hEq : l' = lineA' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        l' lineA'
        hO'l' hB'l'
        hO'lineA' hB'lineA'

    have hA'line :
        HilbertIncidence.OnLine A' l' := by
      rw [hEq]
      exact hA'lineA'

    exact hA'off hA'line

  have hA'H'Same :
      HilbertSameSide Geo A' H' l' :=
    hilbert_sameRay_points_sameSide
      Geo
      O' A'
      A' H'
      B'
      lineA' l'
      hO'lineA'
      hA'lineA'
      hO'l'
      hB'l'
      hB'notLineA'
      (hilbert_sameRay_refl
        Geo O' A' hO'A'.symm)
      hRayA'H'

  --------------------------------------------------------------------
  -- C' and K' lie on the same side of l'.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O' C' hO'C' with
    ⟨lineC', hO'lineC', hC'lineC'⟩

  have hB'notLineC' :
      Not (HilbertIncidence.OnLine B' lineC') := by

    intro hB'lineC'

    have hEq : l' = lineC' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        l' lineC'
        hO'l' hB'l'
        hO'lineC' hB'lineC'

    have hC'line :
        HilbertIncidence.OnLine C' l' := by
      rw [hEq]
      exact hC'lineC'

    exact hC'off hC'line

  have hC'K'Same :
      HilbertSameSide Geo C' K' l' :=
    hilbert_sameRay_points_sameSide
      Geo
      O' C'
      C' K'
      B'
      lineC' l'
      hO'lineC'
      hC'lineC'
      hO'l'
      hB'l'
      hB'notLineC'
      (hilbert_sameRay_refl
        Geo O' C' hO'C'.symm)
      hRayC'K'

  --------------------------------------------------------------------
  -- Transport A' ~ C' to H' ~ K'.
  --------------------------------------------------------------------

  have hH'A'Same :
      HilbertSameSide Geo H' A' l' :=
    hilbert_sameSide_symm
      Geo A' H' l' hA'H'Same

  have hH'C'Same :
      HilbertSameSide Geo H' C' l' :=
    hilbert_sameSide_trans
      Geo H' A' C' l'
      hH'A'Same
      hSame'

  have hH'K'Same :
      HilbertSameSide Geo H' K' l' :=
    hilbert_sameSide_trans
      Geo H' C' K' l'
      hH'C'Same
      hC'K'Same

  --------------------------------------------------------------------
  -- III.4 uniqueness: H' and K' determine one ray from L'.
  --------------------------------------------------------------------

  rcases
      hilbert_theorem_15_angle_unique_common_ray
        Geo
        O' L' H' K'
        l'
        hO'L'
        hO'l'
        hL'line
        hH'off
        hH'K'Same
        hAngleL'H'_L'K' with
    ⟨X, hRayXH', hRayXK'⟩

  exact
    hilbert_sameRay_common_reference
      Geo
      L' X H' K'
      hRayXH'
      hRayXK'

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Order of H' and K' on the common ray
------------------------------------------------------------------------

/--
If H lies between B and C, and the corresponding segments on the
common ray from L' have the same lengths, then H' lies between
L' and K'. At the same time HC is congruent to H'K'.
-/
theorem hilbert_theorem_15_case1_order
    [HilbertCongruence Geo]
    (B C H L' H' K' : Geo.Point)
    (hCHB : Geo.Between C H B)
    (hRayH'K' : HilbertSameRay Geo L' H' K')
    (hBH_L'H' : Geo.Congruent B H L' H')
    (hBC_L'K' : Geo.Congruent B C L' K') :
    Geo.Between L' H' K' /\
    Geo.Congruent H C H' K' := by

  --------------------------------------------------------------------
  -- Extend L'H' beyond H'.
  --------------------------------------------------------------------

  have hL'H' : Ne L' H' :=
    hRayH'K'.1.symm

  rcases
      HilbertOrder.between_extension
        L' H' hL'H' with
    ⟨T', hL'H'T'⟩

  have hH'T' : Ne H' T' :=
    (HilbertOrder.between_incidence
      L' H' T' hL'H'T').2.1

  --------------------------------------------------------------------
  -- Lay off HC from H' on the extension ray H'T'.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        H C
        H' T'
        hH'T' with
    ⟨J', hRayT'J', hH'J'_HC⟩

  --------------------------------------------------------------------
  -- Since J' is on the continuation of H'T',
  -- H' lies between L' and J'.
  --------------------------------------------------------------------

  have hRayL'L' :
      HilbertSameRay Geo H' L' L' :=
    hilbert_sameRay_refl
      Geo H' L' hL'H'

  have hL'H'J' :
      Geo.Between L' H' J' :=
    hilbert_between_transport_sameRays
      Geo
      L' H' T'
      L' J'
      hL'H'T'
      hRayL'L'
      hRayT'J'

  have hRayH'J' :
      HilbertSameRay Geo L' H' J' :=
    hilbert_sameRay_of_between
      Geo L' H' J' hL'H'J'

  --------------------------------------------------------------------
  -- B-H-C, so BC = BH + HC.
  -- Likewise L'-H'-J', so L'J' = L'H' + H'J'.
  --------------------------------------------------------------------

  have hBHC :
      Geo.Between B H C :=
    (HilbertOrder.between_incidence
      C H B hCHB).2.2.2.2

  have hHC_H'J' :
      Geo.Congruent H C H' J' :=
    hilbert_congruent_symmetry
      Geo
      H' J'
      H C
      hH'J'_HC

  have hBC_L'J' :
      Geo.Congruent B C L' J' :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      B H C
      L' H' J'
      hBHC
      hL'H'J'
      hBH_L'H'
      hHC_H'J'

  --------------------------------------------------------------------
  -- J' and K' are on the same ray from L' and both are at
  -- distance BC from L'. Uniqueness of segment construction gives
  -- J' = K'.
  --------------------------------------------------------------------

  have hL'J'_BC :
      Geo.Congruent L' J' B C :=
    hilbert_congruent_symmetry
      Geo
      B C
      L' J'
      hBC_L'J'

  have hL'K'_BC :
      Geo.Congruent L' K' B C :=
    hilbert_congruent_symmetry
      Geo
      B C
      L' K'
      hBC_L'K'

  have hJ'K' : J' = K' :=
    hilbert_segment_construction_unique
      Geo
      B C
      L' H'
      J' K'
      hRayH'J'
      hRayH'K'
      hL'J'_BC
      hL'K'_BC

  subst K'

  exact
    ⟨hL'H'J', hHC_H'J'⟩

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Adjacent angles and final Theorem 12
------------------------------------------------------------------------

theorem hilbert_theorem_15_case1_finalSAS
    [HilbertCongruence Geo]
    (O B C H O' L' H' K' : Geo.Point)
    (hCHB : Geo.Between C H B)
    (hL'H'K' : Geo.Between L' H' K')
    (hOBH : Not (Collinear Geo O B H))
    (hO'L'H' : Not (Collinear Geo O' L' H'))
    (hAngleOHB :
      Geo.AngleCongruent O H B O' H' L')
    (hOH_O'H' :
      Geo.Congruent O H O' H')
    (hHC_H'K' :
      Geo.Congruent H C H' K') :
    Geo.AngleCongruent H O C H' O' K' := by

  --------------------------------------------------------------------
  -- Reverse the order C-H-B to B-H-C.
  --------------------------------------------------------------------

  have hBHC :
      Geo.Between B H C :=
    (HilbertOrder.between_incidence
      C H B hCHB).2.2.2.2

  --------------------------------------------------------------------
  -- Noncollinearity needed for Hilbert Theorem 14.
  --------------------------------------------------------------------

  have hBHO :
      Not (Collinear Geo B H O) := by

    rintro ⟨m, hBm, hHm, hOm⟩

    exact
      hOBH
        ⟨m, hOm, hBm, hHm⟩

  have hL'H'O' :
      Not (Collinear Geo L' H' O') := by

    rintro ⟨m, hL'm, hH'm, hO'm⟩

    exact
      hO'L'H'
        ⟨m, hO'm, hL'm, hH'm⟩

  --------------------------------------------------------------------
  -- Reverse both rays in
  --
  --   angle OHB = angle O'H'L'
  --
  -- to obtain
  --
  --   angle BHO = angle L'H'O'.
  --------------------------------------------------------------------

  have hAngleBHO_1 :
      Geo.AngleCongruent B H O O' H' L' :=
    (Geo.angle_congruent_reverse_first
      O H B
      O' H' L').mp hAngleOHB

  have hAngleBHO :
      Geo.AngleCongruent B H O L' H' O' :=
    (Geo.angle_congruent_reverse_second
      B H O
      O' H' L').mp hAngleBHO_1

  --------------------------------------------------------------------
  -- Hilbert Theorem 14.
  --
  -- Since
  --
  --   B-H-C
  --   L'-H'-K'
  --
  -- the adjacent angles are congruent:
  --
  --   angle OHC = angle O'H'K'.
  --------------------------------------------------------------------

  have hAngleOHC :
      Geo.AngleCongruent O H C O' H' K' :=
    hilbert_adjacent_angles_congruent
      Geo
      B H O C
      L' H' O' K'
      hBHC
      hL'H'K'
      hBHO
      hL'H'O'
      hAngleBHO

  --------------------------------------------------------------------
  -- Triangle HOC is noncollinear.
  --------------------------------------------------------------------

  have hHOC :
      Not (Collinear Geo H O C) := by

    rintro ⟨m, hHm, hOm, hCm⟩

    rcases
        (HilbertOrder.between_incidence
          B H C hBHC).2.2.2.1 with
      ⟨n, hBn, hHn, hCn⟩

    have hHC : H ≠ C :=
      (HilbertOrder.between_incidence
        B H C hBHC).2.1

    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        H C hHC
        m n
        hHm hCm
        hHn hCn

    have hBm :
        HilbertIncidence.OnLine B m := by
      rw [hmn]
      exact hBn

    exact
      hOBH
        ⟨m, hOm, hBm, hHm⟩

  --------------------------------------------------------------------
  -- Triangle H'O'K' is noncollinear.
  --------------------------------------------------------------------

  have hH'O'K' :
      Not (Collinear Geo H' O' K') := by

    rintro ⟨m, hH'm, hO'm, hK'm⟩

    rcases
        (HilbertOrder.between_incidence
          L' H' K' hL'H'K').2.2.2.1 with
      ⟨n, hL'n, hH'n, hK'n⟩

    have hH'K' : H' ≠ K' :=
      (HilbertOrder.between_incidence
        L' H' K' hL'H'K').2.1

    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        H' K' hH'K'
        m n
        hH'm hK'm
        hH'n hK'n

    have hL'm :
        HilbertIncidence.OnLine L' m := by
      rw [hmn]
      exact hL'n

    exact
      hO'L'H'
        ⟨m, hO'm, hL'm, hH'm⟩

  --------------------------------------------------------------------
  -- Reverse both endpoints of
  --
  --   OH = O'H'
  --
  -- to obtain
  --
  --   HO = H'O'.
  --------------------------------------------------------------------

  have hHO_H'O' :
      Geo.Congruent H O H' O' :=
    (Geo.congruent_reverse_second
      H O O' H').mp
      ((Geo.congruent_reverse_first
        O H O' H').mp hOH_O'H')

  --------------------------------------------------------------------
  -- Final Hilbert Theorem 12:
  --
  --     triangle HOC
  --     triangle H'O'K'
  --
  -- with
  --
  --     HO = H'O'
  --     HC = H'K'
  --     angle OHC = angle O'H'K'.
  --------------------------------------------------------------------

  have hFinal :=
    hilbert_theorem_12_SAS
      Geo
      H O C
      H' O' K'
      hHOC
      hH'O'K'
      hHO_H'O'
      hAngleOHC
      hHC_H'K'

  exact hFinal.angleB

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Final transport back to the original rays
------------------------------------------------------------------------

/--
Transport the final auxiliary angle congruence back to the original
outer rays.

If H lies on ray OA, H' lies on ray O'A', and K' lies on ray O'C',
then

  angle HOC = angle H'O'K'

implies

  angle AOC = angle A'O'C'.
-/
theorem hilbert_theorem_15_case1_finish
    [HilbertCongruence Geo]
    (A O C A' O' C' H H' K' : Geo.Point)
    (hRayAH : HilbertSameRay Geo O A H)
    (hRayA'H' : HilbertSameRay Geo O' A' H')
    (hRayC'K' : HilbertSameRay Geo O' C' K')
    (hAngle :
      Geo.AngleCongruent H O C H' O' K') :
    Geo.AngleCongruent A O C A' O' C' := by

  --------------------------------------------------------------------
  -- Replace OA by OH.
  --------------------------------------------------------------------

  have hLeft :
      Geo.Angle A O C =
      Geo.Angle H O C :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O A H C
      hRayAH

  --------------------------------------------------------------------
  -- Replace O'A' by O'H'.
  --------------------------------------------------------------------

  have hRightFirst :
      Geo.Angle A' O' C' =
      Geo.Angle H' O' C' :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O' A' H' C'
      hRayA'H'

  --------------------------------------------------------------------
  -- Replace O'C' by O'K'.
  --------------------------------------------------------------------

  have hRightSecond :
      Geo.Angle H' O' C' =
      Geo.Angle H' O' K' :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      O' H' C' K'
      hRayC'K'

  have hRight :
      Geo.Angle A' O' C' =
      Geo.Angle H' O' K' :=
    hRightFirst.trans hRightSecond

  --------------------------------------------------------------------
  -- The auxiliary angle is therefore exactly the original angle.
  --------------------------------------------------------------------

  unfold Geometry.Geo.AngleCongruent at hAngle ⊢

  rw [hLeft, hRight]

  exact hAngle

------------------------------------------------------------------------
-- Hilbert Theorem 15, same-side case 1
-- Complete assembly
------------------------------------------------------------------------

/--
Hilbert Theorem 15, first same-side case.

The ray OA meets the segment CB. If the corresponding outer rays
A' and C' lie on the same side of O'B', and the two component angles
are pairwise congruent, then the outer angles AOC and A'O'C' are
congruent.

This theorem only assembles the previously established local
Hilbert-Theorem-15 lemmas.
-/
theorem hilbert_theorem_15_sameSide_case1
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : Not (HilbertIncidence.OnLine A l))
    (hCoff : Not (HilbertIncidence.OnLine C l))
    (hA'off : Not (HilbertIncidence.OnLine A' l'))
    (hC'off : Not (HilbertIncidence.OnLine C' l'))
    (hSame' : HilbertSameSide Geo A' C' l')
    (hRay :
      HilbertRayMeetsSegment Geo O A C B)
    (hAB :
      Geo.AngleCongruent A O B A' O' B')
    (hBC :
      Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent A O C A' O' C' := by

  --------------------------------------------------------------------
  -- Auxiliary construction.
  --------------------------------------------------------------------

  rcases
      hilbert_theorem_15_case1_construct
        Geo
        O A B C
        O' A' B' C'
        l'
        hO'B'
        hO'l'
        hA'off
        hC'off
        hRay with
    ⟨H,
     K',
     L',
     H',
     hCHB,
     hRayAH,
     hRayC'K',
     hRayB'L',
     hRayA'H',
     hOC_O'K',
     hOB_O'L',
     hOH_O'H'⟩

  --------------------------------------------------------------------
  -- Transport the two assumed component angles.
  --------------------------------------------------------------------

  rcases
      hilbert_theorem_15_case1_transport
        Geo
        A O B C
        A' O' B' C'
        H K' L' H'
        hRayAH
        hRayC'K'
        hRayB'L'
        hRayA'H'
        hAB
        hBC with
    ⟨hAngleHOB, hAngleBOC⟩

  --------------------------------------------------------------------
  -- Noncollinearity of the four triangles used in the first
  -- two applications of Theorem 12.
  --------------------------------------------------------------------

  rcases
      hilbert_theorem_15_case1_noncollinear
        Geo
        A O B C
        A' O' B' C'
        H K' L' H'
        l l'
        hOB
        hO'B'
        hOl
        hBl
        hO'l'
        hB'l'
        hAoff
        hCoff
        hA'off
        hC'off
        hRayAH
        hRayC'K'
        hRayB'L'
        hRayA'H' with
    ⟨hOBH, hO'L'H', hOBC, hO'L'K'⟩

  --------------------------------------------------------------------
  -- The first two applications of Hilbert Theorem 12.
  --------------------------------------------------------------------

  rcases
      hilbert_theorem_15_case1_SAS
        Geo
        O B C
        O' H K' L' H'
        hOBH
        hO'L'H'
        hOBC
        hO'L'K'
        hOB_O'L'
        hOH_O'H'
        hOC_O'K'
        hAngleHOB
        hAngleBOC with
    ⟨hBH_L'H',
     hBC_L'K',
     hAngleOBH,
     hAngleOBC,
     hAngleOHB⟩

  --------------------------------------------------------------------
  -- Angle-construction uniqueness puts H' and K' on the same ray
  -- from L'.
  --------------------------------------------------------------------

  have hRayH'K' :
      HilbertSameRay Geo L' H' K' :=
    hilbert_theorem_15_case1_sameRay
      Geo
      O B C
      A' O' B' C'
      H K' L' H'
      l'
      hO'B'
      hO'l'
      hB'l'
      hA'off
      hC'off
      hSame'
      hRayA'H'
      hRayC'K'
      hRayB'L'
      hCHB
      hAngleOBH
      hAngleOBC

  --------------------------------------------------------------------
  -- Determine the order on that ray and obtain HC = H'K'.
  --------------------------------------------------------------------

  rcases
      hilbert_theorem_15_case1_order
        Geo
        B C H
        L' H' K'
        hCHB
        hRayH'K'
        hBH_L'H'
        hBC_L'K' with
    ⟨hL'H'K', hHC_H'K'⟩

  --------------------------------------------------------------------
  -- Adjacent-angle theorem and the final application of Theorem 12.
  --------------------------------------------------------------------

  have hAngleHOC :
      Geo.AngleCongruent H O C H' O' K' :=
    hilbert_theorem_15_case1_finalSAS
      Geo
      O B C H
      O' L' H' K'
      hCHB
      hL'H'K'
      hOBH
      hO'L'H'
      hAngleOHB
      hOH_O'H'
      hHC_H'K'

  --------------------------------------------------------------------
  -- Return from the auxiliary rays to OA, OC, O'A', O'C'.
  --------------------------------------------------------------------

  exact
    hilbert_theorem_15_case1_finish
      Geo
      A O C
      A' O' C'
      H H' K'
      hRayAH
      hRayA'H'
      hRayC'K'
      hAngleHOC



/--
An angle having an interior point is necessarily nondegenerate.

This is implicit in Hilbert's definition: if O,A,B were collinear,
the two boundary lines would coincide, whereas the same-side
conditions require A and B to lie off the opposite boundary line.
-/
theorem hilbert_insideAngle_nondegenerate
    [HilbertOrder Geo]
    (O A B X : Geo.Point)
    (hInside : HilbertInsideAngle Geo O A B X) :
    Not (Collinear Geo O A B) := by

  rcases hInside with
    ⟨lineOA,
     lineOB,
     hOlineOA,
     hAlineOA,
     hOlineOB,
     hBlineOB,
     hXA,
     hXB⟩

  have hOA : O ≠ A := by
    intro hEq
    subst A
    exact hXA.2.1 hOlineOB

  intro hOAB

  rcases hOAB with
    ⟨line, hOline, hAline, hBline⟩

  have hEq :
      line = lineOA :=
    HilbertPlaneIncidence.line_unique
      O A
      hOA
      line lineOA
      hOline hAline
      hOlineOA hAlineOA

  have hBlineOA :
      HilbertIncidence.OnLine B lineOA := by
    rw [← hEq]
    exact hBline

  exact hXB.2.1 hBlineOA

------------------------------------------------------------------------
-- Chapter I, sec. 5
-- A ray through an interior point remains inside the angle
------------------------------------------------------------------------

/--
If X lies in the interior of angle AOB and Y lies on the same ray
from O as X, then Y also lies in the interior of angle AOB.

This is Hilbert's statement that a ray from the vertex lies entirely
inside or entirely outside an angle.
-/
theorem hilbert_insideAngle_sameRay
    [HilbertOrder Geo]
    (O A B X Y : Geo.Point)
    (hInside : HilbertInsideAngle Geo O A B X)
    (hRay : HilbertSameRay Geo O X Y) :
    HilbertInsideAngle Geo O A B Y := by

  rcases hInside with
    ⟨lineOA,
     lineOB,
     hOlineOA,
     hAlineOA,
     hOlineOB,
     hBlineOB,
     hXA,
     hXB⟩

  --------------------------------------------------------------------
  -- The common line of the ray OX.
  --------------------------------------------------------------------

  rcases hRay.2.2.1 with
    ⟨base, hObase, hXbase, hYbase⟩

  --------------------------------------------------------------------
  -- Basic nondegeneracy of the two sides of the angle.
  --------------------------------------------------------------------

  have hOA : O ≠ A := by
    intro hEq
    subst A
    exact hXA.2.1 hOlineOB

  have hOB : O ≠ B := by
    intro hEq
    subst B
    exact hXB.2.1 hOlineOA

  --------------------------------------------------------------------
  -- A cannot lie on the ray line OX.
  --
  -- Otherwise base = OA, forcing X onto OA, contrary to the fact
  -- that X and B are on the same side of OA.
  --------------------------------------------------------------------

  have hAbase :
      Not (HilbertIncidence.OnLine A base) := by

    intro hAon

    have hEq : base = lineOA :=
      HilbertPlaneIncidence.line_unique
        O A hOA
        base lineOA
        hObase hAon
        hOlineOA hAlineOA

    have hXlineOA :
        HilbertIncidence.OnLine X lineOA := by
      rw [← hEq]
      exact hXbase

    exact hXB.1 hXlineOA

  --------------------------------------------------------------------
  -- Likewise B cannot lie on the ray line OX.
  --------------------------------------------------------------------

  have hBbase :
      Not (HilbertIncidence.OnLine B base) := by

    intro hBon

    have hEq : base = lineOB :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        base lineOB
        hObase hBon
        hOlineOB hBlineOB

    have hXlineOB :
        HilbertIncidence.OnLine X lineOB := by
      rw [← hEq]
      exact hXbase

    exact hXA.1 hXlineOB

  --------------------------------------------------------------------
  -- X and Y are on the same side of OB.
  --------------------------------------------------------------------

  have hXY_OB :
      HilbertSameSide Geo X Y lineOB :=
    hilbert_sameRay_points_sameSide
      Geo
      O X
      X Y
      B
      base lineOB
      hObase
      hXbase
      hOlineOB
      hBlineOB
      hBbase
      (hilbert_sameRay_refl
        Geo O X hRay.1)
      hRay

  --------------------------------------------------------------------
  -- X and Y are also on the same side of OA.
  --------------------------------------------------------------------

  have hXY_OA :
      HilbertSameSide Geo X Y lineOA :=
    hilbert_sameRay_points_sameSide
      Geo
      O X
      X Y
      A
      base lineOA
      hObase
      hXbase
      hOlineOA
      hAlineOA
      hAbase
      (hilbert_sameRay_refl
        Geo O X hRay.1)
      hRay

  --------------------------------------------------------------------
  -- Transport the two interior half-plane conditions from X to Y.
  --------------------------------------------------------------------

  have hYX_OB :
      HilbertSameSide Geo Y X lineOB :=
    hilbert_sameSide_symm
      Geo X Y lineOB hXY_OB

  have hYA :
      HilbertSameSide Geo Y A lineOB :=
    hilbert_sameSide_trans
      Geo Y X A lineOB
      hYX_OB hXA

  have hYX_OA :
      HilbertSameSide Geo Y X lineOA :=
    hilbert_sameSide_symm
      Geo X Y lineOA hXY_OA

  have hYB :
      HilbertSameSide Geo Y B lineOA :=
    hilbert_sameSide_trans
      Geo Y X B lineOA
      hYX_OA hXB

  exact
    ⟨lineOA,
     lineOB,
     hOlineOA,
     hAlineOA,
     hOlineOB,
     hBlineOB,
     hYA,
     hYB⟩



------------------------------------------------------------------------
-- Chapter I, sec. 6
-- Plane separation needed for Hilbert Theorem 15
------------------------------------------------------------------------

/--
Two points off a line which are not on the same side of that line
lie on opposite sides of it.

With the present definition of `HilbertSameSide`, this is immediate:
if the open segment PQ did not meet the line, it would itself give
a one-step same-side path.
-/
theorem hilbert_order_oppositeSide_of_not_sameSide
    [HilbertOrder Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (hPoff : Not (HilbertIncidence.OnLine P l))
    (hQoff : Not (HilbertIncidence.OnLine Q l))
    (hNotSame : Not (HilbertSameSide Geo P Q l)) :
    HilbertOppositeSide Geo P Q l := by

  refine
    ⟨hPoff, hQoff, ?_⟩

  by_contra hNoMeet

  apply hNotSame

  exact
    ⟨hPoff,
     hQoff,
     Relation.ReflTransGen.single
       ⟨hPoff, hQoff, hNoMeet⟩⟩

------------------------------------------------------------------------
-- Chapter I, sec. 5
-- Plane separation
------------------------------------------------------------------------

/--
If two points lie on the same side of a line, then their open
connecting segment does not meet that line.

This collapses the connectivity definition of `HilbertSameSide`
to the classical segment characterization.
-/
theorem hilbert_sameSide_segment_avoids_line
    [HilbertOrder Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (hSame : HilbertSameSide Geo P Q l) :
    Not (HilbertSegmentMeetsLine Geo P Q l) := by

  intro hMeet

  have hOpp :
      HilbertOppositeSide Geo P Q l :=
    ⟨hSame.1,
     hSame.2.1,
     hMeet⟩

  exact
    (hilbert_oppositeSide_not_sameSide
      Geo P Q l hOpp)
      hSame

theorem hilbert_theorem_15_sameSide_case1_from_inside
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : Not (HilbertIncidence.OnLine A l))
    (hCoff : Not (HilbertIncidence.OnLine C l))
    (hA'off : Not (HilbertIncidence.OnLine A' l'))
    (hC'off : Not (HilbertIncidence.OnLine C' l'))
    (hSame' : HilbertSameSide Geo A' C' l')
    (hInside : HilbertInsideAngle Geo O C B A)
    (hAB : Geo.AngleCongruent A O B A' O' B')
    (hBC : Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent A O C A' O' C' := by

  have hRay :
      HilbertRayMeetsSegment Geo O A C B :=
    hilbert_insideAngle_ray_meets_segment
      Geo
      O C B A
      hInside

  exact
    hilbert_theorem_15_sameSide_case1
      Geo
      A O B C
      A' O' B' C'
      l l'
      hOB
      hO'B'
      hOl
      hBl
      hO'l'
      hB'l'
      hAoff
      hCoff
      hA'off
      hC'off
      hSame'
      hRay
      hAB
      hBC

------------------------------------------------------------------------
-- Chapter I, sec. 6
-- Hilbert Theorem 15
-- Same-side case, second interior ordering
------------------------------------------------------------------------

/--
Hilbert Theorem 15, same-side case, second ordering.

If C lies in the interior of angle AOB, the crossbar theorem gives
the intersection of ray OC with segment AB.  After exchanging
A with C, this is the first same-side case already proved.
-/
theorem hilbert_theorem_15_sameSide_case2_from_inside
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : Not (HilbertIncidence.OnLine A l))
    (hCoff : Not (HilbertIncidence.OnLine C l))
    (hA'off : Not (HilbertIncidence.OnLine A' l'))
    (hC'off : Not (HilbertIncidence.OnLine C' l'))
    (hSame' : HilbertSameSide Geo A' C' l')
    (hInside : HilbertInsideAngle Geo O A B C)
    (hAB : Geo.AngleCongruent A O B A' O' B')
    (hBC : Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent A O C A' O' C' := by

  have hRay :
      HilbertRayMeetsSegment Geo O C A B :=
    hilbert_insideAngle_ray_meets_segment
      Geo
      O A B C
      hInside

  have hSameRev' :
      HilbertSameSide Geo C' A' l' :=
    hilbert_sameSide_symm
      Geo A' C' l' hSame'

  have hCB :
      Geo.AngleCongruent C O B C' O' B' := by
    exact
      (Geo.angle_congruent_reverse_second
        C O B
        B' O' C').mp
        ((Geo.angle_congruent_reverse_first
          B O C
          B' O' C').mp hBC)

  have hBA :
      Geo.AngleCongruent B O A B' O' A' := by
    exact
      (Geo.angle_congruent_reverse_second
        B O A
        A' O' B').mp
        ((Geo.angle_congruent_reverse_first
          A O B
          A' O' B').mp hAB)

  have hCOA :
      Geo.AngleCongruent C O A C' O' A' :=
    hilbert_theorem_15_sameSide_case1
      Geo
      C O B A
      C' O' B' A'
      l l'
      hOB
      hO'B'
      hOl
      hBl
      hO'l'
      hB'l'
      hCoff
      hAoff
      hC'off
      hA'off
      hSameRev'
      hRay
      hCB
      hBA

  exact
    (Geo.angle_congruent_reverse_second
      A O C
      C' O' A').mp
      ((Geo.angle_congruent_reverse_first
        C O A
        C' O' A').mp hCOA)



------------------------------------------------------------------------
-- Chapter I, sec. 7
-- Circle language
------------------------------------------------------------------------

/--
Hilbert's circle with center O and reference point R.

A point X lies on the circle when OX is congruent to OR.

No continuity axiom is involved in this definition.
-/
def HilbertCircle
    (O R : Geo.Point) : Set Geo.Point :=
  fun X => Geo.Congruent O X O R


/--
The reference point of a Hilbert circle lies on the circle.
-/
theorem hilbert_circle_reference_mem
    [HilbertCongruence Geo]
    (O R : Geo.Point) :
    HilbertCircle Geo O R R := by

  exact
    hilbert_congruent_reflexive
      Geo O R


/--
Any two points on the same Hilbert circle are equidistant
from its center.
-/
theorem hilbert_circle_center_congruent
    [HilbertCongruence Geo]
    (O R A B : Geo.Point)
    (hA : HilbertCircle Geo O R A)
    (hB : HilbertCircle Geo O R B) :
    Geo.Congruent O A O B := by

  unfold HilbertCircle at hA hB

  exact
    hilbert_congruent_transitivity
      Geo
      O A
      O R
      O B
      hA
      (hilbert_congruent_symmetry
        Geo O B O R hB)


/--
Four points are concyclic when there exists a common center
from which all four points are equidistant.

The first point A is used only as the reference radius.
-/
def HilbertConcyclic4
    (A B C D : Geo.Point) : Prop :=
  Exists fun O : Geo.Point =>
    Geo.Congruent O A O B /\
    Geo.Congruent O A O C /\
    Geo.Congruent O A O D

------------------------------------------------------------------------
-- Concyclicity from one circle
------------------------------------------------------------------------

/--
Four points lying on one Hilbert circle are concyclic.
-/
theorem hilbert_concyclic4_of_circle
    [HilbertCongruence Geo]
    (O R A B C D : Geo.Point)
    (hA : HilbertCircle Geo O R A)
    (hB : HilbertCircle Geo O R B)
    (hC : HilbertCircle Geo O R C)
    (hD : HilbertCircle Geo O R D) :
    HilbertConcyclic4 Geo A B C D := by

  refine
    Exists.intro O
      ?_

  constructor

  · exact
      hilbert_circle_center_congruent
        Geo O R A B hA hB

  constructor

  · exact
      hilbert_circle_center_congruent
        Geo O R A C hA hC

  · exact
      hilbert_circle_center_congruent
        Geo O R A D hA hD

/--
A concyclic quadruple is contained in the Hilbert circle
with center O and reference radius OA.
-/
theorem hilbert_concyclic4_circle
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : HilbertConcyclic4 Geo A B C D) :
    Exists fun O : Geo.Point =>
      HilbertCircle Geo O A A /\
      HilbertCircle Geo O A B /\
      HilbertCircle Geo O A C /\
      HilbertCircle Geo O A D := by

  rcases h with
    ⟨O, hAB, hAC, hAD⟩

  refine
    ⟨O, ?_, ?_, ?_, ?_⟩

  · exact
      hilbert_congruent_reflexive
        Geo O A

  · exact
      hilbert_congruent_symmetry
        Geo O A O B hAB

  · exact
      hilbert_congruent_symmetry
        Geo O A O C hAC

  · exact
      hilbert_congruent_symmetry
        Geo O A O D hAD

------------------------------------------------------------------------
-- Radial congruences of a concyclic quadruple
------------------------------------------------------------------------

/--
For four concyclic points there is a center O such that the four
successive radii are pairwise congruent.

This is only a convenient reformulation of HilbertConcyclic4.
-/
theorem hilbert_concyclic4_radial_chain
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : HilbertConcyclic4 Geo A B C D) :
    Exists fun O : Geo.Point =>
      Geo.Congruent O A O B /\
      Geo.Congruent O B O C /\
      Geo.Congruent O C O D /\
      Geo.Congruent O D O A := by

  rcases h with
    ⟨O, hAB, hAC, hAD⟩

  have hBA :
      Geo.Congruent O B O A :=
    hilbert_congruent_symmetry
      Geo O A O B hAB

  have hCA :
      Geo.Congruent O C O A :=
    hilbert_congruent_symmetry
      Geo O A O C hAC

  have hBC :
      Geo.Congruent O B O C :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      O C
      hBA
      hAC

  have hCD :
      Geo.Congruent O C O D :=
    hilbert_congruent_transitivity
      Geo
      O C
      O A
      O D
      hCA
      hAD

  have hDA :
      Geo.Congruent O D O A :=
    hilbert_congruent_symmetry
      Geo O A O D hAD

  exact
    ⟨O, hAB, hBC, hCD, hDA⟩

------------------------------------------------------------------------
-- First circle consequence
------------------------------------------------------------------------

/--
If A and B lie on the same Hilbert circle with center O,
then triangle OAB is isosceles.

In the noncollinear case, its base angles at A and B
are congruent.
-/
theorem hilbert_circle_base_angles
    [HilbertCongruence Geo]
    (O R A B : Geo.Point)
    (hA : HilbertCircle Geo O R A)
    (hB : HilbertCircle Geo O R B)
    (hOAB : Not (Collinear Geo O A B)) :
    Geo.AngleCongruent O A B O B A := by

  have hOAOB :
      Geo.Congruent O A O B :=
    hilbert_circle_center_congruent
      Geo O R A B hA hB

  exact
    hilbert_theorem_11_isosceles_base_angles
      Geo
      O A B
      hOAB
      hOAOB



------------------------------------------------------------------------
-- Circle geometry
-- Symmetry of four-point concyclicity
------------------------------------------------------------------------

/--
Concyclicity of four points is invariant under cyclic permutation.
-/
theorem hilbert_concyclic4_rotate
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : HilbertConcyclic4 Geo A B C D) :
    HilbertConcyclic4 Geo B C D A := by

  rcases h with
    ⟨O, hAB, hAC, hAD⟩

  have hBA :
      Geo.Congruent O B O A :=
    hilbert_congruent_symmetry
      Geo O A O B hAB

  have hBC :
      Geo.Congruent O B O C :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      O C
      hBA
      hAC

  have hBD :
      Geo.Congruent O B O D :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      O D
      hBA
      hAD

  exact
    ⟨O,
     hBC,
     hBD,
     hBA⟩

------------------------------------------------------------------------
-- Circle geometry
-- Reversal of four-point concyclicity
------------------------------------------------------------------------

/--
Concyclicity of four points is invariant under reversal
with the first point fixed.
-/
theorem hilbert_concyclic4_reverse
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : HilbertConcyclic4 Geo A B C D) :
    HilbertConcyclic4 Geo A D C B := by

  rcases h with
    ⟨O, hAB, hAC, hAD⟩

  exact
    ⟨O,
     hAD,
     hAC,
     hAB⟩

end Geometry

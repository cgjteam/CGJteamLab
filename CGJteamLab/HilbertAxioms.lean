import CGJteamLab.HilbertCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert Grundlagen Axioms

A source-faithful Lean transcription of the five axiom groups in
Hilbert's `Grundlagen der Geometrie`.

The source order is preserved:

* Group I: incidence, I.1-I.8;
* Group II: order, II.1-II.4;
* Group III: congruence, III.1-III.5;
* Group IV: Euclid's parallel axiom;
* Group V: continuity, V.1-V.2.

This module is intentionally separate from the existing production
interfaces `HilbertAxioms.lean` and `Hilbert3DAxioms.lean`.  It is the
source layer against which compatibility adapters can be proved.

No Smith, Wyler, Salas, Coxeter, dimension-free, or project-specific
geometric axiom is introduced here.
-/


/-!
# Hilbert Grundlagen: Group I (Incidence)

Primitive objects used here:
* points and lines from `Geometry.Geo`;
* the primitive point-line incidence relation `Geo.OnLine`;
* planes and point-plane incidence introduced below.

No order, congruence, parallel, continuity, dimension-free, Smith, Wyler,
or Salas axiom is assumed in this file.
-/

/--
Primitive plane sort and point-plane incidence for Hilbert's original
three-dimensional incidence language.
-/
class HilbertGrundlagenPrimitive (Geo : Geometry.Geo) where
  Plane : Type u
  OnPlane : Geo.Point -> Plane -> Prop

/--
Three points are collinear if one line contains all three.
This definition uses the primitive incidence relation `Geo.OnLine`.
-/
def HilbertGrundlagenCollinear
    (A B C : Geo.Point) : Prop :=
  exists l : Geo.Line,
    Geo.OnLine A l /\
    Geo.OnLine B l /\
    Geo.OnLine C l

/--
Four points are coplanar if one plane contains all four.
-/
def HilbertGrundlagenCoplanar4
    [S : HilbertGrundlagenPrimitive Geo]
    (A B C D : Geo.Point) : Prop :=
  exists pi : S.Plane,
    S.OnPlane A pi /\
    S.OnPlane B pi /\
    S.OnPlane C pi /\
    S.OnPlane D pi

/--
Hilbert, Grundlagen der Geometrie, Group I: incidence axioms I.1-I.8.

The fields follow the source order. Distinctness assumptions that Hilbert
handles by the convention of using different letters are explicit in Lean.
-/
class HilbertGrundlagenGroupI
    (Geo : Geometry.Geo)
    [S : HilbertGrundlagenPrimitive Geo] : Prop where

  /-- I.1: two distinct points lie on a line. -/
  I1_line_through :
    forall A B : Geo.Point,
      Ne A B ->
      exists l : Geo.Line,
        Geo.OnLine A l /\
        Geo.OnLine B l

  /-- I.2: two distinct points lie on at most one line. -/
  I2_line_unique :
    forall A B : Geo.Point,
      Ne A B ->
      forall l m : Geo.Line,
        Geo.OnLine A l ->
        Geo.OnLine B l ->
        Geo.OnLine A m ->
        Geo.OnLine B m ->
        l = m

  /-- I.3, line clause: every line contains at least two distinct points. -/
  I3_two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        Geo.OnLine A l /\
        Geo.OnLine B l

  /-- I.3, nondegeneracy clause: there exist three noncollinear points. -/
  I3_three_noncollinear :
  exists A B C : Geo.Point,
    Ne A B /\
    Ne A C /\
    Ne B C /\
    Not (HilbertGrundlagenCollinear Geo A B C)

  /-- I.4, first clause: three noncollinear points lie in a plane. -/
  I4_plane_through :
    forall A B C : Geo.Point,
      Not (HilbertGrundlagenCollinear Geo A B C) ->
      exists pi : S.Plane,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi

  /-- I.4, second clause: every plane contains a point. -/
  I4_point_on_each_plane :
    forall pi : S.Plane,
      exists A : Geo.Point,
        S.OnPlane A pi

  /-- I.5: three noncollinear points lie in at most one plane. -/
  I5_plane_unique :
    forall A B C : Geo.Point,
      Not (HilbertGrundlagenCollinear Geo A B C) ->
      forall pi rho : S.Plane,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        S.OnPlane A rho ->
        S.OnPlane B rho ->
        S.OnPlane C rho ->
        pi = rho

  /--
  I.6: if two distinct points of a line lie in a plane, every point of
  that line lies in the plane.
  -/
  I6_line_in_plane :
    forall A B : Geo.Point,
      Ne A B ->
      forall l : Geo.Line,
        Geo.OnLine A l ->
        Geo.OnLine B l ->
        forall pi : S.Plane,
          S.OnPlane A pi ->
          S.OnPlane B pi ->
          forall X : Geo.Point,
            Geo.OnLine X l ->
            S.OnPlane X pi

  /--
  I.7: two distinct planes with a common point have another distinct
  common point.

  Hilbert explicitly notes that this axiom gives dimension at most 3.
  -/
  I7_second_common_point :
    forall pi rho : S.Plane,
      Ne pi rho ->
      forall A : Geo.Point,
        S.OnPlane A pi ->
        S.OnPlane A rho ->
        exists B : Geo.Point,
          Ne B A /\
          S.OnPlane B pi /\
          S.OnPlane B rho

  /--
  I.8: there exist four points which do not lie in one plane.

  Hilbert explicitly notes that this axiom gives dimension at least 3.
  -/
  I8_four_noncoplanar :
    exists A B C D : Geo.Point,
      Not (HilbertGrundlagenCoplanar4 Geo A B C D)

/-!
# Hilbert Grundlagen: Group II (Order)

This file records Hilbert's order axioms II.1-II.4 in the source order.
No theorem of order is added here.

Source: Hilbert, Grundlagen der Geometrie, Chapter I, Section 3.
-/

/--
A line lies in a plane when every point of the line lies in the plane.

This is only terminology for formulating Hilbert II.4.
It is not a new axiom.
-/
def HilbertGrundlagenLineInPlane
    [S : HilbertGrundlagenPrimitive Geo]
    (l : Geo.Line)
    (pi : S.Plane) : Prop :=
  forall X : Geo.Point,
    Geo.OnLine X l ->
    S.OnPlane X pi

/--
Hilbert, Grundlagen der Geometrie, Group II: order axioms II.1-II.4.

The primitive order relation is `Geo.Between A B C`, meaning that B lies
between A and C.
-/
class HilbertGrundlagenGroupII
    (Geo : Geometry.Geo)
    [S : HilbertGrundlagenPrimitive Geo]
    [HilbertGrundlagenGroupI Geo] : Prop where

  /--
  II.1:
  If B lies between A and C, then A, B, C are three distinct collinear
  points, and B also lies between C and A.
  -/
  II1_between :
    forall A B C : Geo.Point,
      Geo.Between A B C ->
      Ne A B /\
      Ne B C /\
      Ne A C /\
      HilbertGrundlagenCollinear Geo A B C /\
      Geo.Between C B A

  /--
  II.2:
  For two distinct points A and C, there exists a point B such that
  C lies between A and B.
  -/
  II2_extension :
    forall A C : Geo.Point,
      Ne A C ->
      exists B : Geo.Point,
        Geo.Between A C B

  /--
  II.3:
  Of three collinear points, at most one lies between the other two.

  The three possible middle points are B, A, and C, represented by
  `Between A B C`, `Between B A C`, and `Between A C B`.
  -/
  II3_at_most_one_between :
    forall A B C : Geo.Point,
      HilbertGrundlagenCollinear Geo A B C ->
      (Geo.Between A B C ->
        Not (Geo.Between B A C) /\
        Not (Geo.Between A C B)) /\
      (Geo.Between B A C ->
        Not (Geo.Between A C B))

  /--
  II.4 (Pasch):
  Let A, B, C be noncollinear points and let l be a line in their plane,
  passing through none of A, B, C. If l meets the open segment AB, then
  l also meets the open segment AC or the open segment BC.
  -/
  II4_pasch :
    forall A B C : Geo.Point,
      Not (HilbertGrundlagenCollinear Geo A B C) ->
      forall pi : S.Plane,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        forall l : Geo.Line,
          HilbertGrundlagenLineInPlane Geo l pi ->
          Not (Geo.OnLine A l) ->
          Not (Geo.OnLine B l) ->
          Not (Geo.OnLine C l) ->
          (exists X : Geo.Point,
            Geo.Between A X B /\
            Geo.OnLine X l) ->
          (exists Y : Geo.Point,
            Geo.Between A Y C /\
            Geo.OnLine Y l) \/
          (exists Z : Geo.Point,
            Geo.Between B Z C /\
            Geo.OnLine Z l)

/-!
# Hilbert Grundlagen: Group III (Congruence)

This file records Hilbert's congruence axioms III.1-III.5 in source order.

Important representation choice:
the angle-congruence relation used below is the primitive
`Geo.UnorientedAngleCongruent`, not the derived `Geo.AngleCongruent`.
The latter is an equivalence closure in the current library and would build
reflexivity, symmetry, and transitivity into the representation, whereas
Hilbert derives the corresponding properties from Group III.

Source: Hilbert, Grundlagen der Geometrie, Chapter I, Section 5.
-/

/--
The open segment AB meets the line l.

This is a definition, not an axiom.
-/
def HilbertGrundlagenSegmentMeetsLine
    (A B : Geo.Point)
    (l : Geo.Line) : Prop :=
  exists X : Geo.Point,
    Geo.Between A X B /\
    Geo.OnLine X l

/--
P and Q lie on the same ray from O.

This is a definition used to represent Hilbert's phrase "on a given side
of a line through O" in the one-dimensional sense used in III.1.
-/
def HilbertGrundlagenSameRay
    (O P Q : Geo.Point) : Prop :=
  Ne P O /\
  Ne Q O /\
  HilbertGrundlagenCollinear Geo O P Q /\
  Not (Geo.Between P O Q)

/--
One elementary in-plane connection between two points avoiding a line.

This is a definition, not an axiom.
-/
def HilbertGrundlagenSameSideStep
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (P Q : Geo.Point) : Prop :=
  S.OnPlane P pi /\
  S.OnPlane Q pi /\
  Not (Geo.OnLine P l) /\
  Not (Geo.OnLine Q l) /\
  Not (HilbertGrundlagenSegmentMeetsLine Geo P Q l)

/--
P and Q lie on the same side of l in the plane pi.

The side is represented by finite connectivity inside the complement of l,
generated by segments avoiding l. This is only a representation of the
plane-side notion already developed by Hilbert from Groups I and II.
It is not an additional axiom.
-/
def HilbertGrundlagenSameSideInPlane
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (P Q : Geo.Point) : Prop :=
  HilbertGrundlagenLineInPlane Geo l pi /\
  S.OnPlane P pi /\
  S.OnPlane Q pi /\
  Not (Geo.OnLine P l) /\
  Not (Geo.OnLine Q l) /\
  Relation.ReflTransGen
    (HilbertGrundlagenSameSideStep Geo pi l) P Q

/--
Primitive congruence of the unoriented angles ABC and DEF.

Unlike `Geo.AngleCongruent`, this definition does not take an equivalence
closure. It therefore does not silently assume reflexivity, symmetry, or
transitivity of angle congruence.
-/
def HilbertGrundlagenAngleCongruent
    (A B C D E F : Geo.Point) : Prop :=
  Geo.UnorientedAngleCongruent
    (Geo.Angle A B C)
    (Geo.Angle D E F)

/--
Hilbert, Grundlagen der Geometrie, Group III:
congruence axioms III.1-III.5.
-/
class HilbertGrundlagenGroupIII
    (Geo : Geometry.Geo)
    [S : HilbertGrundlagenPrimitive Geo]
    [HilbertGrundlagenGroupI Geo]
    [HilbertGrundlagenGroupII Geo] : Prop where

  /--
  III.1:
  A segment AB can be laid off from O on a prescribed ray OR.
  Hilbert states existence here; uniqueness is proved later.
  -/
  III1_segment_construction :
    forall A B O R : Geo.Point,
      Ne O R ->
      exists X : Geo.Point,
        HilbertGrundlagenSameRay Geo O R X /\
        Geo.Congruent O X A B

  /--
  III.2:
  If A'B' and A''B'' are both congruent to AB, then A'B' is
  congruent to A''B''.
  -/
  III2_segment_congruence_common :
    forall A B A' B' A'' B'' : Geo.Point,
      Geo.Congruent A B A' B' ->
      Geo.Congruent A B A'' B'' ->
      Geo.Congruent A' B' A'' B''

  /--
  III.3:
  Additivity of adjacent congruent segments.
  -/
  III3_segment_additivity :
    forall A B C A' B' C' : Geo.Point,
      Geo.Between A B C ->
      Geo.Between A' B' C' ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent B C B' C' ->
      Geo.Congruent A C A' C'

  /--
  III.4, construction and uniqueness clause:
  an angle can be constructed uniquely on a prescribed side of a
  prescribed ray in a prescribed plane.

  A point S selects the side of the target line l in the target plane pi.
  Uniqueness is uniqueness of the resulting ray from B'.
  -/
  III4_angle_construction :
    forall A B C A' B' S0 : Geo.Point,
      Not (HilbertGrundlagenCollinear Geo A B C) ->
      Ne A' B' ->
      forall pi : S.Plane,
        S.OnPlane A' pi ->
        S.OnPlane B' pi ->
        S.OnPlane S0 pi ->
        forall l : Geo.Line,
          Geo.OnLine A' l ->
          Geo.OnLine B' l ->
          HilbertGrundlagenLineInPlane Geo l pi ->
          Not (Geo.OnLine S0 l) ->
          exists C' : Geo.Point,
            HilbertGrundlagenSameSideInPlane Geo pi l C' S0 /\
            HilbertGrundlagenAngleCongruent
              Geo A B C A' B' C' /\
            forall D' : Geo.Point,
              HilbertGrundlagenSameSideInPlane Geo pi l D' S0 ->
              HilbertGrundlagenAngleCongruent
                Geo A B C A' B' D' ->
              HilbertGrundlagenSameRay Geo B' C' D'

  /--
  III.4, reflexivity clause:
  every nondegenerate angle is congruent to itself.
  -/
  III4_angle_reflexive :
    forall A B C : Geo.Point,
      Not (HilbertGrundlagenCollinear Geo A B C) ->
      HilbertGrundlagenAngleCongruent Geo A B C A B C

  /--
  III.5:
  Hilbert's SAS axiom in its original angle-conclusion form.

  If AB = A'B', AC = A'C', and angle BAC = angle B'A'C',
  then angle ABC = angle A'B'C'.
  -/
  III5_sas :
    forall A B C A' B' C' : Geo.Point,
      Not (HilbertGrundlagenCollinear Geo A B C) ->
      Not (HilbertGrundlagenCollinear Geo A' B' C') ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent A C A' C' ->
      HilbertGrundlagenAngleCongruent
        Geo B A C B' A' C' ->
      HilbertGrundlagenAngleCongruent
        Geo A B C A' B' C'

/-!
# Hilbert Grundlagen: Group IV (Parallel Axiom)

This file records Hilbert's single Group IV axiom.
No existence of a parallel is postulated here: Hilbert proves existence
before stating the axiom and postulates only uniqueness.

Source: Hilbert, Grundlagen der Geometrie, Chapter I, Section 7.
-/

/--
Two lines meet when they have a common point.

This is a definition, not an axiom.
-/
def HilbertGrundlagenLinesMeet
    (l m : Geo.Line) : Prop :=
  exists P : Geo.Point,
    Geo.OnLine P l /\
    Geo.OnLine P m

/--
Two lines are disjoint when they have no common point.

This is a definition, not an axiom.
-/
def HilbertGrundlagenLinesDisjoint
    (l m : Geo.Line) : Prop :=
  Not (HilbertGrundlagenLinesMeet Geo l m)

/--
Two lines are parallel in a plane when both lie in that plane
and do not meet.

This follows Hilbert's definition immediately preceding Axiom IV.
-/
def HilbertGrundlagenParallelInPlane
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (l m : Geo.Line) : Prop :=
  HilbertGrundlagenLineInPlane Geo l pi /\
  HilbertGrundlagenLineInPlane Geo m pi /\
  HilbertGrundlagenLinesDisjoint Geo l m

/--
Hilbert, Grundlagen der Geometrie, Group IV: Euclid's parallel axiom.

For a line l and a point A not on l, in the plane containing l and A,
there is at most one line through A that does not meet l.
-/
class HilbertGrundlagenGroupIV
    (Geo : Geometry.Geo)
    [S : HilbertGrundlagenPrimitive Geo]
    [HilbertGrundlagenGroupI Geo]
    [HilbertGrundlagenGroupII Geo]
    [HilbertGrundlagenGroupIII Geo] : Prop where

  /--
  IV:
  Let l be a line and A a point not on it.
  In a plane pi containing l and A, there is at most one line through A
  that does not meet l.
  -/
  IV_parallel_uniqueness :
    forall (pi : S.Plane) (l : Geo.Line) (A : Geo.Point),
      HilbertGrundlagenLineInPlane Geo l pi ->
      S.OnPlane A pi ->
      Not (Geo.OnLine A l) ->
      forall m n : Geo.Line,
        HilbertGrundlagenLineInPlane Geo m pi ->
        HilbertGrundlagenLineInPlane Geo n pi ->
        Geo.OnLine A m ->
        Geo.OnLine A n ->
        HilbertGrundlagenLinesDisjoint Geo l m ->
        HilbertGrundlagenLinesDisjoint Geo l n ->
        m = n

/-!
# Hilbert Grundlagen: Group V.1 (Archimedean Axiom)

This file records Hilbert's Axiom V.1 only.

Axiom V.2 is intentionally not encoded here.  V.2 is a maximality
statement about proper extensions of an ordered congruence structure on a
line, so it needs an explicit notion of extension of structures.  It will be
handled separately rather than replaced by a stronger or weaker ad hoc
continuity axiom.

Source: Hilbert, Grundlagen der Geometrie, Chapter I, Section 8.
-/

/--
A chain of n consecutive copies of segment CD, starting at A and lying
on the ray from A through B.

For P : Fin (n + 1) -> Point:
* P 0 = A;
* each consecutive segment P_i P_(i+1) is congruent to CD;
* every positive chain point lies on the ray AB.

This is a definition used to state V.1, not an additional axiom.
-/
def HilbertGrundlagenSegmentChain
    (A B C D : Geo.Point)
    (n : Nat)
    (P : Fin (n + 1) -> Geo.Point) : Prop :=
  P 0 = A /\
  (forall i : Fin n,
    Geo.Congruent
      (P i.castSucc)
      (P i.succ)
      C D) /\
  (forall i : Fin n,
    HilbertGrundlagenSameRay
      Geo A B (P i.succ))

/--
Hilbert, Grundlagen der Geometrie, Axiom V.1
(the Archimedean axiom).

For any nondegenerate segments AB and CD, finitely many consecutive
copies of CD laid off from A along the ray AB pass beyond B.
-/
class HilbertGrundlagenGroupV1
    (Geo : Geometry.Geo)
    [S : HilbertGrundlagenPrimitive Geo]
    [HilbertGrundlagenGroupI Geo]
    [HilbertGrundlagenGroupII Geo]
    [HilbertGrundlagenGroupIII Geo] : Prop where

  /--
  V.1:
  there is a positive integer n and a chain of n copies of CD from A
  along ray AB whose final point lies beyond B.
  -/
  V1_archimedes :
    forall A B C D : Geo.Point,
      Ne A B ->
      Ne C D ->
      exists n : Nat,
        0 < n /\
        exists P : Fin (n + 1) -> Geo.Point,
          HilbertGrundlagenSegmentChain
            Geo A B C D n P /\
          Geo.Between
            A B (P (Fin.last n))

/-!
# Hilbert Grundlagen: Group V.2 (Line Completeness)

This file records Hilbert's Axiom V.2 as a genuine maximality axiom.

Hilbert does not formulate V.2 as Dedekind completeness, Cauchy
completeness, or existence of suprema.  He says that the points of a line,
together with their order and congruence relations, cannot be properly
extended while preserving the fundamental line properties already obtained
from Groups I-III and V.1.

To express that statement faithfully in Lean, this file introduces an
abstract ordered-congruence structure on a line and a notion of extension.
These are metatheoretic bookkeeping devices, not new geometric axioms.

Source: Hilbert, Grundlagen der Geometrie, Chapter I, Section 8.
-/

/--
The structure carried by one geometric line for the purpose of V.2.

Only the data mentioned by Hilbert in V.2 are retained:
points, betweenness, and segment congruence.
-/
structure HilbertGrundlagenLineStructure where
  Point : Type u
  Between : Point -> Point -> Point -> Prop
  Congruent : Point -> Point -> Point -> Point -> Prop

namespace HilbertGrundlagenLineStructure

/--
P and Q lie on the same ray from O in an abstract line structure.
-/
def SameRay
    (L : HilbertGrundlagenLineStructure)
    (O P Q : L.Point) : Prop :=
  Ne P O /\
  Ne Q O /\
  Not (L.Between P O Q)

/--
A chain of n consecutive copies of CD beginning at A and proceeding
along the ray from A through B.
-/
def SegmentChain
    (L : HilbertGrundlagenLineStructure)
    (A B C D : L.Point)
    (n : Nat)
    (P : Fin (n + 1) -> L.Point) : Prop :=
  P 0 = A /\
  (forall i : Fin n,
    L.Congruent
      (P i.castSucc)
      (P i.succ)
      C D) /\
  (forall i : Fin n,
    L.SameRay A B (P i.succ))

end HilbertGrundlagenLineStructure

/--
The line properties whose preservation Hilbert explicitly requires in V.2.

They are:
* order properties II.1-II.3;
* Theorem 5 on the ordering of four points;
* segment-congruence properties III.1-III.3;
* uniqueness of segment construction;
* the Archimedean property V.1.

This class does not add these properties to ambient geometry.  It packages
the exact conditions that a candidate extension must continue to satisfy.
-/
class HilbertGrundlagenLineFundamentals
    (L : HilbertGrundlagenLineStructure) : Prop where

  II1 :
    forall A B C : L.Point,
      L.Between A B C ->
      Ne A B /\
      Ne B C /\
      Ne A C /\
      L.Between C B A

  II2 :
    forall A C : L.Point,
      Ne A C ->
      exists B : L.Point,
        L.Between A C B

  II3 :
    forall A B C : L.Point,
      L.Between A B C ->
      Not (L.Between B A C) /\
      Not (L.Between A C B)

  /--
  Theorem 5:
  any four distinct points can be relabeled A,B,C,D so that

      A - B - C - D

  in Hilbert's precise betweenness sense.
  -/
  theorem5 :
    forall x : Fin 4 -> L.Point,
      Function.Injective x ->
      exists p : Equiv.Perm (Fin 4),
        L.Between (x (p 0)) (x (p 1)) (x (p 2)) /\
        L.Between (x (p 0)) (x (p 1)) (x (p 3)) /\
        L.Between (x (p 0)) (x (p 2)) (x (p 3)) /\
        L.Between (x (p 1)) (x (p 2)) (x (p 3))

  III1 :
    forall A B O R : L.Point,
      Ne O R ->
      exists X : L.Point,
        L.SameRay O R X /\
        L.Congruent O X A B

  III2 :
    forall A B A' B' A'' B'' : L.Point,
      L.Congruent A B A' B' ->
      L.Congruent A B A'' B'' ->
      L.Congruent A' B' A'' B''

  III3 :
    forall A B C A' B' C' : L.Point,
      L.Between A B C ->
      L.Between A' B' C' ->
      L.Congruent A B A' B' ->
      L.Congruent B C B' C' ->
      L.Congruent A C A' C'

  segment_construction_unique :
    forall A B O R X Y : L.Point,
      Ne O R ->
      L.SameRay O R X ->
      L.SameRay O R Y ->
      L.Congruent O X A B ->
      L.Congruent O Y A B ->
      X = Y

  V1 :
    forall A B C D : L.Point,
      Ne A B ->
      Ne C D ->
      exists n : Nat,
        0 < n /\
        exists P : Fin (n + 1) -> L.Point,
          L.SegmentChain A B C D n P /\
          L.Between A B (P (Fin.last n))

/--
The ordered-congruence structure induced on one ambient geometric line.
-/
def HilbertGrundlagenLineOf
    (Geo : Geometry.Geo)
    (l : Geo.Line) :
    HilbertGrundlagenLineStructure where
  Point := {P : Geo.Point // Geo.OnLine P l}
  Between := fun A B C =>
    Geo.Between A.1 B.1 C.1
  Congruent := fun A B C D =>
    Geo.Congruent A.1 B.1 C.1 D.1

/--
An admissible extension in the sense of Hilbert V.2.

The old line is embedded injectively into a possibly larger line structure.
Betweenness and segment congruence on old points are preserved and
reflected, and the extended structure satisfies the fundamental line
properties listed by Hilbert in the formulation of V.2.
-/
structure HilbertGrundlagenLineExtension
    (L : HilbertGrundlagenLineStructure)
    (M : HilbertGrundlagenLineStructure) where

  toFun : L.Point -> M.Point

  injective :
    Function.Injective toFun

  between_iff :
    forall A B C : L.Point,
      M.Between (toFun A) (toFun B) (toFun C) <->
      L.Between A B C

  congruent_iff :
    forall A B C D : L.Point,
      M.Congruent
        (toFun A) (toFun B)
        (toFun C) (toFun D) <->
      L.Congruent A B C D

  target_fundamentals :
    HilbertGrundlagenLineFundamentals M

/--
Hilbert, Grundlagen der Geometrie, Axiom V.2 (line completeness).

No ambient line admits a proper admissible extension of its ordered
congruence structure.  Equivalently, every admissible extension embedding
is surjective.
-/
class HilbertGrundlagenGroupV2
    (Geo : Geometry.Geo)
    [S : HilbertGrundlagenPrimitive Geo]
    [HilbertGrundlagenGroupI Geo]
    [HilbertGrundlagenGroupII Geo]
    [HilbertGrundlagenGroupIII Geo]
    [HilbertGrundlagenGroupV1 Geo] : Prop where

  V2_line_completeness :
    forall (l : Geo.Line)
      (M : HilbertGrundlagenLineStructure.{u})
      (E :
        HilbertGrundlagenLineExtension
          (HilbertGrundlagenLineOf Geo l)
          M),
      Function.Surjective E.toFun

end Geometry

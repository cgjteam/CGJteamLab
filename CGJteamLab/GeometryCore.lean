import Mathlib.Data.Sym.Sym2

namespace Geometry

universe u

structure Geo where
  Point : Type u
  Line  : Type u

  OnLine :
    Point → Line → Prop

  Between :
    Point → Point → Point → Prop

  SegmentCongruent :
    Sym2 Point →
    Sym2 Point →
    Prop

  UnorientedAngleCongruent :
    (Point × Sym2 (Set Point)) →
    (Point × Sym2 (Set Point)) →
    Prop

  ParallelConfiguration :
    Sym2 (Set Point) →
    Prop

namespace Geo

/-- A ray is represented extensionally by its set of points. -/
abbrev Ray
    (Geo : Geometry.Geo) :=
  Set Geo.Point

/--
One elementary step between two non-origin points lying in the same
direction from `O`.
-/
def SameDirectionStep
    (Geo : Geometry.Geo)
    (O P Q : Geo.Point) : Prop :=
  P ≠ O ∧
  Q ≠ O ∧
  (P = Q ∨
    Geo.Between O P Q ∨
    Geo.Between O Q P)

/--
The ray with origin `O` passing through `A`.

Apart from the origin, it is the connected component of `A` generated
by elementary same-direction steps. This makes the ray independent of
which of its non-origin points is used to determine it, without adding
any order axiom to the shared core.
-/
def ray
    (Geo : Geometry.Geo)
    (O A : Geo.Point) :
    Geo.Ray :=
  {X |
    X = O ∨
    Relation.ReflTransGen (Geo.SameDirectionStep O) A X}

theorem sameDirectionStep_symm
    (Geo : Geometry.Geo)
    (O P Q : Geo.Point) :
    Geo.SameDirectionStep O P Q →
    Geo.SameDirectionStep O Q P := by
  rintro ⟨hPO, hQO, hPQ | hOPQ | hOQP⟩
  · exact ⟨hQO, hPO, Or.inl hPQ.symm⟩
  · exact ⟨hQO, hPO, Or.inr (Or.inr hOPQ)⟩
  · exact ⟨hQO, hPO, Or.inr (Or.inl hOQP)⟩

theorem ray_eq_of_sameDirectionStep
    (Geo : Geometry.Geo)
    (O A B : Geo.Point)
    (hAB : Geo.SameDirectionStep O A B) :
    Geo.ray O A = Geo.ray O B := by
  apply Set.ext
  intro X
  constructor
  · rintro (hXO | hAX)
    · exact Or.inl hXO
    · exact
        Or.inr
          ((Relation.ReflTransGen.single
            (Geo.sameDirectionStep_symm O A B hAB)).trans hAX)
  · rintro (hXO | hBX)
    · exact Or.inl hXO
    · exact
        Or.inr
          ((Relation.ReflTransGen.single hAB).trans hBX)

/-- The unoriented segment with endpoints `A` and `B`. -/
def Segment
    (Geo : Geometry.Geo)
    (A B : Geo.Point) :
    Sym2 Geo.Point :=
  s(A, B)

/--
Congruence of the unoriented segments `AB` and `CD`.

The four-point interface is retained for compatibility with the rest of
the geometry library.
-/
def Congruent
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) : Prop :=
  Geo.SegmentCongruent (Geo.Segment A B) (Geo.Segment C D)

/--
The unoriented angle `ABC`, represented by its vertex `B` and the
unordered pair of rays `BA` and `BC`.
-/
def Angle
    (Geo : Geometry.Geo)
    (A B C : Geo.Point) :
    Geo.Point × Sym2 Geo.Ray :=
  (B, s(Geo.ray B A, Geo.ray B C))

/--
The rays `OA` and `OC` are opposite when their determining points are
distinct from the common origin and the origin lies between them.
-/
def OppositeRays
    (Geo : Geometry.Geo)
    (O A C : Geo.Point) : Prop :=
  A ≠ O ∧
  C ≠ O ∧
  Geo.Between A O C

/--
The angles `AOB` and `BOC` form an adjacent linear pair: they share
the nondegenerate ray `OB`, while their remaining sides `OA` and `OC`
are opposite rays.
-/
def AdjacentAngles
    (Geo : Geometry.Geo)
    (A O B C : Geo.Point) : Prop :=
  B ≠ O ∧
  Geo.OppositeRays O A C

/--
Congruence of the unoriented angles `ABC` and `DEF`.

The six-point interface is retained for compatibility with the rest of
the geometry library.
-/
def AngleCongruent
    (Geo : Geometry.Geo)
    (A B C D E F : Geo.Point) : Prop :=
  Geo.UnorientedAngleCongruent
    (Geo.Angle A B C)
    (Geo.Angle D E F)

/--
Three points are weakly collinear in the language shared by all
geometries when two coincide or one of the six oriented betweenness
relations holds.

All orientations are included because `GeometryCore` deliberately
assumes no order axioms.
-/
def LineCollinear
    (Geo : Geometry.Geo)
    (A B C : Geo.Point) : Prop :=
  A = B ∨
  A = C ∨
  B = C ∨
  Geo.Between A B C ∨
  Geo.Between A C B ∨
  Geo.Between B A C ∨
  Geo.Between B C A ∨
  Geo.Between C A B ∨
  Geo.Between C B A

/--
The extensional point-line determined by `A` and `B`.

For distinct endpoints, Hilbert's order theorems identify this set
with the unique incidence line through `A` and `B`. Degenerate pairs
are excluded by `Parallel`.
-/
def PointLine
    (Geo : Geometry.Geo)
    (A B : Geo.Point) :
    Set Geo.Point :=
  {X | Geo.LineCollinear A B X}

/--
Parallelism of two unoriented point-lines, represented as an unordered
pair so that exchanging the two lines is definitional.

The four-point interface is retained for compatibility with the rest of
the geometry library.
-/
def Parallel
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) : Prop :=
  A ≠ B ∧
  C ≠ D ∧
  Geo.ParallelConfiguration
    s(Geo.PointLine A B, Geo.PointLine C D)

theorem segment_swap
    (Geo : Geometry.Geo)
    (A B : Geo.Point) :
    Geo.Segment A B = Geo.Segment B A := by
  exact Sym2.eq_swap

theorem congruent_reverse_first
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D ↔
    Geo.Congruent B A C D := by
  unfold Congruent Segment
  constructor
  · intro h
    exact (Sym2.eq_swap (a := A) (b := B)) ▸ h
  · intro h
    exact (Sym2.eq_swap (a := B) (b := A)) ▸ h

theorem congruent_reverse_second
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D ↔
    Geo.Congruent A B D C := by
  unfold Congruent Segment
  constructor
  · intro h
    exact (Sym2.eq_swap (a := C) (b := D)) ▸ h
  · intro h
    exact (Sym2.eq_swap (a := D) (b := C)) ▸ h

theorem angle_swap
    (Geo : Geometry.Geo)
    (A B C : Geo.Point) :
    Geo.Angle A B C = Geo.Angle C B A := by
  unfold Angle
  rw [Sym2.eq_swap]

theorem angle_congruent_reverse_first
    (Geo : Geometry.Geo)
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F ↔
    Geo.AngleCongruent C B A D E F := by
  unfold AngleCongruent
  constructor
  · intro h
    exact (Geo.angle_swap A B C) ▸ h
  · intro h
    exact (Geo.angle_swap C B A) ▸ h

theorem angle_congruent_reverse_second
    (Geo : Geometry.Geo)
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F ↔
    Geo.AngleCongruent A B C F E D := by
  unfold AngleCongruent
  constructor
  · intro h
    exact (Geo.angle_swap D E F) ▸ h
  · intro h
    exact (Geo.angle_swap F E D) ▸ h

theorem pointLine_swap
    (Geo : Geometry.Geo)
    (A B : Geo.Point) :
    Geo.PointLine A B = Geo.PointLine B A := by
  apply Set.ext
  intro X
  simp only [PointLine, Set.mem_ofPred_eq, LineCollinear]
  aesop

theorem parallel_symmetry
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D ↔
    Geo.Parallel C D A B := by
  unfold Parallel
  constructor
  · rintro ⟨hAB, hCD, h⟩
    refine ⟨hCD, hAB, ?_⟩
    exact (Sym2.eq_swap
      (a := Geo.PointLine A B)
      (b := Geo.PointLine C D)) ▸ h
  · rintro ⟨hCD, hAB, h⟩
    refine ⟨hAB, hCD, ?_⟩
    exact (Sym2.eq_swap
      (a := Geo.PointLine C D)
      (b := Geo.PointLine A B)) ▸ h

theorem parallel_swap_first
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D ↔
    Geo.Parallel B A C D := by
  unfold Parallel
  constructor
  · rintro ⟨hAB, hCD, h⟩
    refine ⟨hAB.symm, hCD, ?_⟩
    exact congrArg
      (fun l =>
        Geo.ParallelConfiguration
          s(l, Geo.PointLine C D))
      (Geo.pointLine_swap A B) ▸ h
  · rintro ⟨hBA, hCD, h⟩
    refine ⟨hBA.symm, hCD, ?_⟩
    exact congrArg
      (fun l =>
        Geo.ParallelConfiguration
          s(l, Geo.PointLine C D))
      (Geo.pointLine_swap B A) ▸ h

theorem parallel_swap_second
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D ↔
    Geo.Parallel A B D C := by
  unfold Parallel
  constructor
  · rintro ⟨hAB, hCD, h⟩
    refine ⟨hAB, hCD.symm, ?_⟩
    exact congrArg
      (fun l =>
        Geo.ParallelConfiguration
          s(Geo.PointLine A B, l))
      (Geo.pointLine_swap C D) ▸ h
  · rintro ⟨hAB, hDC, h⟩
    refine ⟨hAB, hDC.symm, ?_⟩
    exact congrArg
      (fun l =>
        Geo.ParallelConfiguration
          s(Geo.PointLine A B, l))
      (Geo.pointLine_swap D C) ▸ h

end Geo

end Geometry

namespace Geometry

universe u

structure Geo where
  Point : Type u

  Collinear :
    Point → Point → Point → Prop

  Parallel :
    Point → Point →
    Point → Point →
    Prop

  Congruent :
    Point → Point →
    Point → Point →
    Prop

  AngleCongruent :
    Point → Point → Point →
    Point → Point → Point →
    Prop

variable (Geo : Geo)

------------------------------------------------------------------------
-- Basic definitions
------------------------------------------------------------------------

def IsMidpoint
    (M A B : Geo.Point) : Prop :=
  Geo.Collinear A M B ∧
  Geo.Congruent A M M B

def IsIntersection
    (A B C D P : Geo.Point) : Prop :=
  Geo.Collinear A P B ∧
  Geo.Collinear C P D

def IsMedian
    (_ M B C : Geo.Point) : Prop :=
  IsMidpoint Geo M B C

def OppositeSidesParallel
    (A B C D : Geo.Point) : Prop :=
  Geo.Parallel A B C D ∧
  Geo.Parallel B C D A

def OppositeSidesCongruent
    (A B C D : Geo.Point) : Prop :=
  Geo.Congruent A B C D ∧
  Geo.Congruent B C D A

def IsParallelogram
    (A B C D : Geo.Point) : Prop :=
  OppositeSidesParallel Geo A B C D

------------------------------------------------------------------------
-- Basic theorems
------------------------------------------------------------------------

theorem midpoint_collinear
    (A B M : Geo.Point) :
    IsMidpoint Geo M A B →
    Geo.Collinear A M B := by
  intro h
  exact h.left

theorem MidpointMedian
    (A B C M : Geo.Point) :
    IsMidpoint Geo M B C →
    IsMedian Geo A M B C := by
  intro h
  exact h


------------------------------------------------------------------------
-- Collinearity
------------------------------------------------------------------------

axiom CollinearSymmetry
    (A B C : Geo.Point) :
    Geo.Collinear A B C →
    Geo.Collinear C B A

axiom CollinearRotate
    (A B C : Geo.Point) :
    Geo.Collinear A B C →
    Geo.Collinear A C B

axiom CollinearTrans
    (A G P D : Geo.Point) :
    Geo.Collinear A G P →
    Geo.Collinear P D G →
    Geo.Collinear A G D

------------------------------------------------------------------------
-- Congruence
------------------------------------------------------------------------

axiom CongruentSymmetry
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent C D A B

axiom CongruentReverseFirst
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A C D

axiom CongruentReverseBoth
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A D C

axiom CongruentSwapSecond
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent A B D C

------------------------------------------------------------------------
-- Angle congruence
------------------------------------------------------------------------

axiom AngleCongruentReverse
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F →
    Geo.AngleCongruent C B A F E D

axiom VerticalAngles
    (C E D B F : Geo.Point) :
    Geo.Collinear C E B →
    Geo.Collinear D E F →
    Geo.AngleCongruent C E D B E F

------------------------------------------------------------------------
-- Parallelism
------------------------------------------------------------------------

axiom ParallelSymmetry
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel C D A B

axiom ParallelSwapFirstLine
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel B A C D

axiom ParallelSwapSecondLine
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel A B D C

axiom ParallelCollinearLeft
    (A B C D E : Geo.Point) :
    Geo.Parallel A B D E →
    Geo.Collinear C A B →
    Geo.Parallel C B D E

axiom collinear_parallel_trans
    (A B C D E : Geo.Point) :
    Geo.Collinear A B C →
    Geo.Parallel A C D E →
    Geo.Parallel A B D E

axiom parallel_from_equal_angles
    (A C D B E F : Geo.Point) :
    Geo.Collinear A C D →
    Geo.AngleCongruent E C D E B F →
    Geo.Parallel A D B F

------------------------------------------------------------------------
-- Triangle congruence (SAS)
------------------------------------------------------------------------

structure TriangleCongruenceResult
    (A B C D E F : Geo.Point) where
  sideAB : Geo.Congruent A B D E
  sideBC : Geo.Congruent B C E F
  sideAC : Geo.Congruent A C D F
  angleA : Geo.AngleCongruent B A C E D F
  angleB : Geo.AngleCongruent A B C D E F
  angleC : Geo.AngleCongruent A C B D F E

axiom SAS
    (A B C D E F : Geo.Point) :
    Geo.Congruent A B D E →
    Geo.AngleCongruent B A C E D F →
    Geo.Congruent A C D F →
    TriangleCongruenceResult Geo A B C D E F

axiom TriangleCongruentFromSAS
    (A B C D E F : Geo.Point) :
    Geo.Congruent A B D E →
    Geo.AngleCongruent B A C E D F →
    Geo.Congruent A C D F →
    TriangleCongruenceResult Geo A B C D E F

------------------------------------------------------------------------
-- One parallel side + congruent side
------------------------------------------------------------------------

structure OnePairParallelCongruent
    (A B C D : Geo.Point) where
  parallel : Geo.Parallel A D B C
  congruent : Geo.Congruent A D B C

axiom OnePairParallelCongruentCriterion
    (A B C D : Geo.Point) :
    OnePairParallelCongruent Geo A B C D →
    IsParallelogram Geo A B C D

------------------------------------------------------------------------
-- Parallelograms
------------------------------------------------------------------------

axiom ParallelogramOppositeSidesParallel
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesParallel Geo A B C D

axiom ParallelogramOppositeSidesCongruent
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesCongruent Geo A B C D

axiom ParallelogramDiagonals
    (A B C D M : Geo.Point) :
    IsParallelogram Geo A B C D →
    Geo.Collinear A M C →
    Geo.Collinear B M D →
    IsMidpoint Geo M A C

------------------------------------------------------------------------
-- Auxiliary axioms
------------------------------------------------------------------------

/-
axiom MidsegmentTheorem
    (A B C M N : Geo.Point) :
    IsMidpoint Geo M A B →
    IsMidpoint Geo N A C →
    Geo.Parallel M N B C
-/

axiom ExtendSegment
    (A B : Geo.Point) :
    ∃ T : Geo.Point,
      Geo.Collinear A B T ∧
      Geo.Congruent A B B T

axiom IntersectionOnSameLine
    (A G P B C D : Geo.Point) :
    Geo.Collinear A G P →
    IsIntersection Geo A P B C D →
    IsIntersection Geo P G B C D

axiom congruent_transitivity
    (A D C B F : Geo.Point) :
    Geo.Congruent A D D C →
    Geo.Congruent C D B F →
    Geo.Congruent A D B F

end Geometry

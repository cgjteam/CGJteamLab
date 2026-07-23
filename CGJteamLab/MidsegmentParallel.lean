import CGJteamLab.GeometryBase

namespace Geometry

universe u

variable (Geo : Geo)

variable [HilbertIncidence Geo]
variable [HilbertEuclideanPlane Geo]

theorem MidsegmentParallel
    (V₁ V₂ V₃ M₁ M₂ : Geo.Point)
    (hM₁ : HilbertIsMidpoint Geo M₁ V₁ V₃)
    (hM₂ : HilbertIsMidpoint Geo M₂ V₂ V₃)
    (hTri : ¬ Collinear Geo M₂ M₁ V₃) :
    Geo.Parallel M₁ M₂ V₁ V₂ := by

  ------------------------------------------------------------------------
  -- Step 1. Auxiliary Construction
  ------------------------------------------------------------------------

  have hM₂M₁ : M₂ ≠ M₁ :=
    hilbert_noncollinear_ne_first Geo M₂ M₁ V₃ hTri
  rcases ExtendSegmentBeyond Geo M₁ M₂ hM₂M₁.symm with
    ⟨T, hM₁M₂TBetween, hSeg⟩
  have hM₁M₂TData :=
    HilbertOrder.between_incidence M₁ M₂ T hM₁M₂TBetween
  have hM₁M₂T : Collinear Geo M₁ M₂ T :=
    hM₁M₂TData.2.2.2.1
  have hM₂T : M₂ ≠ T := hM₁M₂TData.2.1

  have hM₁Geometry : IsMidpoint Geo M₁ V₁ V₃ :=
    midpoint_of_hilbert Geo M₁ V₁ V₃ hM₁
  have hM₂Geometry : IsMidpoint Geo M₂ V₂ V₃ :=
    midpoint_of_hilbert Geo M₂ V₂ V₃ hM₂
  have hV₁M₁V₃ := hM₁Geometry.left
  have hV₃M₂V₂Between : Geo.Between V₃ M₂ V₂ :=
    (HilbertOrder.between_incidence
      V₂ M₂ V₃ hM₂.left).2.2.2.2
  have hV₃M₂V₂ :=
    CollinearSymmetry Geo V₂ M₂ V₃ hM₂Geometry.left
  have hM₂V₂ : M₂ ≠ V₂ :=
    (HilbertOrder.between_incidence
      V₂ M₂ V₃ hM₂.left).1.symm
  have hTri₂ : ¬ Collinear Geo M₂ T V₂ := by
    intro hM₂TV₂
    have hM₁M₂V₂ : Collinear Geo M₁ M₂ V₂ :=
      hilbert_primCollinear_trans
        Geo M₁ M₂ T V₂ hM₂T hM₁M₂T hM₂TV₂
    have hM₂V₂V₃ : Collinear Geo M₂ V₂ V₃ :=
      PrimCollinearCycle Geo V₃ M₂ V₂ hV₃M₂V₂
    have hM₁M₂V₃ : Collinear Geo M₁ M₂ V₃ :=
      hilbert_primCollinear_trans
        Geo M₁ M₂ V₂ V₃ hM₂V₂ hM₁M₂V₂ hM₂V₂V₃
    exact hTri (PrimCollinearSwap Geo M₁ M₂ V₃ hM₁M₂V₃)

  ------------------------------------------------------------------------
  -- Step 2. Triangle Congruence (SAS)
  ------------------------------------------------------------------------

  have hVert :=
    VerticalAngles
      Geo V₃ M₂ M₁ V₂ T
      hV₃M₂V₂Between hM₁M₂TBetween
      (fun h =>
        hTri (PrimCollinearCycle Geo V₃ M₂ M₁ h))
  have hVert' := AngleCongruentReverse Geo V₃ M₂ M₁ V₂ M₂ T hVert
  have hSideM₁M₂M₂T := CongruentReverseFirst Geo M₁ M₂ M₂ T hSeg
  have hSideV₂M₂M₂V₃ :=
    CongruentReverseBoth Geo V₂ M₂ M₂ V₃ hM₂Geometry.right
  have hSideV₃M₂M₂V₂ :=
    CongruentReverseFirst Geo V₃ M₂ M₂ V₂
      (CongruentSymmetry Geo M₂ V₂ V₃ M₂ hSideV₂M₂M₂V₃)
  have hCong :=
    TriangleCongruentFromSAS Geo M₂ M₁ V₃ M₂ T V₂
      hTri
      hTri₂
      hSideM₁M₂M₂T
      hVert'
      hSideV₃M₂M₂V₂

  ------------------------------------------------------------------------
  -- Step 3. Deriving Parallelism
  ------------------------------------------------------------------------

  have hParV₁M₁V₂T :=
    parallel_from_equal_angles Geo V₁ V₃ M₁ V₂ M₂ T
      hM₁.left
      hV₃M₂V₂Between
      hM₁M₂TBetween
      (fun h =>
        hTri (PrimCollinearCycle Geo V₃ M₂ M₁ h))
      hCong.angleC

  ------------------------------------------------------------------------
  -- Step 4. Parallelogram Recognition
  ------------------------------------------------------------------------

  have hSideM₁V₃TV₂ := hCong.sideBC
  have hSideV₃M₁V₂T :=
  CongruentReverseFirstSwapSecond
    Geo
    M₁ V₃ T V₂
    hCong.sideBC
  have hSideV₁M₁V₂T :=
    congruent_transitivity Geo V₁ M₁ V₃ V₂ T
      hM₁Geometry.right
      hSideV₃M₁V₂T
  have hOnePair : OnePairParallelCongruent Geo V₁ V₂ T M₁ :=
    onePairParallelCongruent_of_crossing
      Geo V₁ V₂ T M₁ V₃ M₂
      hM₁.left
      hV₃M₂V₂Between
      hM₁M₂TBetween
      hTri
      hParV₁M₁V₂T
      hSideV₁M₁V₂T
  have hParallelogram :=
    OnePairParallelCongruentCriterion
      Geo V₁ V₂ T M₁ hOnePair

  ------------------------------------------------------------------------
  -- Step 5. Applying a Parallelogram Property
  ------------------------------------------------------------------------

  have hParM₁TV₁V₂ :=
    ParallelogramAdjacentParallel
      Geo V₁ V₂ T M₁ hParallelogram

  ------------------------------------------------------------------------
  -- Step 6. Transfer Along a Collinear Line
  ------------------------------------------------------------------------

  exact
    collinear_parallel_trans
      Geo M₁ M₂ T V₁ V₂
      hM₂M₁.symm
      hM₁M₂T
      hParM₁TV₁V₂

theorem MidpointSymmetry
    (M A B : Geo.Point)
    (h : HilbertIsMidpoint Geo M A B) :
    HilbertIsMidpoint Geo M B A := by
  rcases h with ⟨hCol, hCong⟩
  constructor
  · exact (HilbertOrder.between_incidence A M B hCol).2.2.2.2
  ·
    have h1 : Geo.Congruent M A B M :=
      CongruentReverseBoth Geo A M M B hCong
    exact CongruentSymmetry Geo M A B M h1

theorem MidsegmentTheorem
    (A B C M N : Geo.Point)
    (hM : HilbertIsMidpoint Geo M A B)
    (hN : HilbertIsMidpoint Geo N A C)
    (hTri : ¬ Collinear Geo N M A) :
    Geo.Parallel M N B C := by

  have hMBA : HilbertIsMidpoint Geo M B A :=
    MidpointSymmetry Geo M A B hM

  have hNCA : HilbertIsMidpoint Geo N C A :=
    MidpointSymmetry Geo N A C hN

  exact MidsegmentParallel Geo B C A M N hMBA hNCA hTri

end Geometry

/-!
----------------------------------------------------------------------------
Dependency graph of the Midsegment Theorem
----------------------------------------------------------------------------

Step 1. Auxiliary construction

    ExtendSegment

                    |
                    v

Step 2. Triangle congruence

    VerticalAngles
            |
    TriangleCongruentFromSAS

                    |
                    v

Step 3. Deriving parallelism

    parallel_from_equal_angles

                    |
                    v

Step 4. Parallelogram recognition

    OnePairParallelCongruentCriterion

                    |
                    v

Step 5. Parallelogram property

    ParallelogramAdjacentParallel

                    |
                    v

Step 6. Transfer along a collinear line

    collinear_parallel_trans

                    |
                    v

    MidsegmentParallel

----------------------------------------------------------------------------
This proof is organized as a dependency path through GeometryBase.

Each step corresponds to a reusable geometric result rather than to a
proof-specific argument. The resulting sequence exposes the mathematical
dependency graph underlying the Midsegment Theorem.
----------------------------------------------------------------------------
-/

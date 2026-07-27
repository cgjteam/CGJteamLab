import CGJteamLab.TarskiInterface

/-!
# Midsegment parallelism via Tarski

This is the Tarski-based route to the midsegment theorem.
`TarskiBase.lean` connects midpoint and collinearity expressed in
Tarski's primitive language with the shared language of
`GeometryBase.lean`.
-/

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Geo)
variable [TarskiNeutral Geo]
variable [HilbertIncidence Geo]
variable [HilbertEuclideanPlane Geo]
variable [TarskiGeometryBaseBridge Geo]

omit [TarskiNeutral Geo] [TarskiGeometryBaseBridge Geo] in
private theorem midpointSymmetry
    (M A B : Geo.Point)
    (h : IsMidpoint Geo M A B) :
    IsMidpoint Geo M B A := by
  rcases h with ⟨hCol, hCong⟩
  constructor
  · exact CollinearSymmetry Geo A M B hCol
  ·
    have h₁ : Geo.Congruent M A B M :=
      CongruentReverseBoth Geo A M M B hCong
    exact CongruentSymmetry Geo M A B M h₁


private theorem midsegmentParallelFromGeometryMidpoints
    (V₁ V₂ V₃ M₁ M₂ : Geo.Point)
    (hM₁ : IsMidpoint Geo M₁ V₁ V₃)
    (hM₂ : IsMidpoint Geo M₂ V₂ V₃)
    (hM₁Between : Geo.Between V₁ M₁ V₃)
    (hM₂Between : Geo.Between V₃ M₂ V₂)
    (hM₂V₂ : M₂ ≠ V₂)
    (hTri : ¬ Collinear Geo M₂ M₁ V₃) :
    Geo.Parallel M₁ M₂ V₁ V₂ := by

  have hM₂M₁ : M₂ ≠ M₁ :=
    hilbert_noncollinear_ne_first Geo M₂ M₁ V₃ hTri

  rcases ExtendSegmentBeyond Geo M₁ M₂ hM₂M₁.symm with
    ⟨T, hM₁M₂TBetween, hSeg⟩

  have hM₁M₂TData :=
    HilbertOrder.between_incidence M₁ M₂ T hM₁M₂TBetween

  have hM₁M₂T : Collinear Geo M₁ M₂ T :=
    hM₁M₂TData.2.2.2.1

  have hM₁M₂TTarski : TarskiCollinear Geo M₁ M₂ T := by
    left
    exact hM₁M₂TBetween

  have hM₂T : M₂ ≠ T :=
    hM₁M₂TData.2.1

  have hV₁M₁V₃ :=
    hM₁.left

  have hV₃M₂V₂ :=
    CollinearSymmetry Geo V₂ M₂ V₃ hM₂.left

  have hTri₂ : ¬ Collinear Geo M₂ T V₂ := by
    intro hM₂TV₂

    have hM₂TV₂Tarski : TarskiCollinear Geo M₂ T V₂ := by
      exact tarski_collinear_of_geometry Geo M₂ T V₂ hM₂TV₂

    have hM₁M₂V₂Tarski : TarskiCollinear Geo M₁ M₂ V₂ := by
      exact
        tarski_collinear_trans
          Geo M₁ M₂ T V₂
          hM₂T
          hM₁M₂TTarski
          hM₂TV₂Tarski

    have hM₂V₂V₃Tarski : TarskiCollinear Geo M₂ V₂ V₃ := by
      right
      right
      exact hM₂Between

    have hM₁M₂V₃Tarski : TarskiCollinear Geo M₁ M₂ V₃ := by
      exact
        tarski_collinear_trans
          Geo M₁ M₂ V₂ V₃
          hM₂V₂
          hM₁M₂V₂Tarski
          hM₂V₂V₃Tarski

    have hM₁M₂V₃ : Collinear Geo M₁ M₂ V₃ := by
      exact collinear_of_tarski Geo M₁ M₂ V₃ hM₁M₂V₃Tarski

    exact hTri
      (PrimCollinearSwap Geo M₁ M₂ V₃ hM₁M₂V₃)

  have hVert :=
    VerticalAngles
      Geo V₃ M₂ M₁ V₂ T
      hM₂Between hM₁M₂TBetween
      (fun h =>
        hTri (PrimCollinearCycle Geo V₃ M₂ M₁ h))
  have hVert' := AngleCongruentReverse Geo V₃ M₂ M₁ V₂ M₂ T hVert
  have hSideM₁M₂M₂T := CongruentReverseFirst Geo M₁ M₂ M₂ T hSeg
  have hSideV₂M₂M₂V₃ :=
    CongruentReverseBoth Geo V₂ M₂ M₂ V₃ hM₂.right
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

  have hParV₁M₁V₂T :=
    parallel_from_equal_angles Geo V₁ V₃ M₁ V₂ M₂ T
      hM₁Between
      hM₂Between
      hM₁M₂TBetween
      (fun h =>
        hTri (PrimCollinearCycle Geo V₃ M₂ M₁ h))
      hCong.angleC

  have hSideV₃M₁V₂T :=
    CongruentReverseFirstSwapSecond
      Geo M₁ V₃ T V₂ hCong.sideBC
  have hSideV₁M₁V₂T :=
    congruent_transitivity Geo V₁ M₁ V₃ V₂ T
      hM₁.right
      hSideV₃M₁V₂T
  have hOnePair : OnePairParallelCongruent Geo V₁ V₂ T M₁ :=
    onePairParallelCongruent_of_crossing
      Geo V₁ V₂ T M₁ V₃ M₂
      hM₁Between
      hM₂Between
      hM₁M₂TBetween
      hTri
      hParV₁M₁V₂T
      hSideV₁M₁V₂T
  have hParallelogram :=
    OnePairParallelCongruentCriterion
      Geo V₁ V₂ T M₁ hOnePair

  have hParM₁TV₁V₂ :=
    ParallelogramAdjacentParallel
      Geo V₁ V₂ T M₁ hParallelogram

  exact
    collinear_parallel_trans
      Geo M₁ M₂ T V₁ V₂
      hM₂M₁.symm
      hM₁M₂T
      hParM₁TV₁V₂

/--
The midsegment theorem for midpoints expressed in Tarski's primitive
betweenness and congruence language.
-/
theorem MidsegmentTheoremTarski
    (A B C M N : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B)
    (hN : TarskiIsMidpoint Geo N A C)
    (hTri : ¬ Collinear Geo N M A) :
    Geo.Parallel M N B C := by
  have hMGeometry : IsMidpoint Geo M A B :=
    midpoint_of_tarski Geo M A B hM
  have hNGeometry : IsMidpoint Geo N A C :=
    midpoint_of_tarski Geo N A C hN
  have hMBA : IsMidpoint Geo M B A :=
    midpointSymmetry Geo M A B hMGeometry
  have hNCA : IsMidpoint Geo N C A :=
    midpointSymmetry Geo N A C hNGeometry
  have hNC : N ≠ C :=
    (HilbertOrder.between_incidence A N C hN.left).2.1
  exact
    midsegmentParallelFromGeometryMidpoints
      Geo B C A M N hMBA hNCA
      (HilbertOrder.between_incidence
        A M B hM.left).2.2.2.2
      hN.left hNC hTri

end Tarski

end Geometry

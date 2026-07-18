import CGJteamLab.GeometryBase

namespace Geometry

universe u

variable (Geo : Geo)

theorem MidsegmentParallel
    (V₁ V₂ V₃ M₁ M₂ : Geo.Point)
    (hM₁ : IsMidpoint Geo M₁ V₁ V₃)
    (hM₂ : IsMidpoint Geo M₂ V₂ V₃) :
    Geo.Parallel M₁ M₂ V₁ V₂ := by


  rcases ExtendSegment Geo M₁ M₂ with ⟨T, hM₁M₂T, hSeg⟩

  have hV₁M₁V₃ := hM₁.left
  have hV₃M₂V₂ := CollinearSymmetry Geo V₂ M₂ V₃ hM₂.left

  have hVert := VerticalAngles Geo V₃ M₂ M₁ V₂ T hV₃M₂V₂ hM₁M₂T
  have hVert' := AngleCongruentReverse Geo V₃ M₂ M₁ V₂ M₂ T hVert
  have hSideM₁M₂M₂T := CongruentReverseFirst Geo M₁ M₂ M₂ T hSeg
  have hSideV₂M₂M₂V₃ := CongruentReverseBoth Geo V₂ M₂ M₂ V₃ hM₂.right

  have hSideV₃M₂M₂V₂ := CongruentReverseFirst Geo V₃ M₂ M₂ V₂
    (CongruentSymmetry Geo M₂ V₂ V₃ M₂ hSideV₂M₂M₂V₃)
  have hCong := TriangleCongruentFromSAS Geo M₂ M₁ V₃ M₂ T V₂
    hSideM₁M₂M₂T hVert' hSideV₃M₂M₂V₂

  have hParV₁M₁V₂T := parallel_from_equal_angles Geo V₁ V₃ M₁ V₂ M₂ T
    (CollinearRotate Geo V₁ M₁ V₃ hV₁M₁V₃) hCong.angleC
  have hSideM₁V₃TV₂ := hCong.sideBC

  have hSideV₃M₁TV₂ : Geo.Congruent V₃ M₁ T V₂ :=
    CongruentReverseFirst Geo M₁ V₃ T V₂ hSideM₁V₃TV₂
  have hSideV₃M₁V₂T : Geo.Congruent V₃ M₁ V₂ T :=
    CongruentSwapSecond Geo V₃ M₁ T V₂ hSideV₃M₁TV₂
  have hSideV₁M₁V₂T := congruent_transitivity Geo V₁ M₁ V₃ V₂ T
    hM₁.right hSideV₃M₁V₂T

  have hOnePair : OnePairParallelCongruent Geo V₁ V₂ T M₁ := by
    constructor
    exact hParV₁M₁V₂T
    exact hSideV₁M₁V₂T

  have hParallelogram := OnePairParallelCongruentCriterion Geo V₁ V₂ T M₁ hOnePair

  have hOpp := ParallelogramOppositeSidesParallel Geo V₁ V₂ T M₁ hParallelogram
  rcases hOpp with ⟨hPar1, hPar2⟩

  have hParTM₁V₁V₂ := ParallelSymmetry Geo V₁ V₂ T M₁ hPar1
  have hParM₁TV₁V₂ := ParallelSwapFirstLine Geo T M₁ V₁ V₂ hParTM₁V₁V₂

  exact collinear_parallel_trans Geo M₁ M₂ T V₁ V₂ hM₁M₂T hParM₁TV₁V₂

theorem MidpointSymmetry
    (M A B : Geo.Point)
    (h : IsMidpoint Geo M A B) :
    IsMidpoint Geo M B A := by
  rcases h with ⟨hCol, hCong⟩
  constructor
  · exact CollinearSymmetry Geo A M B hCol
  ·
    have h1 : Geo.Congruent M A B M :=
      CongruentReverseBoth Geo A M M B hCong
    exact CongruentSymmetry Geo M A B M h1

theorem MidsegmentTheorem
    (A B C M N : Geo.Point)
    (hM : IsMidpoint Geo M A B)
    (hN : IsMidpoint Geo N A C) :
    Geo.Parallel M N B C := by
  have hMBA : IsMidpoint Geo M B A :=
    MidpointSymmetry Geo M A B hM
  have hNCA : IsMidpoint Geo N C A :=
    MidpointSymmetry Geo N A C hN
  exact MidsegmentParallel Geo B C A M N hMBA hNCA



end Geometry

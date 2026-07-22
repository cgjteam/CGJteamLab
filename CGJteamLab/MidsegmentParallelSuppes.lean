import CGJteamLab.GeometryBase
import CGJteamLab.SuppesTheorems

/-!
# Midsegment parallelism via Suppes

This is the alternative, Suppes-based route to the midsegment theorem.
`GeometryBase.lean` is left unchanged. The bridge below records how the
primitive operations of Suppes' affine theory are interpreted for a `Geo`.
-/

namespace Geometry

universe u

open Suppes

variable (Geo : Geometry.Geo)
variable [HilbertIncidence Geo]
variable [SuppesGeometry Geo.Point]

local notation "SMid" => SuppesGeometry.operation_midpoint
local notation "SDbl" => SuppesGeometry.operation_double
local notation "SCol" => SuppesGeometry.Collinear

/-- Suppes' Definition 3 of parallel segments. -/
def SuppesParallel (A B C D : Geo.Point) : Prop :=
  PrimTriangle A B C ∧ C ≠ D ∧
  PrimParallelogram A B (SDbl A (SMid B D)) D ∧
  SCol C (SDbl A (SMid B D)) D

/-- Suppes' Theorem 16(vi), for one pair of opposite sides. -/
theorem suppes_parallel_of_parallelogram
    (A B C D : Geo.Point)
    (h : PrimParallelogram A B C D) :
    SuppesParallel Geo A B C D := by
  rcases h with ⟨hTri, hMid⟩
  have hCD : C ≠ D := by
    intro hCD
    have hMid' : SMid A C = SMid B C := by
      calc
        SMid A C = SMid B D := hMid
        _ = SMid B C := by rw [hCD]
    have hAB : A = B := by
      apply midpoint_cancellation C A B
      calc
        SMid C A = SMid A C := midpoint_commutative C A
        _ = SMid B C := hMid'
        _ = SMid C B := midpoint_commutative B C
    apply hTri
    apply L2
    exact Or.inl hAB
  have hDouble : SDbl A (SMid B D) = C := by
    apply midpoint_cancellation A (SDbl A (SMid B D)) C
    calc
      SMid A (SDbl A (SMid B D)) = SMid B D :=
        midpoint_double_reduction A (SMid B D)
      _ = SMid A C := hMid.symm
  refine ⟨hTri, hCD, ?_, ?_⟩
  · rw [hDouble]
    exact ⟨hTri, hMid⟩
  · rw [hDouble]
    apply L2
    exact Or.inl rfl

/-- Interpretation data exposing Suppes' affine result through `GeometryBase`. -/
class SuppesMidsegmentBridge (Geo : Geometry.Geo)
    [HilbertIncidence Geo] [SuppesGeometry Geo.Point] : Prop where
  midpoint_eq : ∀ (A B M : Geo.Point), IsMidpoint Geo M A B → M = SMid A B
  collinear_iff : ∀ (A B C : Geo.Point), Collinear Geo A B C ↔ SCol A B C
  parallel_of_suppes :
    ∀ (A B C D : Geo.Point), SuppesParallel Geo A B C D → Geo.Parallel A B C D
  degenerate_midsegment_parallel :
    ∀ (A B C M N : Geo.Point), Collinear Geo A B C →
      IsMidpoint Geo M A B → IsMidpoint Geo N A C → Geo.Parallel M N B C

variable [SuppesMidsegmentBridge Geo]

/-- The midsegment theorem obtained from Suppes' Theorem 11. -/
theorem MidsegmentTheoremSuppes
    (A B C M N : Geo.Point)
    (hM : IsMidpoint Geo M A B)
    (hN : IsMidpoint Geo N A C) :
    Geo.Parallel M N B C := by
  let bridge : SuppesMidsegmentBridge Geo := inferInstance
  by_cases hCol : Collinear Geo A B C
  · exact bridge.degenerate_midsegment_parallel A B C M N hCol hM hN
  · have hTriBCA : PrimTriangle B C A := by
      intro hSCol
      apply hCol
      have hBCA : Collinear Geo B C A :=
        (bridge.collinear_iff B C A).mpr hSCol
      have hACB : Collinear Geo A C B := CollinearSymmetry Geo B C A hBCA
      exact CollinearRotate Geo A C B hACB
    have hP : PrimParallelogram B (SMid B C) (SMid A C) (SMid A B) := by
      simpa using (theorem11 B C A hTriBCA)
    have hSP : SuppesParallel Geo B (SMid B C) (SMid A C) (SMid A B) :=
      suppes_parallel_of_parallelogram Geo B (SMid B C) (SMid A C) (SMid A B) hP
    have hPar : Geo.Parallel B (SMid B C) (SMid A C) (SMid A B) :=
      bridge.parallel_of_suppes _ _ _ _ hSP
    have hBCMid : Collinear Geo B C (SMid B C) :=
      (bridge.collinear_iff B C (SMid B C)).mpr
        (Suppes.midpoint_collinear B C)
    have hPar' : Geo.Parallel B C (SMid A C) (SMid A B) :=
      collinear_parallel_trans Geo B C (SMid B C) (SMid A C) (SMid A B) hBCMid hPar
    have hPar'' : Geo.Parallel (SMid A C) (SMid A B) B C :=
      ParallelSymmetry Geo B C (SMid A C) (SMid A B) hPar'
    have hMidPar : Geo.Parallel (SMid A B) (SMid A C) B C :=
      ParallelSwapFirstLine Geo (SMid A C) (SMid A B) B C hPar''
    have hM' : M = SMid A B :=
      bridge.midpoint_eq A B M hM
    have hN' : N = SMid A C :=
      bridge.midpoint_eq A C N hN
    simpa [hM', hN'] using hMidPar

end Geometry

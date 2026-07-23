import CGJteamLab.SuppesBase

/-!
# Midsegment parallelism via Suppes

This is the alternative, Suppes-based route to the midsegment theorem.
`SuppesBase.lean` provides the interpretation of Suppes' affine theory
through the common language of `GeometryBase.lean`.
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

import CGJteamLab.SuppesInterface


namespace Geometry
namespace Suppes

universe u

variable {Point : Type u}
variable [SuppesGeometry Point]

local notation "Mid" =>
  (SuppesGeometry.operation_midpoint (Point := Point))

/--
Suppes midsegment theorem.

For a noncollinear triangle ABC, the segment joining the midpoints
of AB and BC is parallel to the segment joining A to the midpoint
of AC.
-/
theorem MidsegmentTheoremSuppes
    (A B C : Point)
    (hT : PrimTriangle A B C) :
    SuppesParallel
      (Mid A B)
      (Mid B C)
      A
      (Mid A C) := by
  have hP :
      PrimParallelogram
        A
        (Mid A B)
        (Mid B C)
        (Mid A C) :=
    theorem11 A B C hT

  exact
    parallelogram_parallel_second
      A
      (Mid A B)
      (Mid B C)
      (Mid A C)
      hP

end Suppes
end Geometry

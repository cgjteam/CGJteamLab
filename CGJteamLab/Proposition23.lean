import CGJteamLab.HilbertInterface
import CGJteamLab.HilbertBookZero
import CGJteamLab.Proposition22

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid I.23.

On a given straight line, and at a given point on it, construct
a rectilinear angle congruent to a given rectilinear angle.

In the Hilbert reconstruction this is a direct consequence of
Hilbert III.4: angle construction on a prescribed side of a
prescribed ray.
-/
theorem euclid_proposition_23
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E S : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hDE : D ≠ E)
    (base : Geo.Line)
    (hDbase : HilbertIncidence.OnLine D base)
    (hEbase : HilbertIncidence.OnLine E base)
    (hSbase : ¬ HilbertIncidence.OnLine S base) :
    ∃ F : Geo.Point,
      HilbertSameSide Geo F S base ∧
      Geo.AngleCongruent A B C D E F := by

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A B C
        D E
        S
        hABC
        hDE
        base
        hDbase
        hEbase
        hSbase with
    ⟨F, hFSame, hAngle, _hUnique⟩

  exact ⟨F, hFSame, hAngle⟩

end Geometry

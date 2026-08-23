import CGJteamLab.HilbertScissors
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Geometry

universe u v

variable (Geo : Geometry.Geo)

/-- An additive valuation on Hilbert scissors terms. -/
structure HilbertScissorsValuation
    (M : Type v)
    [AddCommMonoid M] where
  value : HilbertScissorsTerm Geo -> M

  map_add :
    forall P Q : HilbertScissorsTerm Geo,
      value (P + Q) = value P + value Q

  map_split :
    forall (A B C X : Geo.Point),
      Geo.Between B X C ->
      value (hilbertScissorsTriangle Geo A B C) =
        value
          (hilbertScissorsTriangle Geo A B X +
           hilbertScissorsTriangle Geo A X C)

  map_congruent :
    forall (A B C D E F : Geo.Point),
      TriangleCongruenceResult Geo A B C D E F ->
      value (hilbertScissorsTriangle Geo A B C) =
        value (hilbertScissorsTriangle Geo D E F)


theorem HilbertScissorsValuation.eq_of_scissorsEq
    {M : Type v}
    [AddCommMonoid M]
    (V : HilbertScissorsValuation Geo M)
    {P Q : HilbertScissorsTerm Geo}
    (h : HilbertScissorsEq Geo P Q) :
    V.value P = V.value Q := by
  induction h with
  | refl P =>
      rfl
  | symm h ih =>
      exact ih.symm
  | trans hPQ hQR ihPQ ihQR =>
      exact ihPQ.trans ihQR
  | add hPQ hRS ihPQ ihRS =>
      calc
        V.value (_ + _) = V.value _ + V.value _ := V.map_add _ _
        _ = V.value _ + V.value _ := by rw [ihPQ, ihRS]
        _ = V.value (_ + _) := (V.map_add _ _).symm
  | split A B C X hBXC =>
      exact V.map_split A B C X hBXC
  | congruent A B C D E F hCong =>
      exact V.map_congruent A B C D E F hCong

/-- A cancellative additive valuation is constant on equicomplementable terms. -/
theorem HilbertScissorsValuation.eq_of_equicomplementable
    {M : Type v}
    [AddCancelCommMonoid M]
    (V : HilbertScissorsValuation Geo M)
    {P Q : HilbertScissorsTerm Geo}
    (h : HilbertScissorsEquicomplementable Geo P Q) :
    V.value P = V.value Q := by
  let R := h.choose
  let S := h.choose_spec.choose
  have hRS : HilbertScissorsEq Geo R S :=
    h.choose_spec.choose_spec.1
  have hPQ : HilbertScissorsEq Geo (P + R) (Q + S) :=
    h.choose_spec.choose_spec.2

  have hRSval : V.value R = V.value S :=
    HilbertScissorsValuation.eq_of_scissorsEq Geo V hRS

  have hPQval :
      V.value P + V.value R = V.value Q + V.value S := by
    calc
      V.value P + V.value R = V.value (P + R) := (V.map_add P R).symm
      _ = V.value (Q + S) :=
        HilbertScissorsValuation.eq_of_scissorsEq Geo V hPQ
      _ = V.value Q + V.value S := V.map_add Q S

  rw [hRSval.symm] at hPQval
  exact add_right_cancel hPQval

/-- A weight assigned to one formal triangle. -/
structure HilbertTriangleWeight
    (M : Type v)
    [AddCommMonoid M] where
  weight : HilbertTriangleTerm Geo -> M

  split :
    forall (A B C X : Geo.Point),
      Geo.Between B X C ->
      weight (hilbertTriangleTerm Geo A B C) =
        weight (hilbertTriangleTerm Geo A B X) +
        weight (hilbertTriangleTerm Geo A X C)

  congruent :
    forall (A B C D E F : Geo.Point),
      TriangleCongruenceResult Geo A B C D E F ->
      weight (hilbertTriangleTerm Geo A B C) =
        weight (hilbertTriangleTerm Geo D E F)

/-- Extend a triangle weight additively to formal scissors sums. -/
def HilbertTriangleWeight.toValuation
    {M : Type v}
    [AddCommMonoid M]
    (W : HilbertTriangleWeight Geo M) :
    HilbertScissorsValuation Geo M :=
  {
    value := fun P => (Multiset.map W.weight P).sum

    map_add := by
      intro P Q
      simp

    map_split := by
      intro A B C X hBXC
      simpa [hilbertScissorsTriangle] using
        W.split A B C X hBXC

    map_congruent := by
      intro A B C D E F hCong
      simpa [hilbertScissorsTriangle] using
        W.congruent A B C D E F hCong
  }

end Geometry

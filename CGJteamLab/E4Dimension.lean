import CGJteamLab.SalasExchange

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Synthetic dimension four

This module adds exactly one new ingredient beyond the dimension-free
Sancho de Salas incidence theory: the assertion that the ambient geometry
has dimension exactly four.

The formulation is closure-theoretic and uses the already existing
`SmithSpan` calculus.  No numerical rank function is introduced.

The two clauses have distinct roles:

* `frame_exists` is the lower bound `dim >= 4`;
* `generated3Flat_adjoin_external_eq_univ` is the upper bound `dim <= 4`.

Thus the class below is not an incidence axiom of Hilbert, Smith, Wyler, or
Sancho de Salas.  It is the explicit dimension-four assumption of the
present development.

No hyperplane primitive, order, congruence, Euclidean axiom, metric,
orthogonality, reflection, or continuity is introduced here.
-/

/--
A four-point generated 3-flat certificate.

The first three points generate a plane and the fourth point lies outside
that plane span.
-/
def E4Generated3Flat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point) : Prop :=
  exists A B C D : Geo.Point,
    Not (PrimCollinear Geo A B C) /\
    Not (SmithSpan Geo (SmithPointTriple Geo A B C) D) /\
    F =
      SmithSpan Geo
        (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)


/--
A five-point frame witnessing four-dimensional growth.

A,B,C generate a plane, D lies outside that plane span, and P lies outside
the generated 3-flat.
-/
def E4Frame
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (A B C D P : Geo.Point) : Prop :=
  Not (PrimCollinear Geo A B C) /\
  Not (SmithSpan Geo (SmithPointTriple Geo A B C) D) /\
  Not
    (SmithSpan Geo
      (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)
      P)


/--
The set of the five named generators of an E4 frame.
-/
def E4PointFive
    (A B C D P : Geo.Point) : Set Geo.Point :=
  SmithAdjoinPoint Geo
    (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)
    P


/--
A generated 3-flat is a Smith flat.
-/
theorem e4Generated3Flat_flat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point)
    (hF : E4Generated3Flat Geo F) :
    SmithFlat Geo F := by

  rcases hF with
    ⟨A, B, C, D, _hABC, _hDout, hFspan⟩

  rw [hFspan]

  exact
    smithSpan_flat
      (Geo := Geo)
      (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)


/--
Closing a set before adjoining one new point does not change the final
generated Smith span.
-/
theorem e4_span_adjoin_span_eq_adjoin
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point)
    (P : Geo.Point) :
    SmithSpan Geo
        (SmithAdjoinPoint Geo (SmithSpan Geo X) P) =
      SmithSpan Geo (SmithAdjoinPoint Geo X P) := by

  apply Set.Subset.antisymm

  · apply
      smithSpan_least
        (Geo := Geo)
        (SmithAdjoinPoint Geo (SmithSpan Geo X) P)
        (SmithSpan Geo (SmithAdjoinPoint Geo X P))
        (smithSpan_flat
          (Geo := Geo)
          (SmithAdjoinPoint Geo X P))

    intro Q hQ
    rcases hQ with hQP | hQspan

    · subst Q
      exact
        smithSpan_extensive
          (Geo := Geo)
          (SmithAdjoinPoint Geo X P)
          (Or.inl rfl)

    · have hXadjoin :
          Set.Subset X (SmithAdjoinPoint Geo X P) := by
        intro R hRX
        exact Or.inr hRX

      exact
        smithSpan_mono
          (Geo := Geo)
          hXadjoin
          hQspan

  · apply
      smithSpan_mono
        (Geo := Geo)

    intro Q hQ
    rcases hQ with hQP | hQX

    · exact Or.inl hQP

    · exact
        Or.inr
          (smithSpan_extensive
            (Geo := Geo)
            X hQX)


/--
The explicit dimension-four assumption.

`frame_exists` prevents dimensions <= 3.

`generated3Flat_adjoin_external_eq_univ` prevents dimensions >= 5:
once a genuine generated 3-flat is present, adjoining any point outside it
already generates the whole ambient geometry.
-/
class E4Dimension
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop where

  frame_exists :
    exists A B C D P : Geo.Point,
      E4Frame Geo A B C D P

  generated3Flat_adjoin_external_eq_univ :
    forall (F : Set Geo.Point) (P : Geo.Point),
      E4Generated3Flat Geo F ->
      Not (F P) ->
      SmithSpan Geo (SmithAdjoinPoint Geo F P) =
        (Set.univ : Set Geo.Point)


/--
Every E4 frame spans the whole ambient point space.
-/
theorem e4Frame_span_eq_univ
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D4 : E4Dimension Geo]
    (A B C D P : Geo.Point)
    (hFrame : E4Frame Geo A B C D P) :
    SmithSpan Geo (E4PointFive Geo A B C D P) =
      (Set.univ : Set Geo.Point) := by

  rcases hFrame with
    ⟨hABC, hDout, hPout⟩

  let F : Set Geo.Point :=
    SmithSpan Geo
      (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)

  have hF : E4Generated3Flat Geo F := by
    exact
      ⟨A, B, C, D,
       hABC,
       hDout,
       rfl⟩

  have hPoutF : Not (F P) := by
    simpa [F] using hPout

  have hAmbient :
      SmithSpan Geo (SmithAdjoinPoint Geo F P) =
        (Set.univ : Set Geo.Point) :=
    D4.generated3Flat_adjoin_external_eq_univ
      F P hF hPoutF

  have hNormal :
      SmithSpan Geo
          (SmithAdjoinPoint Geo
            (SmithSpan Geo
              (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D))
            P) =
        SmithSpan Geo (E4PointFive Geo A B C D P) := by
    simpa [E4PointFive] using
      e4_span_adjoin_span_eq_adjoin
        (Geo := Geo)
        (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)
        P

  dsimp [F] at hAmbient
  rw [hNormal] at hAmbient
  exact hAmbient


/--
Dimension four supplies an actual five-point spanning frame.
-/
theorem e4Dimension_exists_spanning_frame
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D4 : E4Dimension Geo] :
    exists A B C D P : Geo.Point,
      E4Frame Geo A B C D P /\
      SmithSpan Geo (E4PointFive Geo A B C D P) =
        (Set.univ : Set Geo.Point) := by

  rcases D4.frame_exists with
    ⟨A, B, C, D, P, hFrame⟩

  exact
    ⟨A, B, C, D, P,
     hFrame,
     e4Frame_span_eq_univ
       (Geo := Geo)
       A B C D P
       hFrame⟩

end Geometry

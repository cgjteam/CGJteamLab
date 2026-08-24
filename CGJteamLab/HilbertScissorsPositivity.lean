import CGJteamLab.HilbertScissorsInvariant

namespace Geometry

universe u v

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- De Zolt as positivity
--
-- The specialized De Zolt principle used in Euclid I.39 is not a
-- geometric statement about the configuration B - X - A.  It is the
-- statement that the scissors calculus admits an additive invariant
-- that does not vanish on nondegenerate triangles.
--
-- Isolating it in that form has three effects:
--
--   * the assumption stops mentioning any configuration, so it cannot
--     hide an order or incidence defect;
--   * it is discharged in three lines once an area valuation exists
--     (Hartshorne, Prop. 23.1(a),(d) and Thm. 23.2);
--   * it is the same assumption that I.40 and the converse of the
--     theory of content will need, so it is proved once.
--
-- It is genuinely an assumption and not an oversight: by Hilbert's
-- footnote on p. 64 of the Foundations, the geometry of Appendix II
-- satisfies Groups I-IV, with a restricted form of III,5, and refutes
-- both Theorem 48 and "the whole is greater than the part".  No
-- derivation from Groups I-III together with the parallel axiom is
-- possible.
------------------------------------------------------------------------


/--
Cutting a triangle at a point on the side joining the second vertex
to the first.

`HilbertScissorsEq.split` cuts the side joining the second and third
vertices of the triangle term.  A triangle term is a multiset of its
vertices, so taking `C` as apex cuts the side `B A` directly, and the
three permutation lemmas put the result back into the orientation used
by the caller.
-/
theorem scissors_split_side
    (A B C X : Geo.Point)
    (hBXA : Geo.Between B X A) :
    HilbertScissorsEq Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo X B C +
       hilbertScissorsTriangle Geo A X C) := by

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo C B A)
        (hilbertScissorsTriangle Geo C B X +
         hilbertScissorsTriangle Geo C X A) :=
    HilbertScissorsEq.split
      (Geo := Geo) C B A X hBXA

  have hCBA :
      hilbertScissorsTriangle Geo C B A =
        hilbertScissorsTriangle Geo A B C := by
    rw [scissors_triangle_swap12 Geo C B A,
        scissors_triangle_swap23 Geo B C A,
        scissors_triangle_swap12 Geo B A C]

  have hCBX :
      hilbertScissorsTriangle Geo C B X =
        hilbertScissorsTriangle Geo X B C := by
    rw [scissors_triangle_swap12 Geo C B X,
        scissors_triangle_swap23 Geo B C X,
        scissors_triangle_swap12 Geo B X C]

  have hCXA :
      hilbertScissorsTriangle Geo C X A =
        hilbertScissorsTriangle Geo A X C := by
    rw [scissors_triangle_swap12 Geo C X A,
        scissors_triangle_swap23 Geo X C A,
        scissors_triangle_swap12 Geo X A C]

  rw [hCBA, hCBX, hCXA] at hSplit

  exact hSplit


/--
Positivity of content: adjoining a nondegenerate triangle to a
scissors term does not produce an equicomplementable term.

This is the single temporary assumption of the De Zolt route.
-/
axiom hilbert_scissors_triangle_positive
    [HilbertIncidence Geo]
    (P : HilbertScissorsTerm Geo)
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    ¬ HilbertScissorsEquicomplementable Geo
        (P + hilbertScissorsTriangle Geo A B C)
        P

-- Discharge, once an area valuation is available.  Let
--
--   V : HilbertScissorsValuation Geo M,  M an AddCancelCommMonoid,
--   hV : V.value (hilbertScissorsTriangle Geo A B C) <> 0
--        for noncollinear A B C
--
-- (Hartshorne Thm. 23.2 builds exactly this, with M the additive
-- group of the field of segment arithmetic and
-- V = half base times altitude; the halving is not needed here).
-- Then:
--
--   intro h
--   have hval := V.eq_of_equicomplementable Geo h
--   rw [V.map_add] at hval
--   exact hV (by simpa using add_left_cancel (hval.trans (add_zero _).symm))


/--
Specialized De Zolt principle used in Euclid I.39, now a theorem.

If `X` lies strictly between `B` and `A`, then the triangle `X B C` is
a proper part of `A B C`, and the two cannot have equal content.
-/
theorem hilbert_scissors_triangle_proper_part
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A X B C : Geo.Point)
    (hBXA : Geo.Between B X A)
    (_hBC : B ≠ C)
    (hNoncol : ¬ Collinear Geo B C A) :
    ¬ HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo X B C) := by

  intro hEq

  --------------------------------------------------------------------
  -- The cut-off piece A X C is nondegenerate: X lies on the line B A,
  -- and C does not.
  --------------------------------------------------------------------

  have hData :=
    HilbertOrder.between_incidence B X A hBXA

  have hXA : X ≠ A := hData.2.1

  have hAX : A ≠ X := hXA.symm

  rcases hData.2.2.2.1 with ⟨m, hBm, hXm, hAm⟩

  have hCm :
      ¬ HilbertIncidence.OnLine C m := by
    intro hC
    exact hNoncol ⟨m, hBm, hC, hAm⟩

  have hAXC :
      ¬ Collinear Geo A X C :=
    hilbert_not_collinear_of_off_line
      Geo A X C m hAX hAm hXm hCm

  --------------------------------------------------------------------
  -- A B C splits as X B C together with A X C.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo X B C +
         hilbertScissorsTriangle Geo A X C) :=
    scissors_split_side Geo A B C X hBXA

  have hGrown :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo X B C +
         hilbertScissorsTriangle Geo A X C)
        (hilbertScissorsTriangle Geo X B C) :=
    equicomplementable_trans
      Geo
      (equicomplementable_symm
        Geo
        (equicomplementable_of_scissorsEq Geo hSplit))
      hEq

  exact
    hilbert_scissors_triangle_positive
      Geo
      (hilbertScissorsTriangle Geo X B C)
      A X C
      hAXC
      hGrown

end Geometry

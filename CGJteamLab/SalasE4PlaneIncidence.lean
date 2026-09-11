import CGJteamLab.E4Dimension

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert plane-incidence base derived in E4

For the E4 development, `HilbertPlaneIncidence` need not be an additional
foundation assumption.

Sancho de Salas LP1 supplies the point-line incidence clauses, while
`E4Dimension.frame_exists` supplies a noncollinear triple and, together
with span extensivity, a concrete line containing two distinct points.

Thus

    SalasIncidence + E4Dimension
        -> HilbertPlaneIncidence.

No new axiom is introduced here.
-/

/--
In an E4 frame, the fourth point is different from the first point.
-/
theorem e4Frame_fourth_ne_first
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (A B C D P : Geo.Point)
    (hFrame : E4Frame Geo A B C D P) :
    Ne D A := by

  rcases hFrame with
    ⟨_hABC, hDout, _hPout⟩

  intro hDA
  subst D

  apply hDout

  exact
    smithSpan_extensive
      (Geo := Geo)
      (SmithPointTriple Geo A B C)
      (Or.inl rfl)


/--
Sancho de Salas incidence together with dimension four implies the
historical `HilbertPlaneIncidence` point-line base.

This theorem is intended as a compatibility result: the resulting class
should be installed locally when old code requires it.
-/
theorem salas_e4_implies_hilbertPlaneIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo]
    [D4 : E4Dimension Geo] :
    HilbertPlaneIncidence Geo where

  line_through := by
    intro P Q hPQ

    rcases
        A.line_through_unique
          P Q hPQ with
      ⟨l, hPl, hQl, _hUnique⟩

    exact
      ⟨l, hPl, hQl⟩

  line_unique := by
    intro P Q hPQ l m
      hPl hQl hPm hQm

    rcases
        A.line_through_unique
          P Q hPQ with
      ⟨k, _hPk, _hQk, hUnique⟩

    have hlk : l = k :=
      hUnique l hPl hQl

    have hmk : m = k :=
      hUnique m hPm hQm

    exact hlk.trans hmk.symm

  two_points_on_line := by
    rcases D4.frame_exists with
      ⟨A0, B0, C0, D0, P0, hFrame⟩

    have hDA : Ne D0 A0 :=
      e4Frame_fourth_ne_first
        (Geo := Geo)
        A0 B0 C0 D0 P0
        hFrame

    rcases
        A.line_through_unique
          D0 A0 hDA with
      ⟨l, hDl, hAl, _hUnique⟩

    exact
      ⟨l, D0, A0,
       hDA,
       hDl,
       hAl⟩

  three_noncollinear := by
    rcases D4.frame_exists with
      ⟨A0, B0, C0, D0, P0, hFrame⟩

    exact
      ⟨A0, B0, C0,
       hFrame.1⟩

end Geometry

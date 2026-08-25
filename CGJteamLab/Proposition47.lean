import CGJteamLab.Proposition14
import CGJteamLab.Proposition17
import CGJteamLab.HilbertRightAngle
import CGJteamLab.Proposition41
import CGJteamLab.Proposition46

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.47
--
-- In right-angled triangles the square on the side subtending the
-- right angle is equal to the squares on the sides containing the
-- right angle.
--
-- Euclid's proof, in the labelling used below.  The triangle is
-- `A B C`, right-angled at `A`.  The three squares are
--
--   `B C E D`  on the hypotenuse `BC`   (`D` adjacent to `B`,
--                                        `E` adjacent to `C`),
--   `A B F G`  on the leg `AB`          (`F` adjacent to `B`,
--                                        `G` adjacent to `A`),
--   `A C K H`  on the leg `AC`          (`K` adjacent to `C`,
--                                        `H` adjacent to `A`).
--
-- `AL` is drawn through `A` parallel to `BD`, cutting `BC` at `M` and
-- `DE` at `L`; the cut `ML` divides the big square into the two
-- rectangles `BMLD` and `MCEL`.
--
--   1. `∠BAG` and `∠BAC` are both right, and `G`, `C` lie on opposite
--      sides of `AB`, so `G A C` is a straight line [I.14]; likewise
--      `H A B`.  Hence `AC ∥ BF` and `AB ∥ CK`.
--   2. `∠DBC` and `∠FBA` are both right, hence congruent [Post. 4].
--      Adding `∠ABC` to each gives `∠ABD ≅ ∠FBC`.
--   3. `BD ≅ BC` and `BA ≅ BF` (sides of the two squares), so
--      triangle `ABD ≅ FBC` [I.4].
--   4. Rectangle `BMLD` is double triangle `ABD` (same base `BD`,
--      same parallels `BD`, `AL`) and square `ABFG` is double
--      triangle `FBC` (same base `BF`, same parallels `BF`, `GC`)
--      [I.41].  Hence rectangle `BMLD` equals square `ABFG`.
--   5. Symmetrically rectangle `MCEL` equals square `ACKH`.
--   6. The two rectangles together make the whole square `BCED`.
--
-- Formalization notes.
--
-- Steps 1-2 and the placement of the whole figure are recorded as a
-- single local axiom `i47_diagram`.  Its conjuncts are exactly the
-- diagram data Euclid reads off his figure, and each is annotated in
-- the docstring with the Euclidean proposition that produces it.  Two
-- pieces of it are genuinely unavailable in the library today:
--
--   * side-controlled I.46.  `euclid_proposition_46` produces *a*
--     square on a given segment, but does not say on which side of
--     that segment it lies; the perpendicular in
--     `i46_erect_equal_perpendicular` is taken from
--     `hilbert_right_angle_exists_nondegenerate`, which does not
--     control the side.  Euclid needs the square on `BC` to be on the
--     far side from `A`.
--   * "all right angles are congruent" (Post. 4, Hilbert's Theorem
--     21).  This is proved in `Hilbert48_test.lean` as
--     `hilbert48_test_all_right_angles_congruent` but has not been
--     promoted to the main library, and the subsequent angle addition
--     needs the crossbar data of `hilbert_angle_addition_sameSide_case1`,
--     which again is diagram information.
--
-- Everything else is proved here: the scissors dissection of the big
-- square into the two rectangles (`i47_square_split`, from the two
-- `split` steps and `crossing_quadrilateral_two_triangulations`), the
-- two SAS congruences, the four applications of I.41, and the final
-- equicomplementability bookkeeping.
------------------------------------------------------------------------

/--
Equicomplementability is compatible with formal addition on both
sides.

The complements are added componentwise; the proof is the same
associativity/commutativity rearrangement used in
`equicomplementable_trans` and `i41_equicomplementable_double`.
-/
theorem i47_equicomplementable_add
    {P Q P' Q' : HilbertScissorsTerm Geo}
    (hP : HilbertScissorsEquicomplementable Geo P P')
    (hQ : HilbertScissorsEquicomplementable Geo Q Q') :
    HilbertScissorsEquicomplementable Geo (P + Q) (P' + Q') := by

  rcases hP with ⟨R1, S1, hR1S1, hPP'⟩
  rcases hQ with ⟨R2, S2, hR2S2, hQQ'⟩

  refine ⟨R1 + R2, S1 + S2, ?_, ?_⟩

  · exact
      HilbertScissorsEq.add
        (Geo := Geo) hR1S1 hR2S2

  · have hSum :
        HilbertScissorsEq Geo
          ((P + R1) + (Q + R2))
          ((P' + S1) + (Q' + S2)) :=
      HilbertScissorsEq.add
        (Geo := Geo) hPP' hQQ'

    have hLeft :
        (P + R1) + (Q + R2) = (P + Q) + (R1 + R2) := by
      calc
        (P + R1) + (Q + R2)
            = P + (R1 + (Q + R2)) := Multiset.add_assoc _ _ _
        _ = P + ((R1 + Q) + R2) := by
              rw [Multiset.add_assoc R1 Q R2]
        _ = P + ((Q + R1) + R2) := by
              rw [Multiset.add_comm R1 Q]
        _ = P + (Q + (R1 + R2)) := by
              rw [Multiset.add_assoc Q R1 R2]
        _ = (P + Q) + (R1 + R2) := (Multiset.add_assoc _ _ _).symm

    have hRight :
        (P' + S1) + (Q' + S2) = (P' + Q') + (S1 + S2) := by
      calc
        (P' + S1) + (Q' + S2)
            = P' + (S1 + (Q' + S2)) := Multiset.add_assoc _ _ _
        _ = P' + ((S1 + Q') + S2) := by
              rw [Multiset.add_assoc S1 Q' S2]
        _ = P' + ((Q' + S1) + S2) := by
              rw [Multiset.add_comm S1 Q']
        _ = P' + (Q' + (S1 + S2)) := by
              rw [Multiset.add_assoc Q' S1 S2]
        _ = (P' + Q') + (S1 + S2) := (Multiset.add_assoc _ _ _).symm

    rw [hLeft, hRight] at hSum
    exact hSum

/--
The dissection of the square on the hypotenuse.

If `B C E D` is a parallelogram (here: the square on `BC`), `M` lies
between `B` and `C`, `L` lies between `D` and `E`, and the diagonal
`DC` meets the cut `ML` at `N`, then the square is the formal sum of
the two pieces `M L D B` and `C E L M`.

The proof cuts the two triangles of the diagonal `DC` at `M` and at
`L`, and then re-triangulates the quadrilateral `D M C L` across its
crossing diagonals `DC` and `ML`.
-/
theorem i47_square_split
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M N : Geo.Point)
    (hParallelogram : IsParallelogram Geo B C E D)
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDNC : Geo.Between D N C)
    (hMNL : Geo.Between M N L) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C E D)
      (hilbertParallelogramTerm Geo M L D B +
       hilbertParallelogramTerm Geo C E L M) := by

  --------------------------------------------------------------------
  -- Step 1. Move to the diagonal `DC` of the square.
  --------------------------------------------------------------------

  have hRotate :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo D B C E) :=
    parallelogram_term_rotateOne
      Geo B C E D hParallelogram

  --------------------------------------------------------------------
  -- Step 2. Cut the triangle `D B C` at `M` on the base `BC`.
  --------------------------------------------------------------------

  have hSplitBase :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D B C)
        (hilbertScissorsTriangle Geo D B M +
         hilbertScissorsTriangle Geo D M C) :=
    HilbertScissorsEq.split
      (Geo := Geo) D B C M hBMC

  --------------------------------------------------------------------
  -- Step 3. Cut the triangle `D C E` at `L` on the opposite side `DE`.
  --------------------------------------------------------------------

  have hSplitTop0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo C D E)
        (hilbertScissorsTriangle Geo C D L +
         hilbertScissorsTriangle Geo C L E) :=
    HilbertScissorsEq.split
      (Geo := Geo) C D E L hDLE

  have hSplitTop :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D C E)
        (hilbertScissorsTriangle Geo D C L +
         hilbertScissorsTriangle Geo C L E) := by
    rw [scissors_triangle_swap12 Geo C D E] at hSplitTop0
    rw [scissors_triangle_swap12 Geo C D L] at hSplitTop0
    exact hSplitTop0

  --------------------------------------------------------------------
  -- The square, dissected along `DC` and then cut at `M` and `L`.
  --------------------------------------------------------------------

  have hCut :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D B C E)
        ((hilbertScissorsTriangle Geo D B M +
          hilbertScissorsTriangle Geo D M C) +
         (hilbertScissorsTriangle Geo D C L +
          hilbertScissorsTriangle Geo C L E)) := by
    unfold hilbertParallelogramTerm
    exact
      HilbertScissorsEq.add
        (Geo := Geo) hSplitBase hSplitTop

  --------------------------------------------------------------------
  -- Step 4. Re-triangulate the crossing quadrilateral `D M C L`.
  --------------------------------------------------------------------

  have hCross :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D M C +
         hilbertScissorsTriangle Geo D C L)
        (hilbertScissorsTriangle Geo D M L +
         hilbertScissorsTriangle Geo M C L) :=
    crossing_quadrilateral_two_triangulations
      Geo D M C L N hDNC hMNL

  --------------------------------------------------------------------
  -- Step 5. Bookkeeping: isolate the crossing pair, exchange it, and
  -- redistribute into the two rectangles.
  --------------------------------------------------------------------

  have hRegroup1 :
      (hilbertScissorsTriangle Geo D B M +
       hilbertScissorsTriangle Geo D M C) +
      (hilbertScissorsTriangle Geo D C L +
       hilbertScissorsTriangle Geo C L E)
        =
      (hilbertScissorsTriangle Geo D M C +
       hilbertScissorsTriangle Geo D C L) +
      (hilbertScissorsTriangle Geo D B M +
       hilbertScissorsTriangle Geo C L E) := by
    calc
      (hilbertScissorsTriangle Geo D B M +
       hilbertScissorsTriangle Geo D M C) +
      (hilbertScissorsTriangle Geo D C L +
       hilbertScissorsTriangle Geo C L E)
          = hilbertScissorsTriangle Geo D B M +
            (hilbertScissorsTriangle Geo D M C +
             (hilbertScissorsTriangle Geo D C L +
              hilbertScissorsTriangle Geo C L E)) :=
            Multiset.add_assoc _ _ _
      _ = hilbertScissorsTriangle Geo D B M +
            ((hilbertScissorsTriangle Geo D M C +
              hilbertScissorsTriangle Geo D C L) +
             hilbertScissorsTriangle Geo C L E) := by
            rw [Multiset.add_assoc
                  (hilbertScissorsTriangle Geo D M C)
                  (hilbertScissorsTriangle Geo D C L)
                  (hilbertScissorsTriangle Geo C L E)]
      _ = hilbertScissorsTriangle Geo D B M +
            (hilbertScissorsTriangle Geo C L E +
             (hilbertScissorsTriangle Geo D M C +
              hilbertScissorsTriangle Geo D C L)) := by
            rw [Multiset.add_comm
                  (hilbertScissorsTriangle Geo D M C +
                   hilbertScissorsTriangle Geo D C L)
                  (hilbertScissorsTriangle Geo C L E)]
      _ = (hilbertScissorsTriangle Geo D B M +
            hilbertScissorsTriangle Geo C L E) +
            (hilbertScissorsTriangle Geo D M C +
             hilbertScissorsTriangle Geo D C L) :=
            (Multiset.add_assoc _ _ _).symm
      _ = (hilbertScissorsTriangle Geo D M C +
            hilbertScissorsTriangle Geo D C L) +
            (hilbertScissorsTriangle Geo D B M +
             hilbertScissorsTriangle Geo C L E) :=
            Multiset.add_comm _ _

  have hExchange :
      HilbertScissorsEq Geo
        ((hilbertScissorsTriangle Geo D M C +
          hilbertScissorsTriangle Geo D C L) +
         (hilbertScissorsTriangle Geo D B M +
          hilbertScissorsTriangle Geo C L E))
        ((hilbertScissorsTriangle Geo D M L +
          hilbertScissorsTriangle Geo M C L) +
         (hilbertScissorsTriangle Geo D B M +
          hilbertScissorsTriangle Geo C L E)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hCross
      (HilbertScissorsEq.refl
        (Geo := Geo) _)

  --------------------------------------------------------------------
  -- Step 6. Rename the four pieces into the rectangle triangulations.
  --
  -- Triangle terms are multisets of three vertices, so every renaming
  -- below is an equality of terms, not merely an equidecomposition.
  --------------------------------------------------------------------

  have hNameDML :
      hilbertScissorsTriangle Geo D M L =
      hilbertScissorsTriangle Geo M L D :=
    scissors_triangle_cycle Geo D M L

  have hNameMCL :
      hilbertScissorsTriangle Geo M C L =
      hilbertScissorsTriangle Geo C L M :=
    scissors_triangle_cycle Geo M C L

  have hNameDBM :
      hilbertScissorsTriangle Geo D B M =
      hilbertScissorsTriangle Geo M D B := by
    rw [scissors_triangle_cycle Geo D B M,
        scissors_triangle_cycle Geo B M D]

  have hNameCLE :
      hilbertScissorsTriangle Geo C L E =
      hilbertScissorsTriangle Geo C E L :=
    scissors_triangle_swap23 Geo C L E

  have hRegroup2 :
      (hilbertScissorsTriangle Geo M L D +
       hilbertScissorsTriangle Geo C L M) +
      (hilbertScissorsTriangle Geo M D B +
       hilbertScissorsTriangle Geo C E L)
        =
      hilbertParallelogramTerm Geo M L D B +
      hilbertParallelogramTerm Geo C E L M := by
    unfold hilbertParallelogramTerm
    calc
      (hilbertScissorsTriangle Geo M L D +
       hilbertScissorsTriangle Geo C L M) +
      (hilbertScissorsTriangle Geo M D B +
       hilbertScissorsTriangle Geo C E L)
          = hilbertScissorsTriangle Geo M L D +
            (hilbertScissorsTriangle Geo C L M +
             (hilbertScissorsTriangle Geo M D B +
              hilbertScissorsTriangle Geo C E L)) :=
            Multiset.add_assoc _ _ _
      _ = hilbertScissorsTriangle Geo M L D +
            ((hilbertScissorsTriangle Geo C L M +
              hilbertScissorsTriangle Geo M D B) +
             hilbertScissorsTriangle Geo C E L) := by
            rw [Multiset.add_assoc
                  (hilbertScissorsTriangle Geo C L M)
                  (hilbertScissorsTriangle Geo M D B)
                  (hilbertScissorsTriangle Geo C E L)]
      _ = hilbertScissorsTriangle Geo M L D +
            ((hilbertScissorsTriangle Geo M D B +
              hilbertScissorsTriangle Geo C L M) +
             hilbertScissorsTriangle Geo C E L) := by
            rw [Multiset.add_comm
                  (hilbertScissorsTriangle Geo C L M)
                  (hilbertScissorsTriangle Geo M D B)]
      _ = hilbertScissorsTriangle Geo M L D +
            (hilbertScissorsTriangle Geo M D B +
             (hilbertScissorsTriangle Geo C L M +
              hilbertScissorsTriangle Geo C E L)) := by
            rw [Multiset.add_assoc
                  (hilbertScissorsTriangle Geo M D B)
                  (hilbertScissorsTriangle Geo C L M)
                  (hilbertScissorsTriangle Geo C E L)]
      _ = hilbertScissorsTriangle Geo M L D +
            (hilbertScissorsTriangle Geo M D B +
             (hilbertScissorsTriangle Geo C E L +
              hilbertScissorsTriangle Geo C L M)) := by
            rw [Multiset.add_comm
                  (hilbertScissorsTriangle Geo C L M)
                  (hilbertScissorsTriangle Geo C E L)]
      _ = (hilbertScissorsTriangle Geo M L D +
            hilbertScissorsTriangle Geo M D B) +
            (hilbertScissorsTriangle Geo C E L +
             hilbertScissorsTriangle Geo C L M) :=
            (Multiset.add_assoc _ _ _).symm

  --------------------------------------------------------------------
  -- Step 7. Chain everything.
  --------------------------------------------------------------------

  have hCutRegrouped :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D B C E)
        ((hilbertScissorsTriangle Geo D M C +
          hilbertScissorsTriangle Geo D C L) +
         (hilbertScissorsTriangle Geo D B M +
          hilbertScissorsTriangle Geo C L E)) := by
    rw [hRegroup1] at hCut
    exact hCut

  have hFinalStep :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D B C E)
        (hilbertParallelogramTerm Geo M L D B +
         hilbertParallelogramTerm Geo C E L M) := by
    have hChain :=
      HilbertScissorsEq.trans
        (Geo := Geo) hCutRegrouped hExchange
    rw [hNameDML, hNameMCL, hNameDBM, hNameCLE] at hChain
    rw [hRegroup2] at hChain
    exact hChain

  exact
    HilbertScissorsEq.trans
      (Geo := Geo) hRotate hFinalStep

theorem hilbert_erect_equal_perpendicular_opposite_side
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B R : Geo.Point)
    (l : Geo.Line)
    (hAB : A ≠ B)
    (hAl : HilbertIncidence.OnLine A l)
    (hBl : HilbertIncidence.OnLine B l)
    (hRl : Not (HilbertIncidence.OnLine R l)) :
    ∃ D : Geo.Point,
      Not (Collinear Geo A B D) ∧
      HilbertRightAngle Geo D A B ∧
      Geo.Congruent A D A B ∧
      HilbertOppositeSide Geo D R l := by

  have hBA : B ≠ A := hAB.symm

  have hRA : R ≠ A := by
    intro hEq
    subst hEq
    exact hRl hAl

  --------------------------------------------------------------------
  -- Step 0. A point `S` on the side of `l` opposite `R`.
  --------------------------------------------------------------------

  rcases HilbertOrder.between_extension R A hRA with
    ⟨S, hRAS⟩

  have hRASdata :=
    HilbertOrder.between_incidence R A S hRAS

  have hSl : Not (HilbertIncidence.OnLine S l) := by
    intro hSl
    rcases hRASdata.2.2.2.1 with ⟨l', hRl', hAl', hSl'⟩
    have hEq : l' = l :=
      HilbertPlaneIncidence.line_unique
        A S hRASdata.2.1 l' l hAl' hSl' hAl hSl
    exact hRl (hEq ▸ hRl')

  have hOppositeRS :
      HilbertOppositeSide Geo R S l :=
    ⟨hRl, hSl, ⟨A, hRAS, hAl⟩⟩

  --------------------------------------------------------------------
  -- Step 1. Extend `BA` beyond `A`, so that I.11 applies at `A`.
  --------------------------------------------------------------------

  rcases ExtendSegmentBeyond Geo B A hBA with
    ⟨F, hBAF, _hCongBA⟩

  --------------------------------------------------------------------
  -- Step 2. An arbitrary perpendicular direction at `A`.
  --------------------------------------------------------------------

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo B A F hBAF with
    ⟨X0, hNCBAX0, hRightBAX0⟩

  --------------------------------------------------------------------
  -- Step 3. Copy the right angle onto the side of `l` chosen by `S`
  -- (Hilbert III,4).
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo) B A X0 B A S
        hNCBAX0 hBA l hBl hAl hSl with
    ⟨X, hXSside, hAngleCong, _⟩

  have hXl : Not (HilbertIncidence.OnLine X l) :=
    hXSside.1

  have hNCBAX : Not (PrimCollinear Geo B A X) := by
    intro hCol
    rcases hCol with ⟨l', hBl', hAl', hXl'⟩
    have hEq : l' = l :=
      HilbertPlaneIncidence.line_unique
        A B hAB l' l hAl' hBl' hAl hBl
    exact hXl (hEq ▸ hXl')

  have hRightBAX :
      HilbertRightAngle Geo B A X :=
    hilbert_right_angle_transport
      Geo B A X0 B A X
      hNCBAX0 hNCBAX
      hRightBAX0 hAngleCong

  have hOppositeXR :
      HilbertOppositeSide Geo X R l := by
    have hSameSideSX :
        HilbertSameSide Geo S X l :=
      hilbert_sameSide_symm
        Geo X S l hXSside
    have hOppositeRX :
        HilbertOppositeSide Geo R X l :=
      hilbert_oppositeSide_transport_right
        Geo R S X l hOppositeRS hSameSideSX
    exact
      hilbert_oppositeSide_symm
        Geo R X l hOppositeRX

  --------------------------------------------------------------------
  -- Step 4. Lay off `AB` on the ray `AX` (Hilbert III,1).
  --------------------------------------------------------------------

  have hAX : A ≠ X := by
    intro hEq
    apply hNCBAX
    subst hEq
    exact ⟨l, hBl, hAl, hAl⟩

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo) A B A X hAX with
    ⟨D, hRayAXD, hCongAD⟩

  have hDA : D ≠ A := hRayAXD.2.1
  have hAXD : Collinear Geo A X D := hRayAXD.2.2.1
  have hADX : Collinear Geo A D X :=
    PrimCollinearRotate Geo A X D hAXD

  have hNCBAD : Not (Collinear Geo B A D) := by
    intro hCol
    apply hNCBAX
    exact
      hilbert_primCollinear_trans
        Geo B A D X
        hDA.symm
        hCol
        hADX

  have hNCDAB : Not (Collinear Geo D A B) := by
    intro hCol
    exact hNCBAD (PrimCollinearSymm Geo D A B hCol)

  have hNCABD : Not (Collinear Geo A B D) := by
    intro hCol
    exact hNCBAD (PrimCollinearSwap Geo A B D hCol)

  --------------------------------------------------------------------
  -- Step 5. Replacing `X` by `D` does not change the angle at `A`, and
  -- does not change its side of `l` (both lie on the ray `AX`).
  --------------------------------------------------------------------

  have hAngleEq :
      Geo.Angle B A X = Geo.Angle B A D :=
    hilbert_angle_eq_of_sameRay_second
      Geo A B X D hRayAXD

  have hRefl :
      Geo.AngleCongruent B A X B A X :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo) B A X hNCBAX

  have hAngleBAX_BAD :
      Geo.AngleCongruent B A X B A D := by
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleEq]
    exact hRefl

  have hRightBAD :
      HilbertRightAngle Geo B A D :=
    hilbert_right_angle_transport
      Geo B A X B A D
      hNCBAX hNCBAD
      hRightBAX hAngleBAX_BAD

  have hArmSwap :
      Geo.AngleCongruent B A D D A B :=
    bookZero_56_ABCequalsCBA
      Geo B A D hNCBAD

  have hRightDAB :
      HilbertRightAngle Geo D A B :=
    hilbert_right_angle_transport
      Geo B A D D A B
      hNCBAD hNCDAB
      hRightBAD hArmSwap

  rcases HilbertPlaneIncidence.line_through A X hAX with
    ⟨lineAX, hAlineAX, hXlineAX⟩

  have hBlineAX : Not (HilbertIncidence.OnLine B lineAX) := by
    intro hBlineAX
    exact hNCBAX ⟨lineAX, hBlineAX, hAlineAX, hXlineAX⟩

  have hSameSideXD :
      HilbertSameSide Geo X D l :=
    hilbert_sameRay_points_sameSide
      Geo A X X D B lineAX l
      hAlineAX hXlineAX hAl hBl hBlineAX
      (hilbert_sameRay_refl Geo A X hAX.symm)
      hRayAXD

  have hOppositeDR :
      HilbertOppositeSide Geo D R l := by
    have hOppositeRX' :
        HilbertOppositeSide Geo R X l :=
      hilbert_oppositeSide_symm
        Geo X R l hOppositeXR
    have hOppositeRD :
        HilbertOppositeSide Geo R D l :=
      hilbert_oppositeSide_transport_right
        Geo R X D l hOppositeRX' hSameSideXD
    exact
      hilbert_oppositeSide_symm
        Geo R D l hOppositeRD

  exact ⟨D, hNCABD, hRightDAB, hCongAD, hOppositeDR⟩

/--
Euclid I.46, on a prescribed side.

On a given segment `AB` and a point `R` off the line `AB`, there is a
square `A B C D` with `C, D` on the side of `AB` opposite `R`.
-/
theorem hilbert_square_exists_opposite_side
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B R : Geo.Point)
    (l : Geo.Line)
    (hAB : A ≠ B)
    (hAl : HilbertIncidence.OnLine A l)
    (hBl : HilbertIncidence.OnLine B l)
    (hRl : Not (HilbertIncidence.OnLine R l)) :
    ∃ C D : Geo.Point,
      IsSquare Geo A B C D ∧
      HilbertOppositeSide Geo D R l ∧
      HilbertOppositeSide Geo C R l := by

  --------------------------------------------------------------------
  -- Steps 1-2 (I.11, I.3): the perpendicular side `AD` at `A`, on the
  -- side of `l` opposite `R`.
  --------------------------------------------------------------------

  rcases
      hilbert_erect_equal_perpendicular_opposite_side
        Geo A B R l hAB hAl hBl hRl with
    ⟨D, hNCABD, hRightDAB, hCongAD_AB, hOppositeDR⟩

  --------------------------------------------------------------------
  -- Step 3 (I.31): complete the parallelogram.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo A B D hNCABD with
    ⟨C, hParallelogram⟩

  --------------------------------------------------------------------
  -- Step 4 (I.34): all four sides are congruent to `AB`.
  --------------------------------------------------------------------

  have hI34 :=
    euclid_proposition_34
      Geo A B C D hParallelogram

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    hI34.1

  have hCongDA_AB :
      Geo.Congruent D A A B :=
    CongruentReverseFirst
      Geo A D A B hCongAD_AB

  have hCongBC_AB :
      Geo.Congruent B C A B :=
    hilbert_congruent_transitivity
      Geo B C D A A B
      hSides.2
      hCongDA_AB

  have hCongAB_BC :
      Geo.Congruent A B B C :=
    hilbert_congruent_symmetry
      Geo B C A B hCongBC_AB

  have hCongBC_CD :
      Geo.Congruent B C C D :=
    hilbert_congruent_transitivity
      Geo B C A B C D
      hCongBC_AB
      hSides.1

  have hCongCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hSides.1

  have hCongAB_DA :
      Geo.Congruent A B D A :=
    hilbert_congruent_symmetry
      Geo D A A B hCongDA_AB

  have hCongCD_DA :
      Geo.Congruent C D D A :=
    hilbert_congruent_transitivity
      Geo C D A B D A
      hCongCD_AB
      hCongAB_DA

  --------------------------------------------------------------------
  -- Step 5 (I.29 and I.34): all four angles are right.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hParallelogram

  have hRightABC :
    HilbertRightAngle Geo A B C :=
  parallelogram_adjacent_right_angle
    Geo A B C D hParallelogram hRightDAB

  have hOppositeAngles :
      OppositeAnglesCongruent Geo A B C D :=
    hI34.2

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    hilbert_right_angle_transport
      Geo D A B B C D
      hNC.1 hNC.2.2.1
      hRightDAB hOppositeAngles.1

  have hRightCDA :
      HilbertRightAngle Geo C D A :=
    hilbert_right_angle_transport
      Geo A B C C D A
      hNC.2.1 hNC.2.2.2
      hRightABC hOppositeAngles.2

  --------------------------------------------------------------------
  -- `C` lies on the same side of `l` as `D` (opposite sides of a
  -- parallelogram are on the same side of each other).
  --------------------------------------------------------------------

  have hParallelCDAB :
      Geo.Parallel C D A B :=
    ParallelSymmetry
      Geo A B C D hParallelogram.1

  rcases
      parallel_endpoints_sameSide
        Geo C D A B hParallelCDAB with
    ⟨l', hAl', hBl', hSameSideCD'⟩

  have hLineEq : l' = l :=
    HilbertPlaneIncidence.line_unique
      A B hAB l' l hAl' hBl' hAl hBl

  have hSameSideCD :
      HilbertSameSide Geo C D l :=
    hLineEq ▸ hSameSideCD'

  have hOppositeCR :
      HilbertOppositeSide Geo C R l := by
    have hOppositeRD :
        HilbertOppositeSide Geo R D l :=
      hilbert_oppositeSide_symm
        Geo D R l hOppositeDR
    have hSameSideDC :
        HilbertSameSide Geo D C l :=
      hilbert_sameSide_symm
        Geo C D l hSameSideCD
    have hOppositeRC :
        HilbertOppositeSide Geo R C l :=
      hilbert_oppositeSide_transport_right
        Geo R D C l hOppositeRD hSameSideDC
    exact
      hilbert_oppositeSide_symm
        Geo R C l hOppositeRC

  exact
    ⟨C, D,
      ⟨hParallelogram,
        hCongAB_BC, hCongBC_CD, hCongCD_DA,
        hRightDAB, hRightABC, hRightBCD, hRightCDA⟩,
      hOppositeDR, hOppositeCR⟩


/--
The three squares of the I.47 diagram, constructed outward from the
triangle.

The square on each side is chosen on the side of its supporting line
opposite to the remaining vertex of the triangle.
-/
theorem i47_outward_squares
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C)) :
    ∃ lBC lAB lAC : Geo.Line,
    ∃ D E F G H K : Geo.Point,
      HilbertIncidence.OnLine B lBC ∧
      HilbertIncidence.OnLine C lBC ∧
      HilbertIncidence.OnLine A lAB ∧
      HilbertIncidence.OnLine B lAB ∧
      HilbertIncidence.OnLine A lAC ∧
      HilbertIncidence.OnLine C lAC ∧
      IsSquare Geo B C E D ∧
      IsSquare Geo A B F G ∧
      IsSquare Geo A C K H ∧
      HilbertOppositeSide Geo D A lBC ∧
      HilbertOppositeSide Geo E A lBC ∧
      HilbertOppositeSide Geo G C lAB ∧
      HilbertOppositeSide Geo F C lAB ∧
      HilbertOppositeSide Geo H B lAC ∧
      HilbertOppositeSide Geo K B lAC := by

  --------------------------------------------------------------------
  -- Nondegeneracy of the three sides.
  --------------------------------------------------------------------

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate Geo A C B h)

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle Geo B C A h))

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  --------------------------------------------------------------------
  -- Square on BC, opposite A.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through B C hBC with
    ⟨lBC, hBlBC, hClBC⟩

  have hAoffBC :
      Not (HilbertIncidence.OnLine A lBC) := by
    intro hAlBC
    exact
      hBCA
        ⟨lBC, hBlBC, hClBC, hAlBC⟩

  rcases
      hilbert_square_exists_opposite_side
        Geo B C A lBC
        hBC hBlBC hClBC hAoffBC with
    ⟨E, D, hSqBC, hOppDA, hOppEA⟩

  --------------------------------------------------------------------
  -- Square on AB, opposite C.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through A B hAB with
    ⟨lAB, hAlAB, hBlAB⟩

  have hCoffAB :
      Not (HilbertIncidence.OnLine C lAB) := by
    intro hClAB
    exact
      hABC
        ⟨lAB, hAlAB, hBlAB, hClAB⟩

  rcases
      hilbert_square_exists_opposite_side
        Geo A B C lAB
        hAB hAlAB hBlAB hCoffAB with
    ⟨F, G, hSqAB, hOppGC, hOppFC⟩

  --------------------------------------------------------------------
  -- Square on AC, opposite B.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through A C hAC with
    ⟨lAC, hAlAC, hClAC⟩

  have hBoffAC :
      Not (HilbertIncidence.OnLine B lAC) := by
    intro hBlAC
    exact
      hACB
        ⟨lAC, hAlAC, hClAC, hBlAC⟩

  rcases
      hilbert_square_exists_opposite_side
        Geo A C B lAC
        hAC hAlAC hClAC hBoffAC with
    ⟨K, H, hSqAC, hOppHB, hOppKB⟩

  exact
    ⟨lBC, lAB, lAC,
      D, E, F, G, H, K,
      hBlBC, hClBC,
      hAlAB, hBlAB,
      hAlAC, hClAC,
      hSqBC, hSqAB, hSqAC,
      hOppDA, hOppEA,
      hOppGC, hOppFC,
      hOppHB, hOppKB⟩

/--
If two right-angle rays based at O lie on opposite sides of the
supporting line OB, then they are opposite rays: P-O-Q.
-/
theorem i47_opposite_right_rays_straight
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P O B Q : Geo.Point)
    (base : Geo.Line)
    (hOB : O ≠ B)
    (hOl : HilbertIncidence.OnLine O base)
    (hBl : HilbertIncidence.OnLine B base)
    (hOpp : HilbertOppositeSide Geo P Q base)
    (hRightP : HilbertRightAngle Geo P O B)
    (hRightQ : HilbertRightAngle Geo B O Q) :
    Geo.Between P O Q := by

  have hPO : P ≠ O := by
    intro h
    subst P
    exact hOpp.1 hOl

  --------------------------------------------------------------------
  -- Extend PO through O.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension P O hPO with
    ⟨E, hPOE⟩

  --------------------------------------------------------------------
  -- The two right angles are genuine.
  --------------------------------------------------------------------

  have hOBP :
      Not (Collinear Geo O B P) :=
    hilbert_not_collinear_of_off_line
      Geo O B P base
      hOB hOl hBl hOpp.1

  have hPOB :
      Not (Collinear Geo P O B) := by
    intro h
    exact
      hOBP
        (PrimCollinearCycle Geo P O B h)

  have hOBQ :
      Not (Collinear Geo O B Q) :=
    hilbert_not_collinear_of_off_line
      Geo O B Q base
      hOB hOl hBl hOpp.2.1

  have hBOQ :
      Not (Collinear Geo B O Q) := by
    intro h
    exact
      hOBQ
        (PrimCollinearSwap Geo B O Q h)

  --------------------------------------------------------------------
  -- BOQ and POB are both right, hence congruent.
  --------------------------------------------------------------------

  have hRightCong :
      Geo.AngleCongruent B O Q P O B :=
    hilbert_all_right_angles_congruent
      Geo
      B O Q
      P O B
      hBOQ hPOB
      hRightQ hRightP

  --------------------------------------------------------------------
  -- Since P-O-E, POB is congruent to BOE.
  --------------------------------------------------------------------

  have hOppExtension :
      Geo.AngleCongruent P O B B O E :=
    hilbert_right_angle_opposite_extension
      Geo
      P O B E
      hPOB
      hRightP
      hPOE

  have hBOQ_BOE :
      Geo.AngleCongruent B O Q B O E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O Q
      P O B
      B O E
      hRightCong
      hOppExtension

  --------------------------------------------------------------------
  -- This is exactly the synthetic "two right angles" hypothesis of I.14.
  --------------------------------------------------------------------

  have hTwoRight :
      HilbertAnglesEqualTwoRightAngles
        Geo B O P Q :=
    ⟨E, hPOE, hBOQ_BOE⟩

  exact
    euclid_proposition_14
      Geo
      B O P Q
      base
      hOB.symm
      hBl
      hOl
      hOpp
      hTwoRight

/--
In the I.47 configuration, the outward square on AB extends the
right-angle side AC through A: G-A-C.
-/
theorem i47_square_AB_extension
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C F G : Geo.Point)
    (base : Geo.Line)
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hSquare : IsSquare Geo A B F G)
    (hOppGC : HilbertOppositeSide Geo G C base)
    (hRight : HilbertRightAngle Geo B A C) :
    Geo.Between G A C := by

  have hRightGAB :
      HilbertRightAngle Geo G A B :=
    hSquare.2.2.2.2.1

  exact
    i47_opposite_right_rays_straight
      Geo
      G A B C
      base
      hAB
      hAbase
      hBbase
      hOppGC
      hRightGAB
      hRight

/--
In the I.47 configuration, the outward square on AC extends the
right-angle side AB through A: H-A-B.
-/
theorem i47_square_AC_extension
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C K H : Geo.Point)
    (base : Geo.Line)
    (hAC : A ≠ C)
    (hAbase : HilbertIncidence.OnLine A base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hABC : Not (Collinear Geo A B C))
    (hSquare : IsSquare Geo A C K H)
    (hOppHB : HilbertOppositeSide Geo H B base)
    (hRight : HilbertRightAngle Geo B A C) :
    Geo.Between H A B := by

  have hRightHAC :
      HilbertRightAngle Geo H A C :=
    hSquare.2.2.2.2.1

  have hBAC :
      Not (Collinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap Geo B A C h)

  have hCAB :
      Not (Collinear Geo C A B) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle Geo C A B h)

  have hArmSwap :
      Geo.AngleCongruent B A C C A B :=
    bookZero_56_ABCequalsCBA
      Geo B A C hBAC

  have hRightCAB :
      HilbertRightAngle Geo C A B :=
    hilbert_right_angle_transport
      Geo
      B A C
      C A B
      hBAC
      hCAB
      hRight
      hArmSwap

  exact
    i47_opposite_right_rays_straight
      Geo
      H A C B
      base
      hAC
      hAbase
      hCbase
      hOppHB
      hRightHAC
      hRightCAB

/--
In the I.47 configuration, the side BF of the square on AB is
parallel to AC, because G-A-C and BF || GA.
-/
theorem i47_square_AB_parallel_AC
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C F G : Geo.Point)
    (hAC : A ≠ C)
    (hSquare : IsSquare Geo A B F G)
    (hGAC : Geo.Between G A C) :
    Geo.Parallel A C B F := by

  have hBF_GA :
      Geo.Parallel B F G A :=
    hSquare.1.2

  have hGA_BF :
      Geo.Parallel G A B F :=
    ParallelSymmetry
      Geo B F G A hBF_GA

  have hGACcol :
      Collinear Geo G A C :=
    (HilbertOrder.between_incidence
      G A C hGAC).2.2.2.1

  have hCGA :
      Collinear Geo C G A :=
    PrimCollinearCycle
      Geo A C G
      (PrimCollinearCycle
        Geo G A C hGACcol)

  have hCA_BF :
      Geo.Parallel C A B F :=
    ParallelCollinearLeft
      Geo
      G A C
      B F
      hAC.symm
      hGA_BF
      hCGA

  exact
    ParallelSwapFirstLine
      Geo C A B F hCA_BF

/--
In the I.47 configuration, the side CK of the square on AC is
parallel to AB, because H-A-B and CK || HA.
-/
theorem i47_square_AC_parallel_AB
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C K H : Geo.Point)
    (hAB : A ≠ B)
    (hSquare : IsSquare Geo A C K H)
    (hHAB : Geo.Between H A B) :
    Geo.Parallel A B C K := by

  have hCK_HA :
      Geo.Parallel C K H A :=
    hSquare.1.2

  have hHA_CK :
      Geo.Parallel H A C K :=
    ParallelSymmetry
      Geo C K H A hCK_HA

  have hHABcol :
      Collinear Geo H A B :=
    (HilbertOrder.between_incidence
      H A B hHAB).2.2.2.1

  have hBHA :
      Collinear Geo B H A :=
    PrimCollinearCycle
      Geo A B H
      (PrimCollinearCycle
        Geo H A B hHABcol)

  have hBA_CK :
      Geo.Parallel B A C K :=
    ParallelCollinearLeft
      Geo
      H A B
      C K
      hAB.symm
      hHA_CK
      hBHA

  exact
    ParallelSwapFirstLine
      Geo B A C K hBA_CK

/--
A nondegenerate triangle cannot have right angles at both A and B.

This is the synthetic I.17 contradiction: BAC + ABC is strictly less
than two right angles, while if both are right then the supplementary
angle to ABC is congruent to BAC.
-/
theorem i47_two_right_angles_impossible
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hRightA : HilbertRightAngle Geo B A C)
    (hRightB : HilbertRightAngle Geo A B C) :
    False := by

  --------------------------------------------------------------------
  -- I.17: angle BAC + angle ABC is less than two right angles.
  --
  -- Thus there is E with C-B-E and
  --
  --     angle BAC < angle ABE.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_17_BAC_ABC
        Geo A B C hABC with
    ⟨E, hCBE, hLess⟩

  have hBAC :
      Not (Collinear Geo B A C) :=
    hLess.1

  have hABE :
      Not (Collinear Geo A B E) :=
    hLess.2.1

  --------------------------------------------------------------------
  -- Reverse the arms of the right angle ABC:
  --
  --     ABC right  ->  CBA right.
  --------------------------------------------------------------------

  have hCBA :
      Not (Collinear Geo C B A) := by
    intro h
    exact
      hABC
        (PrimCollinearSymm Geo C B A h)

  have hABC_CBA :
      Geo.AngleCongruent A B C C B A :=
    bookZero_56_ABCequalsCBA
      Geo A B C hABC

  have hRightCBA :
      HilbertRightAngle Geo C B A :=
    hilbert_right_angle_transport
      Geo
      A B C
      C B A
      hABC
      hCBA
      hRightB
      hABC_CBA

  --------------------------------------------------------------------
  -- Since C-B-E, ABE is the adjacent right angle to CBA.
  --------------------------------------------------------------------

  have hCBA_ABE :
      Geo.AngleCongruent C B A A B E :=
    hilbert_right_angle_opposite_extension
      Geo
      C B A E
      hCBA
      hRightCBA
      hCBE

  have hRightABE :
      HilbertRightAngle Geo A B E :=
    hilbert_right_angle_transport
      Geo
      C B A
      A B E
      hCBA
      hABE
      hRightCBA
      hCBA_ABE

  --------------------------------------------------------------------
  -- ABE and BAC are both right, hence congruent.
  --------------------------------------------------------------------

  have hABE_BAC :
      Geo.AngleCongruent A B E B A C :=
    hilbert_all_right_angles_congruent
      Geo
      A B E
      B A C
      hABE
      hBAC
      hRightABE
      hRightA

  --------------------------------------------------------------------
  -- I.17 gave BAC < ABE.  Replace ABE by the congruent right
  -- angle BAC and obtain BAC < BAC.
  --------------------------------------------------------------------

  have hSelf :
      HilbertAngleLess Geo B A C B A C :=
    hilbert_angleLess_transport_right
      Geo
      B A C
      A B E
      B A C
      hLess
      hBAC
      hABE_BAC

  exact
    (hilbert_angleLess_irrefl
      Geo B A C)
      hSelf

/--
In the outward I.47 configuration, C,A,E are noncollinear.

Otherwise the opposite-side condition forces E-C-A.  The right angle
BCE of the square on BC then becomes a right angle of triangle ABC at C.
Together with the given right angle at A this contradicts I.17.
-/
theorem i47_noncollinear_CAE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hRightA : HilbertRightAngle Geo B A C)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSquare : IsSquare Geo B C E D)
    (hOppEA : HilbertOppositeSide Geo E A base) :
    Not (Collinear Geo C A E) := by

  intro hCAE

  --------------------------------------------------------------------
  -- CAE has a carrier line.
  --------------------------------------------------------------------

  rcases hCAE with
    ⟨lineCAE, hCcae, hAcae, hEcae⟩

  --------------------------------------------------------------------
  -- E and A are on opposite sides of BC, hence EA crosses base.
  --------------------------------------------------------------------

  rcases hOppEA.2.2 with
    ⟨X, hEXA, hXbase⟩

  have hXcae :
      HilbertIncidence.OnLine X lineCAE :=
    hilbert_between_on_line
      Geo
      E X A
      lineCAE
      hEcae
      hAcae
      hEXA

  --------------------------------------------------------------------
  -- The intersection X must be C.
  --------------------------------------------------------------------

  have hXC : X = C := by
    by_contra hXC

    have hLines :
        lineCAE = base :=
      HilbertPlaneIncidence.line_unique
        X C hXC
        lineCAE base
        hXcae hCcae
        hXbase hCbase

    exact
      hOppEA.1
        (hLines ▸ hEcae)

  have hECA :
      Geo.Between E C A := by
    simpa [hXC] using hEXA

  --------------------------------------------------------------------
  -- The square BCE D has right angle BCE.
  --------------------------------------------------------------------

  have hNCBCE :
      Not (Collinear Geo B C E) :=
    (parallelogram_vertices_noncollinear
      Geo B C E D hSquare.1).2.1

  have hRightBCE :
      HilbertRightAngle Geo B C E :=
    hSquare.2.2.2.2.2.1

  --------------------------------------------------------------------
  -- Reverse the arms: BCE right -> ECB right.
  --------------------------------------------------------------------

  have hNCECB :
      Not (Collinear Geo E C B) := by
    intro h
    exact
      hNCBCE
        (PrimCollinearSymm Geo E C B h)

  have hBCE_ECB :
      Geo.AngleCongruent B C E E C B :=
    bookZero_56_ABCequalsCBA
      Geo B C E hNCBCE

  have hRightECB :
      HilbertRightAngle Geo E C B :=
    hilbert_right_angle_transport
      Geo
      B C E
      E C B
      hNCBCE
      hNCECB
      hRightBCE
      hBCE_ECB

  --------------------------------------------------------------------
  -- Since E-C-A, the opposite ray CA gives another right angle BCA.
  --------------------------------------------------------------------

  have hECB_BCA :
      Geo.AngleCongruent E C B B C A :=
    hilbert_right_angle_opposite_extension
      Geo
      E C B A
      hNCECB
      hRightECB
      hECA

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle Geo B C A h))

  have hRightBCA :
      HilbertRightAngle Geo B C A :=
    hilbert_right_angle_transport
      Geo
      E C B
      B C A
      hNCECB
      hBCA
      hRightECB
      hECB_BCA

  --------------------------------------------------------------------
  -- Reverse BCA to ACB.
  --------------------------------------------------------------------

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate Geo A C B h)

  have hBCA_ACB :
      Geo.AngleCongruent B C A A C B :=
    bookZero_56_ABCequalsCBA
      Geo B C A hBCA

  have hRightACB :
      HilbertRightAngle Geo A C B :=
    hilbert_right_angle_transport
      Geo
      B C A
      A C B
      hBCA
      hACB
      hRightBCA
      hBCA_ACB

  --------------------------------------------------------------------
  -- Reverse the given right angle BAC to CAB.
  --------------------------------------------------------------------

  have hBAC :
      Not (Collinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap Geo B A C h)

  have hCAB :
      Not (Collinear Geo C A B) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle Geo C A B h)

  have hBAC_CAB :
      Geo.AngleCongruent B A C C A B :=
    bookZero_56_ABCequalsCBA
      Geo B A C hBAC

  have hRightCAB :
      HilbertRightAngle Geo C A B :=
    hilbert_right_angle_transport
      Geo
      B A C
      C A B
      hBAC
      hCAB
      hRightA
      hBAC_CAB

  --------------------------------------------------------------------
  -- Triangle ACB would have two right angles, at A and C.
  --------------------------------------------------------------------

  exact
    i47_two_right_angles_impossible
      Geo
      A C B
      hACB
      hRightCAB
      hRightACB

/--
The two remaining noncollinearity facts needed in the I.47 angle step
follow immediately from the leg-square parallels.
-/
theorem i47_parallel_noncollinearities
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C F K : Geo.Point)
    (hAC_BF : Geo.Parallel A C B F)
    (hAB_CK : Geo.Parallel A B C K) :
    Not (Collinear Geo B F C) ∧
    Not (Collinear Geo C K B) := by

  --------------------------------------------------------------------
  -- BF || CA
  --------------------------------------------------------------------

  have hBF_AC :
      Geo.Parallel B F A C :=
    ParallelSymmetry
      Geo A C B F hAC_BF

  have hBF_CA :
      Geo.Parallel B F C A :=
    ParallelSwapSecondLine
      Geo B F A C hBF_AC

  have hBFC :
      Not (Collinear Geo B F C) :=
    parallel_first_not_collinear
      Geo B F C A hBF_CA

  --------------------------------------------------------------------
  -- CK || BA
  --------------------------------------------------------------------

  have hCK_AB :
      Geo.Parallel C K A B :=
    ParallelSymmetry
      Geo A B C K hAB_CK

  have hCK_BA :
      Geo.Parallel C K B A :=
    ParallelSwapSecondLine
      Geo C K A B hCK_AB

  have hCKB :
      Not (Collinear Geo C K B) :=
    parallel_first_not_collinear
      Geo C K B A hCK_BA

  exact ⟨hBFC, hCKB⟩

/--
Euclid I.47 angle step at B:

    angle ABD ~= angle FBC.

The proof adds equal angles:
    DBC ~= FBA      (both right),
    CBA ~= ABC      (same unordered angle).
-/
theorem i47_angle_ABD_FBC
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F G : Geo.Point)
    (lBC lAB : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hBlBC : HilbertIncidence.OnLine B lBC)
    (hClBC : HilbertIncidence.OnLine C lBC)
    (hAlAB : HilbertIncidence.OnLine A lAB)
    (hBlAB : HilbertIncidence.OnLine B lAB)
    (hSquareBC : IsSquare Geo B C E D)
    (hSquareAB : IsSquare Geo A B F G)
    (hOppDA : HilbertOppositeSide Geo D A lBC)
    (hOppFC : HilbertOppositeSide Geo F C lAB)
    (hNCBAD : Not (Collinear Geo B A D))
    (hNCBFC : Not (Collinear Geo B F C)) :
    Geo.AngleCongruent A B D F B C := by

  --------------------------------------------------------------------
  -- Nondegenerate reference rays BC and BA.
  --------------------------------------------------------------------

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hBA : B ≠ A :=
    hAB.symm

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle Geo B C A h))

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  --------------------------------------------------------------------
  -- Outer angles DBA and FBC are genuine.
  --------------------------------------------------------------------

  have hDBA :
      Not (Collinear Geo D B A) := by
    intro h
    exact
      hNCBAD
        (PrimCollinearCycle Geo D B A h)

  have hFBC :
      Not (Collinear Geo F B C) := by
    intro h
    exact
      hNCBFC
        (PrimCollinearSwap Geo F B C h)

  --------------------------------------------------------------------
  -- Component 1:
  --
  -- DBC ~= FBA, since both are right angles.
  --------------------------------------------------------------------

  have hNCBC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hSquareBC.1

  have hDBC :
      Not (Collinear Geo D B C) :=
    hNCBC.1

  have hRightDBC :
      HilbertRightAngle Geo D B C :=
    hSquareBC.2.2.2.2.1

  have hNCAB :=
    parallelogram_vertices_noncollinear
      Geo A B F G hSquareAB.1

  have hABF :
      Not (Collinear Geo A B F) :=
    hNCAB.2.1

  have hRightABF :
      HilbertRightAngle Geo A B F :=
    hSquareAB.2.2.2.2.2.1

  have hDBC_ABF :
      Geo.AngleCongruent D B C A B F :=
    hilbert_all_right_angles_congruent
      Geo
      D B C
      A B F
      hDBC
      hABF
      hRightDBC
      hRightABF

  have hDBC_FBA :
      Geo.AngleCongruent D B C F B A :=
    (Geo.angle_congruent_reverse_second
      D B C
      A B F).mp hDBC_ABF

  --------------------------------------------------------------------
  -- Component 2:
  --
  -- CBA ~= ABC.
  --------------------------------------------------------------------

  have hCBA :
      Not (Collinear Geo C B A) := by
    intro h
    exact
      hABC
        (PrimCollinearSymm Geo C B A h)

  have hCBA_ABC :
      Geo.AngleCongruent C B A A B C :=
    bookZero_56_ABCequalsCBA
      Geo C B A hCBA

  --------------------------------------------------------------------
  -- In the first sum D and A are on opposite sides of BC.
  -- In the second sum F and C are on opposite sides of AB.
  --
  -- Hence the two angle-addition configurations have the same
  -- side pattern: both are the opposite-side case.
  --------------------------------------------------------------------

  have hNotSameDA :
      Not (HilbertSameSide Geo D A lBC) := by
    intro hSame
    exact
      (hilbert_oppositeSide_not_sameSide
        Geo D A lBC hOppDA)
        hSame

  have hNotSameFC :
      Not (HilbertSameSide Geo F C lAB) := by
    intro hSame
    exact
      (hilbert_oppositeSide_not_sameSide
        Geo F C lAB hOppFC)
        hSame

  have hSideConfiguration :
      HilbertSameSide Geo D A lBC ↔
      HilbertSameSide Geo F C lAB := by
    constructor
    · intro hSame
      exact False.elim (hNotSameDA hSame)
    · intro hSame
      exact False.elim (hNotSameFC hSame)

  --------------------------------------------------------------------
  -- Hilbert Theorem 15:
  --
  --     DBA ~= FBC.
  --------------------------------------------------------------------

  have hDBA_FBC :
      Geo.AngleCongruent D B A F B C :=
    hilbert_angle_addition
      Geo
      D B C A
      F B A C
      lBC lAB
      hBC
      hBA
      hBlBC
      hClBC
      hBlAB
      hAlAB
      hOppDA.1
      hOppDA.2.1
      hOppFC.1
      hOppFC.2.1
      hSideConfiguration
      hDBA
      hFBC
      hDBC_FBA
      hCBA_ABC

  --------------------------------------------------------------------
  -- Normalize DBA to the requested ABD.
  --------------------------------------------------------------------

  exact
    (Geo.angle_congruent_reverse_first
      D B A
      F B C).mp hDBA_FBC

/--
Euclid I.47 angle step at C:

    angle ACE ~= angle KCB.

The proof adds equal angles:
    ACB ~= BCA      (same unordered angle),
    BCE ~= ACK      (both right).
-/
theorem i47_angle_ACE_KCB
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E K H : Geo.Point)
    (lBC lAC : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hBlBC : HilbertIncidence.OnLine B lBC)
    (hClBC : HilbertIncidence.OnLine C lBC)
    (hAlAC : HilbertIncidence.OnLine A lAC)
    (hClAC : HilbertIncidence.OnLine C lAC)
    (hSquareBC : IsSquare Geo B C E D)
    (hSquareAC : IsSquare Geo A C K H)
    (hOppEA : HilbertOppositeSide Geo E A lBC)
    (hOppKB : HilbertOppositeSide Geo K B lAC)
    (hNCCAE : Not (Collinear Geo C A E))
    (hNCCKB : Not (Collinear Geo C K B)) :
    Geo.AngleCongruent A C E K C B := by

  --------------------------------------------------------------------
  -- Nondegenerate reference ray CB.
  --------------------------------------------------------------------

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle
            Geo B C A h))

  have hCBA :
      Not (Collinear Geo C B A) := by
    intro h
    exact
      hBCA
        (PrimCollinearSwap
          Geo C B A h)

  have hCB : C ≠ B :=
    hilbert_noncollinear_ne_first
      Geo C B A hCBA

  --------------------------------------------------------------------
  -- Nondegenerate reference ray CA.
  --------------------------------------------------------------------

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  have hCA : C ≠ A :=
    hAC.symm

  --------------------------------------------------------------------
  -- Outer angle ACE is genuine.
  --------------------------------------------------------------------

  have hACE :
      Not (Collinear Geo A C E) := by
    intro h
    exact
      hNCCAE
        (PrimCollinearSwap
          Geo A C E h)

  --------------------------------------------------------------------
  -- Outer angle BCK is genuine.
  --------------------------------------------------------------------

  have hBCK :
      Not (Collinear Geo B C K) := by
    intro h
    exact
      hNCCKB
        (PrimCollinearCycle
          Geo B C K h)

  --------------------------------------------------------------------
  -- Component 1:
  --
  -- ACB ~= BCA.
  --------------------------------------------------------------------

  have hACB_BCA :
      Geo.AngleCongruent A C B B C A :=
    bookZero_56_ABCequalsCBA
      Geo A C B hACB

  --------------------------------------------------------------------
  -- Component 2:
  --
  -- BCE ~= ACK, since both are right angles.
  --------------------------------------------------------------------

  have hNCBC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hSquareBC.1

  have hBCE :
      Not (Collinear Geo B C E) :=
    hNCBC.2.1

  have hRightBCE :
      HilbertRightAngle Geo B C E :=
    hSquareBC.2.2.2.2.2.1

  have hNCAC :=
    parallelogram_vertices_noncollinear
      Geo A C K H hSquareAC.1

  have hACK :
      Not (Collinear Geo A C K) :=
    hNCAC.2.1

  have hRightACK :
      HilbertRightAngle Geo A C K :=
    hSquareAC.2.2.2.2.2.1

  have hBCE_ACK :
      Geo.AngleCongruent B C E A C K :=
    hilbert_all_right_angles_congruent
      Geo
      B C E
      A C K
      hBCE
      hACK
      hRightBCE
      hRightACK

  --------------------------------------------------------------------
  -- Both angle-addition configurations are opposite-side cases:
  --
  -- A,E are opposite across BC,
  -- B,K are opposite across AC.
  --------------------------------------------------------------------

  have hNotSameAE :
      Not (HilbertSameSide Geo A E lBC) := by
    intro hSameAE

    have hSameEA :
        HilbertSameSide Geo E A lBC :=
      hilbert_sameSide_symm
        Geo A E lBC hSameAE

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo E A lBC hOppEA)
        hSameEA

  have hOppBK :
      HilbertOppositeSide Geo B K lAC :=
    hilbert_oppositeSide_symm
      Geo K B lAC hOppKB

  have hNotSameBK :
      Not (HilbertSameSide Geo B K lAC) := by
    intro hSameBK

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo B K lAC hOppBK)
        hSameBK

  have hSideConfiguration :
      HilbertSameSide Geo A E lBC ↔
      HilbertSameSide Geo B K lAC := by
    constructor

    · intro hSameAE
      exact
        False.elim
          (hNotSameAE hSameAE)

    · intro hSameBK
      exact
        False.elim
          (hNotSameBK hSameBK)

  --------------------------------------------------------------------
  -- Hilbert Theorem 15:
  --
  --     ACE ~= BCK.
  --------------------------------------------------------------------

  have hACE_BCK :
      Geo.AngleCongruent A C E B C K :=
    hilbert_angle_addition
      Geo
      A C B E
      B C A K
      lBC lAC
      hCB
      hCA
      hClBC
      hBlBC
      hClAC
      hAlAC
      hOppEA.2.1
      hOppEA.1
      hOppKB.2.1
      hOppKB.1
      hSideConfiguration
      hACE
      hBCK
      hACB_BCA
      hBCE_ACK

  --------------------------------------------------------------------
  -- Normalize BCK to KCB.
  --------------------------------------------------------------------

  exact
    (Geo.angle_congruent_reverse_second
      A C E
      B C K).mp hACE_BCK


/--
Local axiom: Euclid's figure for I.47.

Given a triangle `A B C` with a right angle at `A`, the whole
Pythagoras diagram exists:

* `B C E D`, `A B F G`, `A C K H` are the three squares on the sides,
  placed outward -- this is I.46 together with the choice of side that
  `euclid_proposition_46` does not yet make;
* `M` lies on `BC` and `L` on `DE`, `AL` being the parallel to `BD`
  through `A` [I.31], so that `L D B M` and `C E L M` are the two
  rectangles into which `ML` divides the big square [I.34];
* `N` is the point where the diagonal `DC` of the big square meets the
  cut `ML` (Pasch);
* `A C ∥ B F` and `A B ∥ C K`, which is Euclid's step "CA is in a
  straight line with AG" [I.14] combined with the parallel sides of
  the squares;
* `∠ABD ≅ ∠FBC` and `∠ACE ≅ ∠KCB`, Euclid's step "let the angle ABC be
  added to each" -- Post. 4 (all right angles are congruent, proved in
  `Hilbert48_test.lean` but not exported) followed by angle addition,
  whose crossbar hypotheses are read off the figure;
* the four triangles used in the two SAS steps are nondegenerate.
-/
axiom i47_diagram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hRight : HilbertRightAngle Geo B A C) :
    ∃ D E F G H K L M N : Geo.Point,
      IsSquare Geo B C E D ∧
      IsSquare Geo A B F G ∧
      IsSquare Geo A C K H ∧
      Geo.Between B M C ∧
      Geo.Between D L E ∧
      Geo.Between D N C ∧
      Geo.Between M N L ∧
      IsParallelogram Geo L D B M ∧
      IsParallelogram Geo C E L M ∧
      Geo.Parallel L A D B ∧
      Geo.Parallel M A C E ∧
      Geo.Parallel A C B F ∧
      Geo.Parallel A B C K ∧
      Geo.AngleCongruent A B D F B C ∧
      Geo.AngleCongruent A C E K C B ∧
      Not (Collinear Geo B A D) ∧
      Not (Collinear Geo B F C) ∧
      Not (Collinear Geo C A E) ∧
      Not (Collinear Geo C K B)

------------------------------------------------------------------------
-- Euclid I.47
------------------------------------------------------------------------

/--
Euclid, Elements, Book I, Proposition 47.

In a right-angled triangle `A B C`, right-angled at `A`, the square on
the hypotenuse `BC` is equal -- equicomplementable in the scissors
calculus -- to the sum of the squares on the two legs `AB` and `AC`.
-/
theorem euclid_proposition_47
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hRight : HilbertRightAngle Geo B A C) :
    ∃ D E F G H K : Geo.Point,
      IsSquare Geo B C E D ∧
      IsSquare Geo A B F G ∧
      IsSquare Geo A C K H ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo A B F G +
         hilbertParallelogramTerm Geo A C K H) := by

  rcases
      i47_diagram
        Geo A B C hABC hRight with
    ⟨D, E, F, G, H, K, L, M, N,
     hSqBC, hSqAB, hSqAC,
     hBMC, hDLE, hDNC, hMNL,
     hParLDBM, hParCELM,
     hParallelLA, hParallelMA,
     hParallelAC, hParallelAB,
     hAngleB, hAngleC,
     hNCBAD, hNCBFC, hNCCAE, hNCCKB⟩

  refine ⟨D, E, F, G, H, K, hSqBC, hSqAB, hSqAC, ?_⟩

  --------------------------------------------------------------------
  -- Side congruences read off the three squares.
  --------------------------------------------------------------------

  -- `BC ≅ CE ≅ ED ≅ DB`, hence `BD ≅ BC`.
  have hCongBC_ED :
      Geo.Congruent B C E D :=
    hilbert_congruent_transitivity
      Geo B C C E E D
      hSqBC.2.1
      hSqBC.2.2.1

  have hCongBC_DB :
      Geo.Congruent B C D B :=
    hilbert_congruent_transitivity
      Geo B C E D D B
      hCongBC_ED
      hSqBC.2.2.2.1

  have hCongBD_BC :
      Geo.Congruent B D B C :=
    CongruentReverseFirst
      Geo D B B C
      (hilbert_congruent_symmetry
        Geo B C D B hCongBC_DB)

  have hCongCE_CB :
      Geo.Congruent C E C B :=
    (Geometry.Geo.congruent_reverse_second
      Geo C E B C).mp
      (hilbert_congruent_symmetry
        Geo B C C E hSqBC.2.1)

  -- `AB ≅ BF` and `AC ≅ CK`.
  have hCongBA_BF :
      Geo.Congruent B A B F :=
    CongruentReverseFirst
      Geo A B B F hSqAB.2.1

  have hCongCA_CK :
      Geo.Congruent C A C K :=
    CongruentReverseFirst
      Geo A C C K hSqAC.2.1

  --------------------------------------------------------------------
  -- Step 3 [I.4]: the two SAS congruences.
  --------------------------------------------------------------------

  have hSAS1 :
      TriangleCongruenceResult Geo B A D B F C :=
    SAS
      Geo B A D B F C
      hNCBAD
      hNCBFC
      hCongBA_BF
      hAngleB
      hCongBD_BC

  have hSAS2 :
      TriangleCongruenceResult Geo C A E C K B :=
    SAS
      Geo C A E C K B
      hNCCAE
      hNCCKB
      hCongCA_CK
      hAngleC
      hCongCE_CB

  have hScTri1 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B A D)
        (hilbertScissorsTriangle Geo B F C) :=
    scissors_congruent
      Geo B A D B F C hSAS1

  have hScTri2 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo C A E)
        (hilbertScissorsTriangle Geo C K B) :=
    scissors_congruent
      Geo C A E C K B hSAS2

  --------------------------------------------------------------------
  -- Step 4 [I.41]: rectangle `L D B M` and square `A B F G` are both
  -- double the corresponding triangle.
  --------------------------------------------------------------------

  have hI41Rect1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo L D B M)
        (hilbertScissorsTriangle Geo A D B +
         hilbertScissorsTriangle Geo A D B) :=
    euclid_proposition_41
      Geo L D B M A
      hParLDBM
      hParallelLA

  have hParABFG :
      IsParallelogram Geo A B F G :=
    hSqAB.1

  have hI41Square1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B F G)
        (hilbertScissorsTriangle Geo C B F +
         hilbertScissorsTriangle Geo C B F) :=
    euclid_proposition_41
      Geo A B F G C
      hParABFG
      hParallelAC

  --------------------------------------------------------------------
  -- Step 5 [I.41]: the same on the other side.
  --------------------------------------------------------------------

  have hParMCEL :
      IsParallelogram Geo M C E L :=
    ParallelogramRotateOne
      Geo C E L M hParCELM

  have hI41Rect2 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M C E L)
        (hilbertScissorsTriangle Geo A C E +
         hilbertScissorsTriangle Geo A C E) :=
    euclid_proposition_41
      Geo M C E L A
      hParMCEL
      hParallelMA

  have hParACKH :
      IsParallelogram Geo A C K H :=
    hSqAC.1

  have hI41Square2 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A C K H)
        (hilbertScissorsTriangle Geo B C K +
         hilbertScissorsTriangle Geo B C K) :=
    euclid_proposition_41
      Geo A C K H B
      hParACKH
      hParallelAB

  --------------------------------------------------------------------
  -- Renaming of the doubled triangles.  Triangle terms are multisets
  -- of vertices, so these are equalities of terms.
  --------------------------------------------------------------------

  have hNameADB :
      hilbertScissorsTriangle Geo A D B =
      hilbertScissorsTriangle Geo B A D := by
    rw [scissors_triangle_cycle Geo A D B,
        scissors_triangle_cycle Geo D B A]

  have hNameCBF :
      hilbertScissorsTriangle Geo C B F =
      hilbertScissorsTriangle Geo B F C := by
    rw [scissors_triangle_cycle Geo C B F]

  have hNameACE :
      hilbertScissorsTriangle Geo A C E =
      hilbertScissorsTriangle Geo C A E :=
    scissors_triangle_swap12 Geo A C E

  have hNameBCK :
      hilbertScissorsTriangle Geo B C K =
      hilbertScissorsTriangle Geo C K B := by
    rw [scissors_triangle_cycle Geo B C K]

  --------------------------------------------------------------------
  -- Rectangle `L D B M` equals square `A B F G`.
  --------------------------------------------------------------------

  have hDouble1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo B A D +
         hilbertScissorsTriangle Geo B A D)
        (hilbertScissorsTriangle Geo B F C +
         hilbertScissorsTriangle Geo B F C) :=
    equicomplementable_add
      Geo
      (equicomplementable_of_scissorsEq
        Geo hScTri1)
      (equicomplementable_of_scissorsEq
        Geo hScTri1)

  have hRect1Square1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo L D B M)
        (hilbertParallelogramTerm Geo A B F G) := by
    rw [hNameADB] at hI41Rect1
    rw [hNameCBF] at hI41Square1
    exact
      equicomplementable_trans
        Geo
        (equicomplementable_trans
          Geo hI41Rect1 hDouble1)
        (equicomplementable_symm Geo hI41Square1)

  --------------------------------------------------------------------
  -- Rectangle `M C E L` equals square `A C K H`.
  --------------------------------------------------------------------

  have hDouble2 :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo C A E +
         hilbertScissorsTriangle Geo C A E)
        (hilbertScissorsTriangle Geo C K B +
         hilbertScissorsTriangle Geo C K B) :=
    equicomplementable_add
      Geo
      (equicomplementable_of_scissorsEq
        Geo hScTri2)
      (equicomplementable_of_scissorsEq
        Geo hScTri2)

  have hRect2Square2 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M C E L)
        (hilbertParallelogramTerm Geo A C K H) := by
    rw [hNameACE] at hI41Rect2
    rw [hNameBCK] at hI41Square2
    exact
      equicomplementable_trans
        Geo
        (equicomplementable_trans
          Geo hI41Rect2 hDouble2)
        (equicomplementable_symm Geo hI41Square2)

  --------------------------------------------------------------------
  -- Move both rectangles to the vertex order used by the dissection.
  --------------------------------------------------------------------

  have hRotRect1 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo L D B M)
        (hilbertParallelogramTerm Geo M L D B) :=
    parallelogram_term_rotateOne
      Geo L D B M hParLDBM

  have hRotRect2 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo C E L M)
        (hilbertParallelogramTerm Geo M C E L) :=
    parallelogram_term_rotateOne
      Geo C E L M hParCELM

  have hRect1' :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M L D B)
        (hilbertParallelogramTerm Geo A B F G) :=
    equicomplementable_trans
      Geo
      (equicomplementable_of_scissorsEq
        Geo
        (HilbertScissorsEq.symm
          (Geo := Geo) hRotRect1))
      hRect1Square1

  have hRect2' :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C E L M)
        (hilbertParallelogramTerm Geo A C K H) :=
    equicomplementable_trans
      Geo
      (equicomplementable_of_scissorsEq
        Geo hRotRect2)
      hRect2Square2

  --------------------------------------------------------------------
  -- Step 6: the two rectangles make up the whole square on `BC`.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo M L D B +
         hilbertParallelogramTerm Geo C E L M) :=
    i47_square_split
      Geo B C D E L M N
      hSqBC.1
      hBMC hDLE hDNC hMNL

  have hSum :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo M L D B +
         hilbertParallelogramTerm Geo C E L M)
        (hilbertParallelogramTerm Geo A B F G +
         hilbertParallelogramTerm Geo A C K H) :=
    i47_equicomplementable_add
      Geo hRect1' hRect2'

  exact
    equicomplementable_transport
      Geo
      hSplit
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo A B F G +
         hilbertParallelogramTerm Geo A C K H))
      hSum

end Geometry

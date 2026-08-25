import CGJteamLab.Proposition12
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
In the outward I.47 configuration, B,A,D are noncollinear.

Otherwise the opposite-side condition forces D-B-A.  The right angle
DBC of the square on BC would then make ABC right, contradicting the
given right angle BAC via I.17.
-/
theorem i47_noncollinear_BAD
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hRightA : HilbertRightAngle Geo B A C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hSquare : IsSquare Geo B C E D)
    (hOppDA : HilbertOppositeSide Geo D A base) :
    Not (Collinear Geo B A D) := by

  intro hBAD

  rcases hBAD with
    ⟨lineBAD, hBbad, hAbad, hDbad⟩

  rcases hOppDA.2.2 with
    ⟨X, hDXA, hXbase⟩

  have hXbad :
      HilbertIncidence.OnLine X lineBAD :=
    hilbert_between_on_line
      Geo
      D X A
      lineBAD
      hDbad
      hAbad
      hDXA

  have hXB : X = B := by
    by_contra hXB

    have hLines :
        lineBAD = base :=
      HilbertPlaneIncidence.line_unique
        X B hXB
        lineBAD base
        hXbad hBbad
        hXbase hBbase

    exact
      hOppDA.1
        (hLines ▸ hDbad)

  have hDBA :
      Geo.Between D B A := by
    simpa [hXB] using hDXA

  have hNCDBC :
      Not (Collinear Geo D B C) :=
    (parallelogram_vertices_noncollinear
      Geo B C E D hSquare.1).1

  have hRightDBC :
      HilbertRightAngle Geo D B C :=
    hSquare.2.2.2.2.1

  have hDBC_CBA :
      Geo.AngleCongruent D B C C B A :=
    hilbert_right_angle_opposite_extension
      Geo
      D B C A
      hNCDBC
      hRightDBC
      hDBA

  have hDBC_ABC :
      Geo.AngleCongruent D B C A B C :=
    (Geo.angle_congruent_reverse_second
      D B C
      C B A).mp hDBC_CBA

  have hRightB :
      HilbertRightAngle Geo A B C :=
    hilbert_right_angle_transport
      Geo
      D B C
      A B C
      hNCDBC
      hABC
      hRightDBC
      hDBC_ABC

  exact
    i47_two_right_angles_impossible
      Geo A B C
      hABC
      hRightA
      hRightB

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


/-
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
/-
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
-/

/--
First step of the internal cut in Euclid I.47.

From the right-angle vertex A drop a perpendicular to the carrier BC.
At this stage we record only incidence of the foot M on BC and the
right angle.  The strict order B-M-C will be proved separately.
-/
theorem i47_perpendicular_foot_on_BC
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base) :
    ∃ M R : Geo.Point,
      HilbertIncidence.OnLine M base ∧
      HilbertIncidence.OnLine R base ∧
      HilbertRightAngle Geo R M A := by

  --------------------------------------------------------------------
  -- BC is nondegenerate.
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

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  --------------------------------------------------------------------
  -- A is outside the carrier BC.
  --------------------------------------------------------------------

  have hAoff :
      Not (HilbertIncidence.OnLine A base) := by
    intro hAbase
    exact
      hABC
        ⟨base, hAbase, hBbase, hCbase⟩

  --------------------------------------------------------------------
  -- Euclid I.12 / Hilbert perpendicular construction.
  --------------------------------------------------------------------

  rcases
      hilbert_perpendicular_from_point_exists
        Geo
        B C A
        base
        hBC
        hBbase
        hCbase
        hAoff with
    ⟨M, R, hMbase, hRbase, hRightRMA⟩

  exact
    ⟨M, R,
      hMbase,
      hRbase,
      hRightRMA⟩

/--
In a right triangle ABC, right at A, the angle at B is strictly
smaller than the right angle BAC.

This is the exterior-angle theorem I.16 applied after extending
CA beyond A.
-/
theorem i47_angle_ABC_less_right_BAC
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hRight : HilbertRightAngle Geo B A C) :
    HilbertAngleLess Geo A B C B A C := by

  --------------------------------------------------------------------
  -- Required permutations of triangle noncollinearity.
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

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle Geo B C A h))

  --------------------------------------------------------------------
  -- Extend CA through A to X:
  --
  --     C - A - X.
  --------------------------------------------------------------------

  have hCA : C ≠ A :=
    hilbert_noncollinear_ne_first
      Geo C A B hCAB

  rcases
      HilbertOrder.between_extension
        C A hCA with
    ⟨X, hCAX⟩

  --------------------------------------------------------------------
  -- I.16 on triangle B C A:
  --
  --     angle CBA < angle BAX.
  --------------------------------------------------------------------

  have hLessCBA_BAX :
      HilbertAngleLess Geo C B A B A X :=
    euclid_proposition_16_first
      Geo
      B C A X
      hBCA
      hCAX

  --------------------------------------------------------------------
  -- Reverse CBA to ABC.
  --------------------------------------------------------------------

  have hABC_CBA :
      Geo.AngleCongruent A B C C B A :=
    bookZero_56_ABCequalsCBA
      Geo A B C hABC

  have hLessABC_BAX :
      HilbertAngleLess Geo A B C B A X :=
    hilbert_angleLess_transport_left
      Geo
      C B A
      A B C
      B A X
      hLessCBA_BAX
      hABC
      hABC_CBA

  --------------------------------------------------------------------
  -- CAB is right because BAC is right.
  --------------------------------------------------------------------

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
      hRight
      hBAC_CAB

  --------------------------------------------------------------------
  -- Since C-A-X, the exterior angle BAX is also right.
  --------------------------------------------------------------------

  have hCAB_BAX :
      Geo.AngleCongruent C A B B A X :=
    hilbert_right_angle_opposite_extension
      Geo
      C A B X
      hCAB
      hRightCAB
      hCAX

  have hBAX :
      Not (Collinear Geo B A X) :=
    hLessABC_BAX.2.1

  have hRightBAX :
      HilbertRightAngle Geo B A X :=
    hilbert_right_angle_transport
      Geo
      C A B
      B A X
      hCAB
      hBAX
      hRightCAB
      hCAB_BAX

  --------------------------------------------------------------------
  -- All right angles are congruent:
  --
  --     BAX ~= BAC.
  --------------------------------------------------------------------

  have hBAX_BAC :
      Geo.AngleCongruent B A X B A C :=
    hilbert_all_right_angles_congruent
      Geo
      B A X
      B A C
      hBAX
      hBAC
      hRightBAX
      hRight

  --------------------------------------------------------------------
  -- Transport the containing angle.
  --------------------------------------------------------------------

  exact
    hilbert_angleLess_transport_right
      Geo
      A B C
      B A X
      B A C
      hLessABC_BAX
      hBAC
      hBAX_BAC

/--
In a right triangle ABC, right at A, the angle at C is strictly
smaller than the right angle BAC.
-/
theorem i47_angle_ACB_less_right_BAC
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hRight : HilbertRightAngle Geo B A C) :
    HilbertAngleLess Geo A C B B A C := by

  --------------------------------------------------------------------
  -- Noncollinearity permutations.
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

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate Geo A C B h)

  --------------------------------------------------------------------
  -- Reverse the right angle BAC to CAB.
  --------------------------------------------------------------------

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
      hRight
      hBAC_CAB

  --------------------------------------------------------------------
  -- Apply the previous theorem to triangle A C B.
  --
  -- This gives:
  --
  --     ACB < CAB.
  --------------------------------------------------------------------

  have hLessACB_CAB :
      HilbertAngleLess Geo A C B C A B :=
    i47_angle_ABC_less_right_BAC
      Geo
      A C B
      hACB
      hRightCAB

  --------------------------------------------------------------------
  -- Normalize the containing right angle CAB back to BAC.
  --------------------------------------------------------------------

  have hCAB_BAC :
      Geo.AngleCongruent C A B B A C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B A C
      C A B
      hBAC_CAB

  exact
    hilbert_angleLess_transport_right
      Geo
      A C B
      C A B
      B A C
      hLessACB_CAB
      hBAC
      hCAB_BAC

/--
A right angle determined by one nonvertex point of a carrier remains
right when that point is replaced by any other nonvertex point of the
same carrier.

This is the local transport needed for the perpendicular foot in I.47.
-/
theorem i47_right_angle_along_base
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A R M X : Geo.Point)
    (base : Geo.Line)
    (hAoff : Not (HilbertIncidence.OnLine A base))
    (hRbase : HilbertIncidence.OnLine R base)
    (hMbase : HilbertIncidence.OnLine M base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hMX : M ≠ X)
    (hRight : HilbertRightAngle Geo R M A) :
    HilbertRightAngle Geo X M A := by

  --------------------------------------------------------------------
  -- The defining witness of the right angle gives R != M.
  --------------------------------------------------------------------

  rcases hRight with
    ⟨T, hRMT, hRightEq⟩

  have hRM : R ≠ M :=
    (HilbertOrder.between_incidence
      R M T hRMT).1

  have hMR : M ≠ R :=
    hRM.symm

  have hRight' :
      HilbertRightAngle Geo R M A :=
    ⟨T, hRMT, hRightEq⟩

  --------------------------------------------------------------------
  -- Both source and target angles are nondegenerate because A is
  -- outside the base line.
  --------------------------------------------------------------------

  have hRMA :
      Not (Collinear Geo R M A) :=
    hilbert_not_collinear_of_off_line
      Geo
      R M A
      base
      hRM
      hRbase
      hMbase
      hAoff

  have hXMA :
      Not (Collinear Geo X M A) :=
    hilbert_not_collinear_of_off_line
      Geo
      X M A
      base
      hMX.symm
      hXbase
      hMbase
      hAoff

  --------------------------------------------------------------------
  -- If R = X there is nothing to prove.
  --------------------------------------------------------------------

  by_cases hRX : R = X

  · subst X
    exact hRight'

  --------------------------------------------------------------------
  -- Otherwise M,R,X are three distinct collinear points.
  --------------------------------------------------------------------

  have hMRX :
      Collinear Geo M R X :=
    ⟨base,
      hMbase,
      hRbase,
      hXbase⟩

  rcases
      hilbert_between_trichotomy
        Geo
        M R X
        hMR
        hRX
        hMX
        hMRX with
    hMRXbet | hRMXbet | hMXRbet

  --------------------------------------------------------------------
  -- Case M-R-X: R and X are on the same ray from M.
  --------------------------------------------------------------------

  · have hRayMRX :
        HilbertSameRay Geo M R X :=
      hilbert_sameRay_of_between
        Geo M R X hMRXbet

    have hAngleEq :
        Geo.Angle R M A =
        Geo.Angle X M A :=
      hilbert_angle_eq_of_sameRay_first
        Geo M R X A hRayMRX

    have hRefl :
        Geo.AngleCongruent R M A R M A :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        R M A
        hRMA

    have hCong :
        Geo.AngleCongruent R M A X M A := by
      unfold Geometry.Geo.AngleCongruent at hRefl ⊢
      rw [← hAngleEq]
      exact hRefl

    exact
      hilbert_right_angle_transport
        Geo
        R M A
        X M A
        hRMA
        hXMA
        hRight'
        hCong

  --------------------------------------------------------------------
  -- Case R-M-X: X is on the opposite ray from R.
  --------------------------------------------------------------------

  · have hCong0 :
        Geo.AngleCongruent R M A A M X :=
      hilbert_right_angle_opposite_extension
        Geo
        R M A X
        hRMA
        hRight'
        hRMXbet

    have hCong :
        Geo.AngleCongruent R M A X M A :=
      (Geo.angle_congruent_reverse_second
        R M A
        A M X).mp hCong0

    exact
      hilbert_right_angle_transport
        Geo
        R M A
        X M A
        hRMA
        hXMA
        hRight'
        hCong

  --------------------------------------------------------------------
  -- Case M-X-R: again R and X are on the same ray from M.
  --------------------------------------------------------------------

  · have hRayMXR :
        HilbertSameRay Geo M X R :=
      hilbert_sameRay_of_between
        Geo M X R hMXRbet

    have hRayMRX :
        HilbertSameRay Geo M R X :=
      hilbert_sameRay_symm
        Geo M X R hRayMXR

    have hAngleEq :
        Geo.Angle R M A =
        Geo.Angle X M A :=
      hilbert_angle_eq_of_sameRay_first
        Geo M R X A hRayMRX

    have hRefl :
        Geo.AngleCongruent R M A R M A :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        R M A
        hRMA

    have hCong :
        Geo.AngleCongruent R M A X M A := by
      unfold Geometry.Geo.AngleCongruent at hRefl ⊢
      rw [← hAngleEq]
      exact hRefl

    exact
      hilbert_right_angle_transport
        Geo
        R M A
        X M A
        hRMA
        hXMA
        hRight'
        hCong

/--
The perpendicular from the right-angle vertex A to the carrier BC
meets the open segment BC.

The two exterior positions of M are excluded by Euclid I.16 together
with the fact that both acute angles of the right triangle are smaller
than the right angle at A.
-/
theorem i47_aux_perpendicular_foot_between_BC
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C M R : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hRightA : HilbertRightAngle Geo B A C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hMbase : HilbertIncidence.OnLine M base)
    (hRbase : HilbertIncidence.OnLine R base)
    (hRightRMA : HilbertRightAngle Geo R M A) :
    Geo.Between B M C := by

  --------------------------------------------------------------------
  -- Triangle nondegeneracy in the orientations used below.
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

  have hACB :
      Not (Collinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate Geo A C B h)

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle Geo B C A h))

  have hCBA :
      Not (Collinear Geo C B A) := by
    intro h
    exact
      hABC
        (PrimCollinearSymm Geo C B A h)

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  --------------------------------------------------------------------
  -- A is off the carrier BC.
  --------------------------------------------------------------------

  have hAoff :
      Not (HilbertIncidence.OnLine A base) := by
    intro hAbase
    exact
      hABC
        ⟨base,
          hAbase,
          hBbase,
          hCbase⟩

  --------------------------------------------------------------------
  -- CAB is also right.
  --------------------------------------------------------------------

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
  -- Exclude M = B.
  --------------------------------------------------------------------

  have hMB : M ≠ B := by
    intro hEq
    subst M

    have hRightCBA :
        HilbertRightAngle Geo C B A :=
      i47_right_angle_along_base
        Geo
        A R B C
        base
        hAoff
        hRbase
        hBbase
        hCbase
        hBC
        hRightRMA

    have hCBA_ABC :
        Geo.AngleCongruent C B A A B C :=
      bookZero_56_ABCequalsCBA
        Geo C B A hCBA

    have hRightABC :
        HilbertRightAngle Geo A B C :=
      hilbert_right_angle_transport
        Geo
        C B A
        A B C
        hCBA
        hABC
        hRightCBA
        hCBA_ABC

    exact
      i47_two_right_angles_impossible
        Geo
        A B C
        hABC
        hRightA
        hRightABC

  --------------------------------------------------------------------
  -- Exclude M = C.
  --------------------------------------------------------------------

  have hMC : M ≠ C := by
    intro hEq
    subst M

    have hRightBCA :
        HilbertRightAngle Geo B C A :=
      i47_right_angle_along_base
        Geo
        A R C B
        base
        hAoff
        hRbase
        hCbase
        hBbase
        hBC.symm
        hRightRMA

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

    exact
      i47_two_right_angles_impossible
        Geo
        A C B
        hACB
        hRightCAB
        hRightACB

  have hBM : B ≠ M :=
    hMB.symm

  --------------------------------------------------------------------
  -- B, M, C lie on the same carrier.
  --------------------------------------------------------------------

  have hBMCcol :
      Collinear Geo B M C :=
    ⟨base,
      hBbase,
      hMbase,
      hCbase⟩

  --------------------------------------------------------------------
  -- Order trichotomy:
  --
  --     B-M-C
  --     M-B-C
  --     B-C-M
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        B M C
        hBM
        hMC
        hBC
        hBMCcol with
    hBMC | hMBC | hBCM

  --------------------------------------------------------------------
  -- Case 1: B-M-C.
  --------------------------------------------------------------------

  · exact hBMC

  --------------------------------------------------------------------
  -- Case 2: M-B-C.
  --
  -- I.16 in triangle A M B:
  --
  --     AMB < ABC.
  --
  -- Also ABC < BAC.
  --
  -- Since AMB and BAC are both right, this is impossible.
  --------------------------------------------------------------------

  · have hBMA :
        Not (Collinear Geo B M A) :=
      hilbert_not_collinear_of_off_line
        Geo
        B M A
        base
        hBM
        hBbase
        hMbase
        hAoff

    have hAMB :
        Not (Collinear Geo A M B) := by
      intro h
      exact
        hBMA
          (PrimCollinearSymm Geo A M B h)

    have hRightBMA :
        HilbertRightAngle Geo B M A :=
      i47_right_angle_along_base
        Geo
        A R M B
        base
        hAoff
        hRbase
        hMbase
        hBbase
        hMB
        hRightRMA

    have hBMA_AMB :
        Geo.AngleCongruent B M A A M B :=
      bookZero_56_ABCequalsCBA
        Geo B M A hBMA

    have hRightAMB :
        HilbertRightAngle Geo A M B :=
      hilbert_right_angle_transport
        Geo
        B M A
        A M B
        hBMA
        hAMB
        hRightBMA
        hBMA_AMB

    have hLessAMB_ABC :
        HilbertAngleLess Geo A M B A B C :=
      euclid_proposition_16_second
        Geo
        A M B C
        hAMB
        hMBC

    have hLessABC_BAC :
        HilbertAngleLess Geo A B C B A C :=
      i47_angle_ABC_less_right_BAC
        Geo
        A B C
        hABC
        hRightA

    have hLessAMB_BAC :
        HilbertAngleLess Geo A M B B A C :=
      hilbert_angleLess_trans
        Geo
        A M B
        A B C
        B A C
        hLessAMB_ABC
        hLessABC_BAC

    have hAMB_BAC :
        Geo.AngleCongruent A M B B A C :=
      hilbert_all_right_angles_congruent
        Geo
        A M B
        B A C
        hAMB
        hBAC
        hRightAMB
        hRightA

    ------------------------------------------------------------------
    -- transport_left wants:
    --
    --     new ~= old
    --
    -- hence BAC ~= AMB.
    ------------------------------------------------------------------

    have hBAC_AMB :
        Geo.AngleCongruent B A C A M B :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A M B
        B A C
        hAMB_BAC

    have hSelf :
        HilbertAngleLess Geo B A C B A C :=
      hilbert_angleLess_transport_left
        Geo
        A M B
        B A C
        B A C
        hLessAMB_BAC
        hBAC
        hBAC_AMB

    exact
      False.elim
        ((hilbert_angleLess_irrefl
          Geo B A C)
          hSelf)

  --------------------------------------------------------------------
  -- Case 3: B-C-M.
  --
  -- Reverse to M-C-B.  I.16 in triangle A M C:
  --
  --     AMC < ACB.
  --
  -- Also ACB < BAC.
  --
  -- Since AMC and BAC are both right, this is impossible.
  --------------------------------------------------------------------

  · have hMCB :
        Geo.Between M C B :=
      (HilbertOrder.between_incidence
        B C M hBCM).2.2.2.2

    have hCMA :
        Not (Collinear Geo C M A) :=
      hilbert_not_collinear_of_off_line
        Geo
        C M A
        base
        hMC.symm
        hCbase
        hMbase
        hAoff

    have hAMC :
        Not (Collinear Geo A M C) := by
      intro h
      exact
        hCMA
          (PrimCollinearSymm Geo A M C h)

    have hRightCMA :
        HilbertRightAngle Geo C M A :=
      i47_right_angle_along_base
        Geo
        A R M C
        base
        hAoff
        hRbase
        hMbase
        hCbase
        hMC
        hRightRMA

    have hCMA_AMC :
        Geo.AngleCongruent C M A A M C :=
      bookZero_56_ABCequalsCBA
        Geo C M A hCMA

    have hRightAMC :
        HilbertRightAngle Geo A M C :=
      hilbert_right_angle_transport
        Geo
        C M A
        A M C
        hCMA
        hAMC
        hRightCMA
        hCMA_AMC

    have hLessAMC_ACB :
        HilbertAngleLess Geo A M C A C B :=
      euclid_proposition_16_second
        Geo
        A M C B
        hAMC
        hMCB

    have hLessACB_BAC :
        HilbertAngleLess Geo A C B B A C :=
      i47_angle_ACB_less_right_BAC
        Geo
        A B C
        hABC
        hRightA

    have hLessAMC_BAC :
        HilbertAngleLess Geo A M C B A C :=
      hilbert_angleLess_trans
        Geo
        A M C
        A C B
        B A C
        hLessAMC_ACB
        hLessACB_BAC

    have hAMC_BAC :
        Geo.AngleCongruent A M C B A C :=
      hilbert_all_right_angles_congruent
        Geo
        A M C
        B A C
        hAMC
        hBAC
        hRightAMC
        hRightA

    ------------------------------------------------------------------
    -- Again transport_left needs new ~= old:
    --
    --     BAC ~= AMC.
    ------------------------------------------------------------------

    have hBAC_AMC :
        Geo.AngleCongruent B A C A M C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A M C
        B A C
        hAMC_BAC

    have hSelf :
        HilbertAngleLess Geo B A C B A C :=
      hilbert_angleLess_transport_left
        Geo
        A M C
        B A C
        B A C
        hLessAMC_BAC
        hBAC
        hBAC_AMC

    exact
      False.elim
        ((hilbert_angleLess_irrefl
          Geo B A C)
          hSelf)

/--
The perpendicular through the interior foot M is parallel to the
square side CE.

Choose X strictly between M and C.  The angles XMA and XCE are both
right angles.  Since A and E lie on opposite sides of the transversal
BC, equal alternate angles give MA || CE.
-/
theorem i47_aux_perpendicular_foot_parallel_CE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E M R : Geo.Point)
    (base : Geo.Line)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hMbase : HilbertIncidence.OnLine M base)
    (hRbase : HilbertIncidence.OnLine R base)
    (hBMC : Geo.Between B M C)
    (hRightRMA : HilbertRightAngle Geo R M A)
    (hSquare : IsSquare Geo B C E D)
    (hOppEA : HilbertOppositeSide Geo E A base) :
    Geo.Parallel M A C E := by

  --------------------------------------------------------------------
  -- A and E are off the transversal BC.
  --------------------------------------------------------------------

  have hEoff :
      Not (HilbertIncidence.OnLine E base) :=
    hOppEA.1

  have hAoff :
      Not (HilbertIncidence.OnLine A base) :=
    hOppEA.2.1

  --------------------------------------------------------------------
  -- M != C because B-M-C.
  --------------------------------------------------------------------

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hMC : M ≠ C :=
    hBMCdata.2.1

  --------------------------------------------------------------------
  -- Choose X strictly between M and C.
  --------------------------------------------------------------------

  rcases
      hilbert_between_exists
        Geo M C hMC with
    ⟨X, hMXC⟩

  have hMXCdata :=
    HilbertOrder.between_incidence
      M X C hMXC

  have hMX : M ≠ X :=
    hMXCdata.1

  have hXC : X ≠ C :=
    hMXCdata.2.1

  have hCX : C ≠ X :=
    hXC.symm

  have hXbase :
      HilbertIncidence.OnLine X base :=
    hilbert_between_on_line
      Geo
      M X C
      base
      hMbase
      hCbase
      hMXC

  --------------------------------------------------------------------
  -- XMA is right: replace the arbitrary base point R in the
  -- perpendicular construction by X.
  --------------------------------------------------------------------

  have hRightXMA :
      HilbertRightAngle Geo X M A :=
    i47_right_angle_along_base
      Geo
      A R M X
      base
      hAoff
      hRbase
      hMbase
      hXbase
      hMX
      hRightRMA

  --------------------------------------------------------------------
  -- BCE is right because BCED is a square.
  --------------------------------------------------------------------

  have hRightBCE :
      HilbertRightAngle Geo B C E :=
    hSquare.2.2.2.2.2.1

  --------------------------------------------------------------------
  -- Replace B by X on the same carrier BC: XCE is right.
  --------------------------------------------------------------------

  have hRightXCE :
      HilbertRightAngle Geo X C E :=
    i47_right_angle_along_base
      Geo
      E B C X
      base
      hEoff
      hBbase
      hCbase
      hXbase
      hCX
      hRightBCE

  --------------------------------------------------------------------
  -- Nondegeneracy of the two right angles.
  --------------------------------------------------------------------

  have hXMA :
      Not (Collinear Geo X M A) :=
    hilbert_not_collinear_of_off_line
      Geo
      X M A
      base
      hMX.symm
      hXbase
      hMbase
      hAoff

  have hXCE :
      Not (Collinear Geo X C E) :=
    hilbert_not_collinear_of_off_line
      Geo
      X C E
      base
      hXC
      hXbase
      hCbase
      hEoff

  --------------------------------------------------------------------
  -- All right angles are congruent.
  --------------------------------------------------------------------

  have hAlternate :
      Geo.AngleCongruent X M A X C E :=
    hilbert_all_right_angles_congruent
      Geo
      X M A
      X C E
      hXMA
      hXCE
      hRightXMA
      hRightXCE

  --------------------------------------------------------------------
  -- A and E lie on opposite sides of BC.
  --------------------------------------------------------------------

  have hOppAE :
      HilbertOppositeSide Geo A E base :=
    hilbert_oppositeSide_symm
      Geo E A base hOppEA

  --------------------------------------------------------------------
  -- X is between M and C on the transversal.  Equal alternate right
  -- angles therefore give MA || CE.
  --------------------------------------------------------------------

  exact
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      M A
      C X E
      base
      hMXC
      hMbase
      hCbase
      hOppAE
      hAlternate

/--
Complete C-E-M to the parallelogram C-E-L-M.

Since C and M lie on the base BC while E lies off that base,
the three points C,E,M are noncollinear.
-/
theorem i47_aux_construct_L_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (C E M : Geo.Point)
    (base : Geo.Line)
    (hCbase : HilbertIncidence.OnLine C base)
    (hMbase : HilbertIncidence.OnLine M base)
    (hEoff : Not (HilbertIncidence.OnLine E base))
    (hMC : M ≠ C) :
    ∃ L : Geo.Point,
      IsParallelogram Geo C E L M := by

  have hCM : C ≠ M :=
    hMC.symm

  have hCME :
      Not (Collinear Geo C M E) :=
    hilbert_not_collinear_of_off_line
      Geo
      C M E
      base
      hCM
      hCbase
      hMbase
      hEoff

  have hCEM :
      Not (Collinear Geo C E M) := by
    intro h
    exact
      hCME
        (PrimCollinearRotate Geo C E M h)

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo C E M hCEM with
    ⟨L, hPar⟩

  exact ⟨L, hPar⟩

/--
If MA is parallel to CE and C-E-L-M is a parallelogram, then
A, M, L lie on one line.

Indeed ML is also parallel to CE.  Two distinct carriers through M
cannot both be parallel to CE.
-/
theorem i47_aux_cut_line_collinear
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A C E M L : Geo.Point)
    (hMA_CE : Geo.Parallel M A C E)
    (hPar : IsParallelogram Geo C E L M) :
    Collinear Geo A M L := by

  --------------------------------------------------------------------
  -- From the parallelogram C-E-L-M:
  --
  --     CE || LM,
  --
  -- hence ML || CE.
  --------------------------------------------------------------------

  have hLM_CE :
      Geo.Parallel L M C E :=
    ParallelSymmetry
      Geo
      C E L M
      hPar.1

  have hML_CE :
      Geo.Parallel M L C E :=
    ParallelSwapFirstLine
      Geo
      L M C E
      hLM_CE

  --------------------------------------------------------------------
  -- The carriers MA and ML must coincide.
  --
  -- Otherwise Euclidean transitivity gives MA || ML, impossible
  -- because both contain M.
  --------------------------------------------------------------------

  have hCarrier :
      Geo.PointLine M A =
      Geo.PointLine M L := by

    by_contra hDistinct

    have hMA_ML :
        Geo.Parallel M A M L :=
      hilbert_parallel_transitive_distinct
        Geo
        M A
        M L
        C E
        hMA_CE
        hML_CE
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        M A
        M L
        M
        (intersection_test_left_mem Geo M A)
        (intersection_test_left_mem Geo M L))
        hMA_ML

  --------------------------------------------------------------------
  -- Convert equality of the two extensional carriers back to
  -- ordinary Hilbert collinearity.
  --------------------------------------------------------------------

  have hMA : M ≠ A :=
    hMA_CE.1

  have hML : M ≠ L :=
    hML_CE.1

  rcases
      HilbertPlaneIncidence.line_through
        M A hMA with
    ⟨lineMA, hMma, hAma⟩

  have hL_ML :
      L ∈ Geo.PointLine M L :=
    intersection_test_right_mem
      Geo M L

  have hL_MA :
      L ∈ Geo.PointLine M A := by
    rw [hCarrier]
    exact hL_ML

  have hLma :
      HilbertIncidence.OnLine L lineMA :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      M A L
      lineMA
      hMA
      hMma
      hAma).mp hL_MA

  exact
    ⟨lineMA,
      hAma,
      hMma,
      hLma⟩

/--
The new point L lies on the upper carrier DE of the square.

Indeed EL is parallel to the base carrier BC through the parallelogram
C-E-L-M, while ED is parallel to BC through the square B-C-E-D.
Since both carriers pass through E, they coincide.
-/
theorem i47_aux_L_on_DE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hSquare : IsSquare Geo B C E D)
    (hPar : IsParallelogram Geo C E L M) :
    Collinear Geo D L E := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBC : B ≠ C :=
    hBMCdata.2.2.1

  have hCM : C ≠ M :=
    hBMCdata.2.1.symm

  --------------------------------------------------------------------
  -- EL || MC from C-E-L-M.
  --------------------------------------------------------------------

  have hEL_MC :
      Geo.Parallel E L M C :=
    hPar.2

  have hMC_EL :
      Geo.Parallel M C E L :=
    ParallelSymmetry
      Geo E L M C hEL_MC

  have hCM_EL :
      Geo.Parallel C M E L :=
    ParallelSwapFirstLine
      Geo M C E L hMC_EL

  --------------------------------------------------------------------
  -- Replace M by B on the same base carrier:
  --
  --     CB || EL.
  --------------------------------------------------------------------

  have hCBMcol :
      Collinear Geo C B M := by
    have hBMCcol :
        Collinear Geo B M C :=
      hBMCdata.2.2.2.1

    exact
      PrimCollinearCycle
        Geo
        M C B
        (PrimCollinearCycle
          Geo B M C hBMCcol)

  have hCB_EL :
      Geo.Parallel C B E L :=
    collinear_parallel_trans
      Geo
      C B M
      E L
      hBC.symm
      hCBMcol
      hCM_EL

  have hEL_CB :
      Geo.Parallel E L C B :=
    ParallelSymmetry
      Geo C B E L hCB_EL

  --------------------------------------------------------------------
  -- ED || CB from the square.
  --------------------------------------------------------------------

  have hBC_ED :
      Geo.Parallel B C E D :=
    hSquare.1.1

  have hCB_ED :
      Geo.Parallel C B E D :=
    ParallelSwapFirstLine
      Geo B C E D hBC_ED

  have hED_CB :
      Geo.Parallel E D C B :=
    ParallelSymmetry
      Geo C B E D hCB_ED

  --------------------------------------------------------------------
  -- EL and ED cannot be distinct parallel carriers through E.
  --------------------------------------------------------------------

  have hCarrier :
      Geo.PointLine E L =
      Geo.PointLine E D := by

    by_contra hDistinct

    have hEL_ED :
        Geo.Parallel E L E D :=
      hilbert_parallel_transitive_distinct
        Geo
        E L
        E D
        C B
        hEL_CB
        hED_CB
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        E L
        E D
        E
        (intersection_test_left_mem Geo E L)
        (intersection_test_left_mem Geo E D))
        hEL_ED

  --------------------------------------------------------------------
  -- Convert carrier equality back to collinearity D-L-E.
  --------------------------------------------------------------------

  have hEL : E ≠ L :=
    hEL_CB.1

  rcases
      HilbertPlaneIncidence.line_through
        E L hEL with
    ⟨lineEL, hEel, hLel⟩

  have hD_ED :
      D ∈ Geo.PointLine E D :=
    intersection_test_right_mem
      Geo E D

  have hD_EL :
      D ∈ Geo.PointLine E L := by
    rw [hCarrier]
    exact hD_ED

  have hDel :
      HilbertIncidence.OnLine D lineEL :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      E L D
      lineEL
      hEL
      hEel
      hLel).mp hD_EL

  exact
    ⟨lineEL,
      hDel,
      hLel,
      hEel⟩


/--
The left part cut from the square is the parallelogram L-D-B-M.

The only delicate point is proving L != D.  Since B-M-C,
CM is a proper part of CB.  The two known parallelograms transport
these lengths to EL and ED, hence EL < ED and therefore L != D.
-/
theorem i47_aux_left_cut_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hDLE : Collinear Geo D L E)
    (hSquare : IsSquare Geo B C E D)
    (hPar : IsParallelogram Geo C E L M) :
    IsParallelogram Geo L D B M := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBM : B ≠ M :=
    hBMCdata.1

  have hMC : M ≠ C :=
    hBMCdata.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  --------------------------------------------------------------------
  -- First prove L != D.
  --
  -- Reverse B-M-C to C-M-B, hence CM < CB.
  --------------------------------------------------------------------

  have hCMB :
      Geo.Between C M B :=
    hBMCdata.2.2.2.2

  have hCMltCB :
      HilbertSegmentLess Geo C M C B :=
    hilbert_segmentLess_of_between
      Geo C M B hCMB

  --------------------------------------------------------------------
  -- In C-E-L-M:
  --
  --     EL ~= MC,
  --
  -- hence EL ~= CM.
  --------------------------------------------------------------------

  have hParSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hPar

  have hEL_MC :
      Geo.Congruent E L M C :=
    hParSides.2

  have hEL_CM :
      Geo.Congruent E L C M :=
    CongruentSwapSecond
      Geo E L M C hEL_MC

  have hELltCB :
      HilbertSegmentLess Geo E L C B :=
    hilbert_segmentLess_congruent_left
      Geo
      C M
      E L
      C B
      hCMltCB
      hEL_CM

  --------------------------------------------------------------------
  -- In the square B-C-E-D:
  --
  --     BC ~= ED,
  --
  -- hence CB ~= ED.
  --------------------------------------------------------------------

  have hSquareSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hSquare.1

  have hBC_ED :
      Geo.Congruent B C E D :=
    hSquareSides.1

  have hCB_ED :
      Geo.Congruent C B E D :=
    CongruentReverseFirst
      Geo B C E D hBC_ED

  have hELltED :
      HilbertSegmentLess Geo E L E D :=
    hilbert_segmentLess_congruent_right
      Geo
      E L
      C B
      E D
      hELltCB
      hCB_ED

  have hLD : L ≠ D := by
    intro hEq
    subst D

    exact
      (hilbert_segmentLess_not_congruent
        Geo E L E L hELltED)
        (hilbert_congruent_reflexive
          Geo E L)

  --------------------------------------------------------------------
  -- First pair:
  --
  --     LD || BM.
  --
  -- Start from BC || ED, transport BC to BM, then ED to LD.
  --------------------------------------------------------------------

  have hBM_ED :
      Geo.Parallel B M E D :=
    collinear_parallel_trans
      Geo
      B M C
      E D
      hBM
      hBMCcol
      hSquare.1.1

  have hED_BM :
      Geo.Parallel E D B M :=
    ParallelSymmetry
      Geo B M E D hBM_ED

  have hLED :
      Collinear Geo L E D :=
    PrimCollinearCycle
      Geo D L E hDLE

  have hLD_BM :
      Geo.Parallel L D B M :=
    ParallelCollinearLeft
      Geo
      E D L
      B M
      hLD
      hED_BM
      hLED

  --------------------------------------------------------------------
  -- Second pair:
  --
  --     DB || ML.
  --
  -- Both are parallel to CE.
  --------------------------------------------------------------------

  have hDB_CE :
      Geo.Parallel D B C E :=
    ParallelSymmetry
      Geo
      C E D B
      hSquare.1.2

  have hLM_CE :
      Geo.Parallel L M C E :=
    ParallelSymmetry
      Geo
      C E L M
      hPar.1

  have hML_CE :
      Geo.Parallel M L C E :=
    ParallelSwapFirstLine
      Geo
      L M C E
      hLM_CE

  --------------------------------------------------------------------
  -- DB and ML are distinct carriers.
  --
  -- If they coincided, B would lie on ML.  Together with B-M-C
  -- this would force L,M,C collinear, contradicting the
  -- nondegeneracy of C-E-L-M.
  --------------------------------------------------------------------

  have hDistinct :
      Geo.PointLine D B ≠
      Geo.PointLine M L := by

    intro hEq

    have hML : M ≠ L :=
      hML_CE.1

    rcases
        HilbertPlaneIncidence.line_through
          M L hML with
      ⟨lineML, hMml, hLml⟩

    have hB_DB :
        B ∈ Geo.PointLine D B :=
      intersection_test_right_mem
        Geo D B

    have hB_ML :
        B ∈ Geo.PointLine M L := by
      rw [← hEq]
      exact hB_DB

    have hBml :
        HilbertIncidence.OnLine B lineML :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        M L B
        lineML
        hML
        hMml
        hLml).mp hB_ML

    have hBML :
        Collinear Geo B M L :=
      ⟨lineML,
        hBml,
        hMml,
        hLml⟩

    have hLMB :
        Collinear Geo L M B :=
      PrimCollinearSymm
        Geo B M L hBML

    have hBCM :
        Collinear Geo B C M :=
      PrimCollinearRotate
        Geo B M C hBMCcol

    have hLMC :
        Collinear Geo L M C :=
      CollinearTrans
        Geo
        L M B C
        hBM.symm
        hLMB
        hBCM

    have hNC :=
      parallelogram_vertices_noncollinear
        Geo C E L M hPar

    exact
      hNC.2.2.2 hLMC

  have hDB_ML :
      Geo.Parallel D B M L :=
    hilbert_parallel_transitive_distinct
      Geo
      D B
      M L
      C E
      hDB_CE
      hML_CE
      hDistinct

  exact
    ⟨hLD_BM,
      hDB_ML⟩

/--
The order B-M-C on the lower side of the square transfers to
D-L-E on the upper side.

The two cut parallelograms and the original square provide the three
corresponding segment congruences required by Hilbert Theorem 27.
-/
theorem i47_aux_upper_cut_between
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hSquare : IsSquare Geo B C E D)
    (hRightPar : IsParallelogram Geo C E L M)
    (hLeftPar : IsParallelogram Geo L D B M) :
    Geo.Between D L E := by

  --------------------------------------------------------------------
  -- Distinctness of D,L,E follows directly from the parallel sides.
  --------------------------------------------------------------------

  have hDL : D ≠ L :=
    hLeftPar.1.1.symm

  have hLE : L ≠ E :=
    hRightPar.2.1.symm

  have hDE : D ≠ E :=
    hSquare.1.1.2.1.symm

  --------------------------------------------------------------------
  -- BM ~= DL from L-D-B-M.
  --------------------------------------------------------------------

  have hLeftSides :
      OppositeSidesCongruent Geo L D B M :=
    ParallelogramOppositeSidesCongruent
      Geo L D B M hLeftPar

  have hLD_BM :
      Geo.Congruent L D B M :=
    hLeftSides.1

  have hBM_LD :
      Geo.Congruent B M L D :=
    hilbert_congruent_symmetry
      Geo L D B M hLD_BM

  have hBM_DL :
      Geo.Congruent B M D L :=
    CongruentSwapSecond
      Geo B M L D hBM_LD

  --------------------------------------------------------------------
  -- BC ~= DE from the square B-C-E-D.
  --------------------------------------------------------------------

  have hSquareSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hSquare.1

  have hBC_ED :
      Geo.Congruent B C E D :=
    hSquareSides.1

  have hBC_DE :
      Geo.Congruent B C D E :=
    CongruentSwapSecond
      Geo B C E D hBC_ED

  --------------------------------------------------------------------
  -- MC ~= LE from C-E-L-M.
  --------------------------------------------------------------------

  have hRightSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hRightPar

  have hEL_MC :
      Geo.Congruent E L M C :=
    hRightSides.2

  have hMC_EL :
      Geo.Congruent M C E L :=
    hilbert_congruent_symmetry
      Geo E L M C hEL_MC

  have hMC_LE :
      Geo.Congruent M C L E :=
    CongruentSwapSecond
      Geo M C E L hMC_EL

  --------------------------------------------------------------------
  -- Hilbert Theorem 27 transports the strict order.
  --
  --     B-M-C
  --       |
  --       | BM ~= DL
  --       | BC ~= DE
  --       | MC ~= LE
  --       v
  --     D-L-E
  --------------------------------------------------------------------

  exact
    hilbert_theorem27_three_points
      Geo
      B M C
      D L E
      hBMC
      hDL
      hLE
      hDE
      hBM_DL
      hBC_DE
      hMC_LE

axiom i47_cut_core
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (base : Geo.Line)
    (hABC : Not (Collinear Geo A B C))
    (hRight : HilbertRightAngle Geo B A C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSquare : IsSquare Geo B C E D)
    (hOppDA : HilbertOppositeSide Geo D A base)
    (hOppEA : HilbertOppositeSide Geo E A base) :
    ∃ L M N : Geo.Point,
      Geo.Between B M C ∧
      Geo.Between D L E ∧
      Geo.Between D N C ∧
      Geo.Between M N L ∧
      IsParallelogram Geo L D B M ∧
      IsParallelogram Geo C E L M ∧
      Geo.Parallel L A D B ∧
      Geo.Parallel M A C E

/-
Remaining geometric construction debt in Euclid I.47.

The three outward squares and all angle/noncollinearity data are now
proved separately.  This axiom records only the internal cut of the
square on BC:

* M lies strictly between B and C;
* L lies strictly between D and E;
* the line through A cuts the square into the two parallelograms
  LDBM and CELM;
* N is the crossing point of DC and ML.

This is the only part of the former monolithic `i47_diagram` which
remains provisional.
-/


/--
Full I.47 diagram reconstructed from the proved outward-square and
angle infrastructure, plus the remaining internal-cut construction.
-/
theorem i47_diagram
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
      Not (Collinear Geo C K B) := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy of the triangle.
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
  -- The three outward squares.
  --------------------------------------------------------------------

  rcases
      i47_outward_squares
        Geo A B C hABC with
    ⟨lBC, lAB, lAC,
      D, E, F, G, H, K,
      hBlBC, hClBC,
      hAlAB, hBlAB,
      hAlAC, hClAC,
      hSqBC, hSqAB, hSqAC,
      hOppDA, hOppEA,
      hOppGC, hOppFC,
      hOppHB, hOppKB⟩

  --------------------------------------------------------------------
  -- Straight extensions through A.
  --------------------------------------------------------------------

  have hGAC :
      Geo.Between G A C :=
    i47_square_AB_extension
      Geo
      A B C F G
      lAB
      hAB
      hAlAB
      hBlAB
      hSqAB
      hOppGC
      hRight

  have hHAB :
      Geo.Between H A B :=
    i47_square_AC_extension
      Geo
      A B C K H
      lAC
      hAC
      hAlAC
      hClAC
      hABC
      hSqAC
      hOppHB
      hRight

  --------------------------------------------------------------------
  -- Parallels induced by the two leg squares.
  --------------------------------------------------------------------

  have hParallelAC :
      Geo.Parallel A C B F :=
    i47_square_AB_parallel_AC
      Geo
      A B C F G
      hAC
      hSqAB
      hGAC

  have hParallelAB :
      Geo.Parallel A B C K :=
    i47_square_AC_parallel_AB
      Geo
      A B C K H
      hAB
      hSqAC
      hHAB

  --------------------------------------------------------------------
  -- Mixed noncollinearities at D and E.
  --------------------------------------------------------------------

  have hNCBAD :
      Not (Collinear Geo B A D) :=
    i47_noncollinear_BAD
      Geo
      A B C D E
      lBC
      hABC
      hRight
      hBlBC
      hSqBC
      hOppDA

  have hNCCAE :
      Not (Collinear Geo C A E) :=
    i47_noncollinear_CAE
      Geo
      A B C D E
      lBC
      hABC
      hRight
      hClBC
      hSqBC
      hOppEA

  --------------------------------------------------------------------
  -- The two remaining SAS nondegeneracy facts follow from parallels.
  --------------------------------------------------------------------

  rcases
      i47_parallel_noncollinearities
        Geo
        A B C F K
        hParallelAC
        hParallelAB with
    ⟨hNCBFC, hNCCKB⟩

  --------------------------------------------------------------------
  -- Euclid's two angle-addition steps.
  --------------------------------------------------------------------

  have hAngleB :
      Geo.AngleCongruent A B D F B C :=
    i47_angle_ABD_FBC
      Geo
      A B C D E F G
      lBC lAB
      hABC
      hBlBC
      hClBC
      hAlAB
      hBlAB
      hSqBC
      hSqAB
      hOppDA
      hOppFC
      hNCBAD
      hNCBFC

  have hAngleC :
      Geo.AngleCongruent A C E K C B :=
    i47_angle_ACE_KCB
      Geo
      A B C D E K H
      lBC lAC
      hABC
      hBlBC
      hClBC
      hAlAC
      hClAC
      hSqBC
      hSqAC
      hOppEA
      hOppKB
      hNCCAE
      hNCCKB

  --------------------------------------------------------------------
  -- The only remaining provisional construction: the internal cut.
  --------------------------------------------------------------------

  rcases
      i47_cut_core
        Geo
        A B C D E
        lBC
        hABC
        hRight
        hBlBC
        hClBC
        hSqBC
        hOppDA
        hOppEA with
    ⟨L, M, N,
      hBMC, hDLE, hDNC, hMNL,
      hParLDBM, hParCELM,
      hParallelLA, hParallelMA⟩

  --------------------------------------------------------------------
  -- Assemble the former i47_diagram package.
  --------------------------------------------------------------------

  exact
    ⟨D, E, F, G, H, K, L, M, N,
      hSqBC,
      hSqAB,
      hSqAC,
      hBMC,
      hDLE,
      hDNC,
      hMNL,
      hParLDBM,
      hParCELM,
      hParallelLA,
      hParallelMA,
      hParallelAC,
      hParallelAB,
      hAngleB,
      hAngleC,
      hNCBAD,
      hNCBFC,
      hNCCAE,
      hNCCKB⟩

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

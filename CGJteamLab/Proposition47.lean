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

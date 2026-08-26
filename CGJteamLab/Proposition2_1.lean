import CGJteamLab.HilbertRectangle

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A rectangle with an interior cut is exactly scissors-equal to the
sum of the two quadrilateral terms determined by the cut.

The underlying dissection theorem is already proved in Proposition I.47;
despite its historical name `i47_square_split`, it requires only the
parallelogram structure.
-/
theorem rectangle_split_scissorsEq
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M N : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDNC : Geo.Between D N C)
    (hMNL : Geo.Between M N L) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C E D)
      (hilbertParallelogramTerm Geo M L D B +
       hilbertParallelogramTerm Geo C E L M) := by

  exact
    i47_square_split
      Geo
      B C D E L M N
      hRect.1
      hBMC
      hDLE
      hDNC
      hMNL

/--
The right-hand piece of a rectangular cut is again a rectangle.

If B-M-C and C-E-L-M is a parallelogram, then the right angle BCE
of the original rectangle transports along the ray CB = CM.
-/
theorem rectangle_split_right
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C)
    (hPar : IsParallelogram Geo C E L M) :
    IsRectangle Geo M C E L := by

  --------------------------------------------------------------------
  -- Rotate the cut parallelogram:
  --
  --   C-E-L-M  ->  M-C-E-L.
  --------------------------------------------------------------------

  have hParMCEL :
      IsParallelogram Geo M C E L :=
    ⟨ParallelSymmetry
        Geo E L M C hPar.2,
      hPar.1⟩

  --------------------------------------------------------------------
  -- From B-M-C obtain C-M-B, hence CB and CM are the same ray.
  --------------------------------------------------------------------

  have hCMB :
      Geo.Between C M B :=
    (HilbertOrder.between_incidence
      B M C hBMC).2.2.2.2

  have hRayCMB :
      HilbertSameRay Geo C M B :=
    hilbert_sameRay_of_between
      Geo C M B hCMB

  have hRayCBM :
      HilbertSameRay Geo C B M :=
    hilbert_sameRay_symm
      Geo C M B hRayCMB

  --------------------------------------------------------------------
  -- Nondegeneracy of the old and new angles.
  --------------------------------------------------------------------

  have hNCWhole :=
    parallelogram_vertices_noncollinear
      Geo B C E D hRect.1

  have hBCE :
      Not (Collinear Geo B C E) :=
    hNCWhole.2.1

  have hNCRight :=
    parallelogram_vertices_noncollinear
      Geo M C E L hParMCEL

  have hMCE :
      Not (Collinear Geo M C E) :=
    hNCRight.2.1

  --------------------------------------------------------------------
  -- The angle BCE is literally the same angle as MCE.
  --------------------------------------------------------------------

  have hAngleEq :
      Geo.Angle B C E =
      Geo.Angle M C E :=
    hilbert_angle_eq_of_sameRay_first
      Geo C B M E hRayCBM

  have hRefl :
      Geo.AngleCongruent
        B C E
        B C E :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      B C E
      hBCE

  have hCong :
      Geo.AngleCongruent
        B C E
        M C E := by
    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [← hAngleEq]
    exact hRefl

  --------------------------------------------------------------------
  -- Transport rightness.
  --------------------------------------------------------------------

  have hRightMCE :
      HilbertRightAngle Geo M C E :=
    hilbert_right_angle_transport
      Geo
      B C E
      M C E
      hBCE
      hMCE
      hRect.2
      hCong

  exact
    ⟨hParMCEL, hRightMCE⟩

/--
The left-hand piece of a rectangular cut is again a rectangle.

The right angle of the original rectangle is propagated around the
original parallelogram to the vertex B. Since B-M-C, the ray BM is
the same as the ray BC. The resulting right angle DBM then propagates
to BML inside the left cut parallelogram.
-/
theorem rectangle_split_left
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C)
    (hPar : IsParallelogram Geo L D B M) :
    IsRectangle Geo B M L D := by

  --------------------------------------------------------------------
  -- Rotate the left cut parallelogram:
  --
  --   L-D-B-M  ->  B-M-L-D.
  --------------------------------------------------------------------

  have hParBMLD :
      IsParallelogram Geo B M L D :=
    ⟨ParallelSymmetry
        Geo L D B M hPar.1,
      ParallelSymmetry
        Geo D B M L hPar.2⟩

  --------------------------------------------------------------------
  -- Propagate the right angle of the whole rectangle around its
  -- vertices:
  --
  --   BCE -> CED -> EDB -> DBC.
  --------------------------------------------------------------------

  have hParCEDB :
      IsParallelogram Geo C E D B :=
    ⟨hRect.1.2,
      ParallelSymmetry
        Geo B C E D hRect.1.1⟩

  have hRightCED :
      HilbertRightAngle Geo C E D :=
    parallelogram_adjacent_right_angle
      Geo C E D B
      hParCEDB
      hRect.2

  have hParEDBC :
      IsParallelogram Geo E D B C :=
    ⟨hParCEDB.2,
      ParallelSymmetry
        Geo C E D B hParCEDB.1⟩

  have hRightEDB :
      HilbertRightAngle Geo E D B :=
    parallelogram_adjacent_right_angle
      Geo E D B C
      hParEDBC
      hRightCED

  have hParDBCE :
      IsParallelogram Geo D B C E :=
    ⟨hParEDBC.2,
      ParallelSymmetry
        Geo E D B C hParEDBC.1⟩

  have hRightDBC :
      HilbertRightAngle Geo D B C :=
    parallelogram_adjacent_right_angle
      Geo D B C E
      hParDBCE
      hRightEDB

  --------------------------------------------------------------------
  -- Since B-M-C, BM and BC are the same ray.
  --------------------------------------------------------------------

  have hRayBMC :
      HilbertSameRay Geo B M C :=
    hilbert_sameRay_of_between
      Geo B M C hBMC

  have hRayBCM :
      HilbertSameRay Geo B C M :=
    hilbert_sameRay_symm
      Geo B M C hRayBMC

  --------------------------------------------------------------------
  -- Transport the right angle DBC to DBM.
  --------------------------------------------------------------------

  have hNCWhole :=
    parallelogram_vertices_noncollinear
      Geo B C E D hRect.1

  have hDBC :
      Not (Collinear Geo D B C) :=
    hNCWhole.1

  have hNCLeft :=
    parallelogram_vertices_noncollinear
      Geo B M L D hParBMLD

  have hDBM :
      Not (Collinear Geo D B M) :=
    hNCLeft.1

  have hAngleEq :
      Geo.Angle D B C =
      Geo.Angle D B M :=
    hilbert_angle_eq_of_sameRay_second
      Geo B D C M hRayBCM

  have hRefl :
      Geo.AngleCongruent
        D B C
        D B C :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      D B C
      hDBC

  have hCong :
      Geo.AngleCongruent
        D B C
        D B M := by
    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [← hAngleEq]
    exact hRefl

  have hRightDBM :
      HilbertRightAngle Geo D B M :=
    hilbert_right_angle_transport
      Geo
      D B C
      D B M
      hDBC
      hDBM
      hRightDBC
      hCong

  --------------------------------------------------------------------
  -- In B-M-L-D, the angle adjacent to DBM is BML.
  --------------------------------------------------------------------

  have hRightBML :
      HilbertRightAngle Geo B M L :=
    parallelogram_adjacent_right_angle
      Geo B M L D
      hParBMLD
      hRightDBM

  exact
    ⟨hParBMLD, hRightBML⟩

/--
A rectangle cut by a segment joining corresponding points on its
opposite sides is the scissors sum of the two resulting rectangles.

The output uses the natural Book II vertex order:

    D ----- L ----- E
    |       |       |
    |       |       |
    B ----- M ----- C

so the two pieces are `B M L D` and `M C E L`.
-/
theorem rectangle_split
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M N : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDNC : Geo.Between D N C)
    (hMNL : Geo.Between M N L)
    (hLeftPar : IsParallelogram Geo L D B M)
    (hRightPar : IsParallelogram Geo C E L M) :
    IsRectangle Geo B M L D /\
    IsRectangle Geo M C E L /\
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C E D)
      (hilbertParallelogramTerm Geo B M L D +
       hilbertParallelogramTerm Geo M C E L) := by

  --------------------------------------------------------------------
  -- The two pieces are rectangles.
  --------------------------------------------------------------------

  have hLeftRect :
      IsRectangle Geo B M L D :=
    rectangle_split_left
      Geo
      B C D E L M
      hRect
      hBMC
      hLeftPar

  have hRightRect :
      IsRectangle Geo M C E L :=
    rectangle_split_right
      Geo
      B C D E L M
      hRect
      hBMC
      hRightPar

  --------------------------------------------------------------------
  -- Existing exact dissection from I.47:
  --
  --   BCED = MLDB + CELM.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo M L D B +
         hilbertParallelogramTerm Geo C E L M) :=
    rectangle_split_scissorsEq
      Geo
      B C D E L M N
      hRect
      hBMC
      hDLE
      hDNC
      hMNL

  --------------------------------------------------------------------
  -- Normalize the left term:
  --
  --   MLDB -> BMLD.
  --------------------------------------------------------------------

  have hParMLDB :
      IsParallelogram Geo M L D B :=
    ⟨ParallelSymmetry
        Geo D B M L hLeftPar.2,
      hLeftPar.1⟩

  have hLeftRotate :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M L D B)
        (hilbertParallelogramTerm Geo B M L D) :=
    parallelogram_term_rotateOne
      Geo M L D B hParMLDB

  --------------------------------------------------------------------
  -- Normalize the right term:
  --
  --   CELM -> MCEL.
  --------------------------------------------------------------------

  have hRightRotate :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo C E L M)
        (hilbertParallelogramTerm Geo M C E L) :=
    parallelogram_term_rotateOne
      Geo C E L M hRightPar

  have hPiecesRotate :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M L D B +
         hilbertParallelogramTerm Geo C E L M)
        (hilbertParallelogramTerm Geo B M L D +
         hilbertParallelogramTerm Geo M C E L) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hLeftRotate
      hRightRotate

  have hFinal :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo B M L D +
         hilbertParallelogramTerm Geo M C E L) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hSplit
      hPiecesRotate

  exact
    ⟨hLeftRect,
      hRightRect,
      hFinal⟩

/--
Three-part additivity of a rectangle.

This is the concrete three-segment form of the scissors identity
underlying Euclid II.1.

The rectangle B-C-E-D is first cut at M-L, and the remaining
rectangle M-C-E-L is then cut at N-K.

    D ----- L ----- K ----- E
    |       |       |       |
    |       |       |       |
    B ----- M ----- N ----- C
-/
theorem rectangle_split_three
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M K N X Y : Geo.Point)
    (hRect : IsRectangle Geo B C E D)

    -- First cut: M-L.
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDXC : Geo.Between D X C)
    (hMXL : Geo.Between M X L)
    (hLeftPar :
      IsParallelogram Geo L D B M)
    (hRightPar :
      IsParallelogram Geo C E L M)

    -- Second cut: N-K inside the right-hand rectangle.
    (hMNC : Geo.Between M N C)
    (hLKE : Geo.Between L K E)
    (hLYC : Geo.Between L Y C)
    (hNYK : Geo.Between N Y K)
    (hMiddlePar :
      IsParallelogram Geo K L M N)
    (hFinalPar :
      IsParallelogram Geo C E K N) :
    IsRectangle Geo B M L D /\
    IsRectangle Geo M N K L /\
    IsRectangle Geo N C E K /\
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C E D)
      (hilbertParallelogramTerm Geo B M L D +
       (hilbertParallelogramTerm Geo M N K L +
        hilbertParallelogramTerm Geo N C E K)) := by

  --------------------------------------------------------------------
  -- First binary split:
  --
  --   BCED = BMLD + MCEL.
  --------------------------------------------------------------------

  have hFirst :=
    rectangle_split
      Geo
      B C D E L M X
      hRect
      hBMC
      hDLE
      hDXC
      hMXL
      hLeftPar
      hRightPar

  have hLeftRect :
      IsRectangle Geo B M L D :=
    hFirst.1

  have hRemainingRect :
      IsRectangle Geo M C E L :=
    hFirst.2.1

  have hFirstEq :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo B M L D +
         hilbertParallelogramTerm Geo M C E L) :=
    hFirst.2.2

  --------------------------------------------------------------------
  -- Second binary split:
  --
  --   MCEL = MNKL + NCEK.
  --------------------------------------------------------------------

  have hSecond :=
    rectangle_split
      Geo
      M C L E K N Y
      hRemainingRect
      hMNC
      hLKE
      hLYC
      hNYK
      hMiddlePar
      hFinalPar

  have hMiddleRect :
      IsRectangle Geo M N K L :=
    hSecond.1

  have hFinalRect :
      IsRectangle Geo N C E K :=
    hSecond.2.1

  have hSecondEq :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M C E L)
        (hilbertParallelogramTerm Geo M N K L +
         hilbertParallelogramTerm Geo N C E K) :=
    hSecond.2.2

  --------------------------------------------------------------------
  -- Add the unchanged left rectangle to the second split.
  --------------------------------------------------------------------

  have hLifted :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B M L D +
         hilbertParallelogramTerm Geo M C E L)
        (hilbertParallelogramTerm Geo B M L D +
         (hilbertParallelogramTerm Geo M N K L +
          hilbertParallelogramTerm Geo N C E K)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo B M L D))
      hSecondEq

  --------------------------------------------------------------------
  -- Compose the two exact dissections.
  --------------------------------------------------------------------

  have hFinalEq :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E D)
        (hilbertParallelogramTerm Geo B M L D +
         (hilbertParallelogramTerm Geo M N K L +
          hilbertParallelogramTerm Geo N C E K)) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hFirstEq
      hLifted

  exact
    ⟨hLeftRect,
      hMiddleRect,
      hFinalRect,
      hFinalEq⟩

/--
The three-part rectangle split expressed in Euclid's
"rectangle contained by" language.

The side C-E of the original rectangle represents the fixed segment P-Q.
The divided side B-C is split into B-M, M-N, and N-C.
-/
theorem rectangle_split_three_contained_by
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E L M K N X Y P Q : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hCE_PQ : Geo.Congruent C E P Q)

    -- First cut.
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDXC : Geo.Between D X C)
    (hMXL : Geo.Between M X L)
    (hLeftPar :
      IsParallelogram Geo L D B M)
    (hRightPar :
      IsParallelogram Geo C E L M)

    -- Second cut.
    (hMNC : Geo.Between M N C)
    (hLKE : Geo.Between L K E)
    (hLYC : Geo.Between L Y C)
    (hNYK : Geo.Between N Y K)
    (hMiddlePar :
      IsParallelogram Geo K L M N)
    (hFinalPar :
      IsParallelogram Geo C E K N) :
    IsRectangleContainedBy Geo
      B C E D B C P Q /\
    IsRectangleContainedBy Geo
      B M L D B M P Q /\
    IsRectangleContainedBy Geo
      M N K L M N P Q /\
    IsRectangleContainedBy Geo
      N C E K N C P Q /\
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C E D)
      (hilbertParallelogramTerm Geo B M L D +
       (hilbertParallelogramTerm Geo M N K L +
        hilbertParallelogramTerm Geo N C E K)) := by

  rcases
      rectangle_split_three
        Geo
        B C D E L M K N X Y
        hRect
        hBMC
        hDLE
        hDXC
        hMXL
        hLeftPar
        hRightPar
        hMNC
        hLKE
        hLYC
        hNYK
        hMiddlePar
        hFinalPar with
    ⟨hLeftRect,
      hMiddleRect,
      hFinalRect,
      hSplit⟩

  --------------------------------------------------------------------
  -- The whole rectangle is contained by BC and PQ.
  --------------------------------------------------------------------

  have hBC_BC :
      Geo.Congruent B C B C :=
    hilbert_congruent_reflexive Geo B C

  have hWholeContained :
      IsRectangleContainedBy Geo
        B C E D B C P Q :=
    ⟨hRect,
      hBC_BC,
      hCE_PQ⟩

  --------------------------------------------------------------------
  -- Left piece: ML ~= CE ~= PQ.
  --------------------------------------------------------------------

  have hWholeSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hRect.1

  have hLeftSides :
      OppositeSidesCongruent Geo B M L D :=
    ParallelogramOppositeSidesCongruent
      Geo B M L D hLeftRect.1

  have hDB_CE :
      Geo.Congruent D B C E :=
    hilbert_congruent_symmetry
      Geo C E D B hWholeSides.2

  have hML_CE :
      Geo.Congruent M L C E :=
    hilbert_congruent_transitivity
      Geo M L D B C E
      hLeftSides.2
      hDB_CE

  have hML_PQ :
      Geo.Congruent M L P Q :=
    hilbert_congruent_transitivity
      Geo M L C E P Q
      hML_CE
      hCE_PQ

  have hBM_BM :
      Geo.Congruent B M B M :=
    hilbert_congruent_reflexive Geo B M

  have hLeftContained :
      IsRectangleContainedBy Geo
        B M L D B M P Q :=
    ⟨hLeftRect,
      hBM_BM,
      hML_PQ⟩

  --------------------------------------------------------------------
  -- Middle piece: NK ~= LM ~= CE ~= PQ.
  --------------------------------------------------------------------

  have hMiddleSides :
      OppositeSidesCongruent Geo M N K L :=
    ParallelogramOppositeSidesCongruent
      Geo M N K L hMiddleRect.1

  have hRightSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hRightPar

  have hLM_CE :
      Geo.Congruent L M C E :=
    hilbert_congruent_symmetry
      Geo C E L M hRightSides.1

  have hNK_CE :
      Geo.Congruent N K C E :=
    hilbert_congruent_transitivity
      Geo N K L M C E
      hMiddleSides.2
      hLM_CE

  have hNK_PQ :
      Geo.Congruent N K P Q :=
    hilbert_congruent_transitivity
      Geo N K C E P Q
      hNK_CE
      hCE_PQ

  have hMN_MN :
      Geo.Congruent M N M N :=
    hilbert_congruent_reflexive Geo M N

  have hMiddleContained :
      IsRectangleContainedBy Geo
        M N K L M N P Q :=
    ⟨hMiddleRect,
      hMN_MN,
      hNK_PQ⟩

  --------------------------------------------------------------------
  -- Final piece already has CE as its second side.
  --------------------------------------------------------------------

  have hNC_NC :
      Geo.Congruent N C N C :=
    hilbert_congruent_reflexive Geo N C

  have hFinalContained :
      IsRectangleContainedBy Geo
        N C E K N C P Q :=
    ⟨hFinalRect,
      hNC_NC,
      hCE_PQ⟩

  exact
    ⟨hWholeContained,
      hLeftContained,
      hMiddleContained,
      hFinalContained,
      hSplit⟩

/--
Euclid II.1, three-part form, independent of the concrete rectangle
representatives.

If BC is divided into BM, MN, NC, then for any rectangles contained by

  BC, PQ
  BM, PQ
  MN, PQ
  NC, PQ

the rectangle on BC,PQ is scissors-equal to the sum of the three
rectangles on the parts.

The auxiliary points D,E,L,K,X,Y belong only to one concrete geometric
realization of the dissection.  The conclusion is independent of that
realization.
-/
theorem euclid_proposition_2_1_three
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    -- Concrete dissection diagram.
    (B C D E L M K N X Y P Q : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hCE_PQ : Geo.Congruent C E P Q)

    -- First cut.
    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDXC : Geo.Between D X C)
    (hMXL : Geo.Between M X L)
    (hLeftPar :
      IsParallelogram Geo L D B M)
    (hRightPar :
      IsParallelogram Geo C E L M)

    -- Second cut.
    (hMNC : Geo.Between M N C)
    (hLKE : Geo.Between L K E)
    (hLYC : Geo.Between L Y C)
    (hNYK : Geo.Between N Y K)
    (hMiddlePar :
      IsParallelogram Geo K L M N)
    (hFinalPar :
      IsParallelogram Geo C E K N)

    -- Arbitrary representatives of the four rectangles.
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)
    (Z0 Z1 Z2 Z3 : Geo.Point)

    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 B C P Q)

    (hPart1 :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 B M P Q)

    (hPart2 :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 M N P Q)

    (hPart3 :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 N C P Q) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       (hilbertParallelogramTerm Geo W0 W1 W2 W3 +
        hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)) := by

  --------------------------------------------------------------------
  -- Concrete realization of II.1.
  --------------------------------------------------------------------

  rcases
      rectangle_split_three_contained_by
        Geo
        B C D E L M K N X Y P Q
        hRect
        hCE_PQ
        hBMC
        hDLE
        hDXC
        hMXL
        hLeftPar
        hRightPar
        hMNC
        hLKE
        hLYC
        hNYK
        hMiddlePar
        hFinalPar with
    ⟨hConcreteWhole,
      hConcrete1,
      hConcrete2,
      hConcrete3,
      hConcreteSplit⟩

  --------------------------------------------------------------------
  -- Replace the concrete whole rectangle by the arbitrary
  -- representative U0-U1-U2-U3.
  --------------------------------------------------------------------

  have hWholeToConcrete :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo B C E D) :=
    rectangle_contained_by_unique
      Geo
      U0 U1 U2 U3
      B C E D
      B C P Q
      hWhole
      hConcreteWhole

  --------------------------------------------------------------------
  -- Replace each concrete piece by an arbitrary representative
  -- of the same "rectangle contained by" pair.
  --------------------------------------------------------------------

  have hPart1Transport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B M L D)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3) :=
    rectangle_contained_by_unique
      Geo
      B M L D
      V0 V1 V2 V3
      B M P Q
      hConcrete1
      hPart1

  have hPart2Transport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M N K L)
        (hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    rectangle_contained_by_unique
      Geo
      M N K L
      W0 W1 W2 W3
      M N P Q
      hConcrete2
      hPart2

  have hPart3Transport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo N C E K)
        (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) :=
    rectangle_contained_by_unique
      Geo
      N C E K
      Z0 Z1 Z2 Z3
      N C P Q
      hConcrete3
      hPart3

  --------------------------------------------------------------------
  -- Transport the nested sum.
  --------------------------------------------------------------------

  have hTailTransport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M N K L +
         hilbertParallelogramTerm Geo N C E K)
        (hilbertParallelogramTerm Geo W0 W1 W2 W3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hPart2Transport
      hPart3Transport

  have hPartsTransport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B M L D +
         (hilbertParallelogramTerm Geo M N K L +
          hilbertParallelogramTerm Geo N C E K))
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         (hilbertParallelogramTerm Geo W0 W1 W2 W3 +
          hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hPart1Transport
      hTailTransport

  --------------------------------------------------------------------
  -- Arbitrary whole
  --   -> concrete whole
  --   -> concrete three-part sum
  --   -> arbitrary three-part sum.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hWholeToConcrete
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hConcreteSplit
        hPartsTransport)

/--
Two-part form of Euclid II.1, independent of concrete rectangle
representatives.

If B-M-C, then

  Rect(BC, PQ) = Rect(BM, PQ) + Rect(MC, PQ).
-/
theorem euclid_proposition_2_1_two
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    -- Concrete cut diagram.
    (B C D E L M X P Q : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hCE_PQ : Geo.Congruent C E P Q)

    (hBMC : Geo.Between B M C)
    (hDLE : Geo.Between D L E)
    (hDXC : Geo.Between D X C)
    (hMXL : Geo.Between M X L)
    (hLeftPar :
      IsParallelogram Geo L D B M)
    (hRightPar :
      IsParallelogram Geo C E L M)

    -- Arbitrary representatives.
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)

    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 B C P Q)

    (hPart1 :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 B M P Q)

    (hPart2 :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 M C P Q) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3) := by

  --------------------------------------------------------------------
  -- Concrete binary split.
  --------------------------------------------------------------------

  rcases
      rectangle_split
        Geo
        B C D E L M X
        hRect
        hBMC
        hDLE
        hDXC
        hMXL
        hLeftPar
        hRightPar with
    ⟨hLeftRect,
      hRightRect,
      hSplit⟩

  --------------------------------------------------------------------
  -- Package the concrete whole rectangle.
  --------------------------------------------------------------------

  have hBC_BC :
      Geo.Congruent B C B C :=
    hilbert_congruent_reflexive Geo B C

  have hConcreteWhole :
      IsRectangleContainedBy Geo
        B C E D B C P Q :=
    ⟨hRect,
      hBC_BC,
      hCE_PQ⟩

  --------------------------------------------------------------------
  -- Package the concrete left rectangle.
  --
  -- In B-M-L-D, ML ~= DB.
  -- In B-C-E-D, CE ~= DB.
  -- Hence ML ~= CE ~= PQ.
  --------------------------------------------------------------------

  have hLeftSides :
      OppositeSidesCongruent Geo B M L D :=
    ParallelogramOppositeSidesCongruent
      Geo B M L D hLeftRect.1

  have hWholeSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hRect.1

  have hDB_CE :
      Geo.Congruent D B C E :=
    hilbert_congruent_symmetry
      Geo C E D B hWholeSides.2

  have hML_CE :
      Geo.Congruent M L C E :=
    hilbert_congruent_transitivity
      Geo M L D B C E
      hLeftSides.2
      hDB_CE

  have hML_PQ :
      Geo.Congruent M L P Q :=
    hilbert_congruent_transitivity
      Geo M L C E P Q
      hML_CE
      hCE_PQ

  have hBM_BM :
      Geo.Congruent B M B M :=
    hilbert_congruent_reflexive Geo B M

  have hConcrete1 :
      IsRectangleContainedBy Geo
        B M L D B M P Q :=
    ⟨hLeftRect,
      hBM_BM,
      hML_PQ⟩

  --------------------------------------------------------------------
  -- Package the concrete right rectangle.
  --------------------------------------------------------------------

  have hMC_MC :
      Geo.Congruent M C M C :=
    hilbert_congruent_reflexive Geo M C

  have hConcrete2 :
      IsRectangleContainedBy Geo
        M C E L M C P Q :=
    ⟨hRightRect,
      hMC_MC,
      hCE_PQ⟩

  --------------------------------------------------------------------
  -- Transport arbitrary representatives to/from the concrete diagram.
  --------------------------------------------------------------------

  have hWholeToConcrete :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo B C E D) :=
    rectangle_contained_by_unique
      Geo
      U0 U1 U2 U3
      B C E D
      B C P Q
      hWhole
      hConcreteWhole

  have hPart1Transport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B M L D)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3) :=
    rectangle_contained_by_unique
      Geo
      B M L D
      V0 V1 V2 V3
      B M P Q
      hConcrete1
      hPart1

  have hPart2Transport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo M C E L)
        (hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    rectangle_contained_by_unique
      Geo
      M C E L
      W0 W1 W2 W3
      M C P Q
      hConcrete2
      hPart2

  have hPartsTransport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B M L D +
         hilbertParallelogramTerm Geo M C E L)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hPart1Transport
      hPart2Transport

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hWholeToConcrete
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hSplit
        hPartsTransport)


end Geometry

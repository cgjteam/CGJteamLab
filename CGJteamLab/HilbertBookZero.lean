import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Definicje bazowe i relacje pomocnicze
------------------------------------------------------------------------

/--
Definicja relacji mniejszości odcinków: AB < CD.
-/
def HilbertSegmentLess
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) : Prop :=
  ∃ P : Geo.Point,
    Geo.Between C P D ∧
    Geo.Congruent A B C P

/--
Relacja przecięcia odcinków `CU A B C D E`.
Odcinki AB i CD przecinają się w punkcie E.
-/
def BookZeroCut
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (A B C D E F : Geo.Point) : Prop :=
  Geo.Between A E B ∧
  Geo.Between C E D ∧
  ¬ PrimCollinear Geo A B C ∧
  ¬ PrimCollinear Geo A B D

/--
Relacja kąta suplementarnego `SU A B C D F`.
-/
def BookZeroSupplement
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (A B C D F : Geo.Point) : Prop :=
  HilbertSameRay Geo B C D ∧
  Geo.Between A B F

/--
Kąt prosty w geometrii Hilberta.
-/
def HilbertRightAngle
    (Geo : Geometry.Geo)
    (A O B : Geo.Point) : Prop :=
  ∃ C : Geo.Point,
    Geo.Between A O C ∧
    Geo.AngleCongruent A O B B O C

------------------------------------------------------------------------
-- Book Zero: Prelinaria logiczne i własności przystawania
------------------------------------------------------------------------

theorem bookZero_equalitySymmetric
    (A B : Geo.Point)
    (h : B = A) :
    A = B := by
  exact h.symm

theorem bookZero_inequalitySymmetric
    (A B : Geo.Point)
    (h : A ≠ B) :
    B ≠ A := by
  intro hBA
  exact h hBA.symm

theorem bookZero_congruenceSymmetric
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by
  exact CongruentSymmetry Geo A B C D h

theorem bookZero_nullSegment3
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (hCong : Geo.Congruent A B C D) :
    C ≠ D := by
  intro hCD
  have hNull : Geo.Congruent A B C C := by
    simpa [hCD] using hCong
  have hEq : A = B :=
    bookZero_nullSegment1 Geo A B C hNull
  exact hAB hEq

theorem bookZero_congruenceTransitive
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (h1 : Geo.Congruent A B C D)
    (h2 : Geo.Congruent C D E F) :
    Geo.Congruent A B E F := by
  exact hilbert_congruent_transitivity Geo A B C D E F h1 h2

theorem bookZero_3_6a
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hACD : Geo.Between A C D) :
    Geo.Between B C D := by
  exact
    (hilbert_between_inner_trans
      Geo A B C D hABC hACD).1

theorem bookZero_betweenNotEqual
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    A ≠ B := by
  exact (HilbertOrder.between_incidence A B C hABC).1

theorem bookZero_extensionUnique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B E F : Geo.Point)
    (hABE : Geo.Between A B E)
    (hABF : Geo.Between A B F)
    (hBEBF : Geo.Congruent B E B F) :
    E = F := by
  have hABAB : Geo.Congruent A B A B :=
    hilbert_congruent_reflexive Geo A B
  have hAEAF : Geo.Congruent A E A F :=
    HilbertCongruence.segment_additivity
      (Geo := Geo) A B E A B F hABE hABF hABAB hBEBF
  have hRayE : HilbertSameRay Geo A B E :=
    hilbert_sameRay_of_between Geo A B E hABE
  have hRayF : HilbertSameRay Geo A B F :=
    hilbert_sameRay_of_between Geo A B F hABF
  exact
    hilbert_segment_construction_unique
      Geo A E A B E F hRayE hRayF
      (hilbert_congruent_reflexive Geo A E)
      (hilbert_congruent_symmetry Geo A E A F hAEAF)

theorem bookZero_3_7a
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D) :
    Geo.Between A C D := by
  exact
    (hilbert_between_outer_trans
      Geo A B C D hABC hBCD).1

theorem bookZero_3_5b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hBCD : Geo.Between B C D) :
    Geo.Between A C D := by
  have hDCB : Geo.Between D C B :=
    (HilbertOrder.between_incidence B C D hBCD).2.2.2.2
  have hDBA : Geo.Between D B A :=
    (HilbertOrder.between_incidence A B D hABD).2.2.2.2
  have hCBA : Geo.Between C B A :=
    (hilbert_between_inner_trans Geo D C B A hDCB hDBA).1
  have hABC : Geo.Between A B C :=
    (HilbertOrder.between_incidence C B A hCBA).2.2.2.2
  exact
    (hilbert_between_outer_trans Geo A B C D hABC hBCD).1

theorem bookZero_3_6b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hACD : Geo.Between A C D) :
    Geo.Between A B D := by
  exact
    (hilbert_between_inner_trans Geo A B C D hABC hACD).2

theorem bookZero_3_7b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D) :
    Geo.Between A B D := by
  exact
    (hilbert_between_outer_trans Geo A B C D hABC hBCD).2

theorem bookZero_doubleReverse
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent D C B A ∧
    Geo.Congruent B A D C := by
  have hBADC : Geo.Congruent B A D C :=
    CongruentReverseBoth Geo A B C D h
  have hDCBA : Geo.Congruent D C B A :=
    CongruentSymmetry Geo B A D C hBADC
  exact ⟨hDCBA, hBADC⟩

theorem bookZero_congruenceFlip
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent B A D C ∧
    Geo.Congruent B A C D ∧
    Geo.Congruent A B D C := by
  constructor
  · exact CongruentReverseBoth Geo A B C D h
  · constructor
    · exact CongruentReverseFirst Geo A B C D h
    · exact CongruentSwapSecond Geo A B C D h

theorem bookZero_sumOfParts
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABab : Geo.Congruent A B a b)
    (hBCbc : Geo.Congruent B C b c)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c) :
    Geo.Congruent A C a c := by
  exact
    HilbertCongruence.segment_additivity
      (Geo := Geo) A B C a b c hABC habc hABab hBCbc

------------------------------------------------------------------------
-- Operacje odejmowania odcinków i własności zaawansowane
------------------------------------------------------------------------

theorem hilbert_segment_subtraction
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c) :
    Geo.Congruent B C b c := by
  have hbc : b ≠ c :=
    (HilbertOrder.between_incidence a b c habc).2.1
  obtain ⟨X, hRayX, hBXBC⟩ :=
    HilbertCongruence.segment_construction (Geo := Geo) B C b c hbc
  have hSymmBetween :
      ∀ P Q R : Geo.Point, Geo.Between P Q R → Geo.Between R Q P :=
    fun P Q R h => (HilbertOrder.between_incidence P Q R h).2.2.2.2
  have habX : Geo.Between a b X := by
    rcases hilbert_sameRay_cases Geo b c X hRayX with hXc | hbcX | hbXc
    · subst X; exact habc
    · exact (hilbert_between_outer_trans Geo a b c X habc hbcX).2
    · have hcXb : Geo.Between c X b := hSymmBetween b X c hbXc
      have hcbA : Geo.Between c b a := hSymmBetween a b c habc
      have hXba : Geo.Between X b a :=
        (hilbert_between_inner_trans Geo c X b a hcXb hcbA).1
      exact hSymmBetween X b a hXba
  have hBCbX : Geo.Congruent B C b X :=
    hilbert_congruent_symmetry Geo b X B C hBXBC
  have hACaX : Geo.Congruent A C a X :=
    HilbertCongruence.segment_additivity (Geo := Geo) A B C a b X hABC habX hABab hBCbX
  have hRayAX : HilbertSameRay Geo a b X :=
    hilbert_sameRay_of_between Geo a b X habX
  have hRayAC : HilbertSameRay Geo a b c :=
    hilbert_sameRay_of_between Geo a b c habc
  have haXAC : Geo.Congruent a X A C :=
    hilbert_congruent_symmetry Geo A C a X hACaX
  have hacAC : Geo.Congruent a c A C :=
    hilbert_congruent_symmetry Geo A C a c hACac
  have hXc : X = c :=
    hilbert_segment_construction_unique Geo A C a b X c hRayAX hRayAC haXAC hacAC
  subst X
  exact hilbert_congruent_symmetry Geo b c B C hBXBC

theorem bookZero_differenceOfParts
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c) :
    Geo.Congruent B C b c := by
  exact
    hilbert_segment_subtraction
      Geo A B C a b c hABC habc hABab hACac

theorem bookZero_17_three_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Geo.Between a b c := by
  exact
    hilbert_theorem27_three_points
      Geo A B C a b c hABC hab hbc hac hABab hACac hBCbc

theorem bookZero_18_outerConnectivity
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hABD : Geo.Between A B D)
    (hNotBCD : ¬ Geo.Between B C D)
    (hNotBDC : ¬ Geo.Between B D C) :
    C = D := by
  by_contra hCD
  have hABCData := HilbertOrder.between_incidence A B C hABC
  have hABDData := HilbertOrder.between_incidence A B D hABD
  have hAB : A ≠ B := hABCData.1
  have hAC : A ≠ C := hABCData.2.2.1
  have hAD : A ≠ D := hABDData.2.2.1
  have hColACD : PrimCollinear Geo A C D := by
    rcases hABCData.2.2.2.1 with ⟨l, hAl, hBl, hCl⟩
    rcases hABDData.2.2.2.1 with ⟨m, hAm, hBm, hDm⟩
    have hlm : l = m := HilbertPlaneIncidence.line_unique A B hAB l m hAl hBl hAm hBm
    subst m; exact ⟨l, hAl, hCl, hDm⟩
  rcases hilbert_between_trichotomy Geo A C D hAC hCD hAD hColACD with hACD | hCAD | hADC
  · have hBCD := (hilbert_between_inner_trans Geo A B C D hABC hACD).1
    exact hNotBCD hBCD
  · have hCBA := hABCData.2.2.2.2
    have hBAD := (hilbert_between_inner_trans Geo C B A D hCBA hCAD).1
    have hColABD := hABDData.2.2.2.1
    have hNotBAD := (HilbertOrder.between_unique A B D hColABD hABD).1
    exact hNotBAD hBAD
  · have hBDC := (hilbert_between_inner_trans Geo A B D C hABD hADC).1
    exact hNotBDC hBDC

theorem bookZero_fiveLine_nondegenerate
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d)
    (hABD : ¬ Collinear Geo A B D) :
    Geo.Congruent C D c d := by
  have hSSS := HilbertSSS Geo A B D a b d hABD hAB hBD hAD
  have habd : ¬ Collinear Geo a b d := hSSS.1
  have hAngleABD : Geo.AngleCongruent A B D a b d := hSSS.2.angleB
  have hAngleDBC : Geo.AngleCongruent D B C d b c :=
    hilbert_adjacent_angles_congruent Geo A B D C a b d c hABC habc hABD habd hAngleABD
  have hAngleCBD : Geo.AngleCongruent C B D c b d :=
    AngleCongruentReverse Geo D B C d b c hAngleDBC
  have hCBD : ¬ Collinear Geo C B D := by
    intro hCBD
    have hABCcol : Collinear Geo A B C := (HilbertOrder.between_incidence A B C hABC).2.2.2.1
    have hBCne : B ≠ C := (HilbertOrder.between_incidence A B C hABC).2.1
    rcases hABCcol with ⟨l, hAl, hBl, hCl⟩
    rcases hCBD with ⟨m, hCm, hBm, hDm⟩
    have hlm : l = m := HilbertPlaneIncidence.line_unique B C hBCne l m hBl hCl hBm hCm
    subst m; exact hABD ⟨l, hAl, hBl, hDm⟩
  have hcbd : ¬ Collinear Geo c b d := by
    intro hcbd
    have habccol : Collinear Geo a b c := (HilbertOrder.between_incidence a b c habc).2.2.2.1
    have hbcne : b ≠ c := (HilbertOrder.between_incidence a b c habc).2.1
    rcases habccol with ⟨l, hal, hbl, hcl⟩
    rcases hcbd with ⟨m, hcm, hbm, hdm⟩
    have hlm : l = m := HilbertPlaneIncidence.line_unique b c hbcne l m hbl hcl hbm hcm
    subst m; exact habd ⟨l, hal, hbl, hdm⟩
  have hCBcb : Geo.Congruent C B c b := CongruentReverseBoth Geo B C b c hBC
  have hBCD : ¬ Collinear Geo B C D := by
    intro hBCDcol; exact hCBD (PrimCollinearSwap Geo B C D hBCDcol)
  have hbcd : ¬ Collinear Geo b c d := by
    intro hbcdcol; exact hcbd (PrimCollinearSwap Geo b c d hbcdcol)
  have hTriangles := SAS Geo B C D b c d hBCD hbcd hBC hAngleCBD hBD
  exact hTriangles.sideBC

theorem bookZero_collinearTriple_transfer
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B D a b d : Geo.Point)
    (hABDcol : Collinear Geo A B D)
    (hAB : Geo.Congruent A B a b)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d) :
    Collinear Geo a b d := by
  by_cases hABeq : A = B
  · subst B
    have habEq : a = b :=
      bookZero_nullSegment1 Geo a b A (hilbert_congruent_symmetry Geo A A a b hAB)
    subst b
    by_cases hadEq : a = d
    · subst d; rcases hilbert_line_through_point Geo a with ⟨l, hal⟩; exact ⟨l, hal, hal, hal⟩
    · rcases HilbertPlaneIncidence.line_through a d hadEq with ⟨l, hal, hdl⟩; exact ⟨l, hal, hal, hdl⟩
  · by_cases hADeq : A = D
    · subst D
      have hadEq : a = d :=
        bookZero_nullSegment1 Geo a d A (hilbert_congruent_symmetry Geo A A a d hAD)
      subst d
      by_cases habEq : a = b
      · subst b; rcases hilbert_line_through_point Geo a with ⟨l, hal⟩; exact ⟨l, hal, hal, hal⟩
      · rcases HilbertPlaneIncidence.line_through a b habEq with ⟨l, hal, hbl⟩; exact ⟨l, hal, hbl, hal⟩
    · by_cases hBDeq : B = D
      · subst D
        have hbdEq : b = d :=
          bookZero_nullSegment1 Geo b d B (hilbert_congruent_symmetry Geo B B b d hBD)
        subst d
        by_cases habEq : a = b
        · subst b; rcases hilbert_line_through_point Geo a with ⟨l, hal⟩; exact ⟨l, hal, hal, hal⟩
        · rcases HilbertPlaneIncidence.line_through a b habEq with ⟨l, hal, hbl⟩; exact ⟨l, hal, hbl, hbl⟩
      · have hab : a ≠ b := bookZero_nullSegment3 Geo A B a b hABeq hAB
        have had : a ≠ d := bookZero_nullSegment3 Geo A D a d hADeq hAD
        have hbd : b ≠ d := bookZero_nullSegment3 Geo B D b d hBDeq hBD
        rcases hilbert_between_trichotomy Geo A B D hABeq hBDeq hADeq hABDcol with hABD | hBAD | hADB
        · have habd : Geo.Between a b d :=
            bookZero_17_three_points Geo A B D a b d hABD hab hbd had hAB hAD hBD
          exact (HilbertOrder.between_incidence a b d habd).2.2.2.1
        · have hBAba : Geo.Congruent B A b a := CongruentReverseBoth Geo A B a b hAB
          have hBAbd : Geo.Congruent B D b d := hBD
          have hADad : Geo.Congruent A D a d := hAD
          have hbad : Geo.Between b a d :=
            bookZero_17_three_points Geo B A D b a d hBAD hab.symm had hbd hBAba hBAbd hADad
          have hbadCol : Collinear Geo b a d := (HilbertOrder.between_incidence b a d hbad).2.2.2.1
          exact PrimCollinearSwap Geo b a d hbadCol
        · have hDBdb : Geo.Congruent D B d b := CongruentReverseBoth Geo B D b d hBD
          have hadb : Geo.Between a d b :=
            bookZero_17_three_points Geo A D B a d b hADB had hbd.symm hab hAD hAB hDBdb
          have hadbCol : Collinear Geo a d b := (HilbertOrder.between_incidence a d b hadb).2.2.2.1
          exact PrimCollinearRotate Geo a d b hadbCol

theorem bookZero_fiveLine_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d)
    (hABDcol : Collinear Geo A B D) :
    Geo.Congruent C D c d := by
  have hABne : A ≠ B := (HilbertOrder.between_incidence A B C hABC).1
  have habne : a ≠ b := bookZero_nullSegment3 Geo A B a b hABne hAB
  by_cases hADeq : A = D
  · subst D
    have hadeq : a = d := bookZero_nullSegment1 Geo a d A (hilbert_congruent_symmetry Geo A A a d hAD)
    subst d
    have hACac : Geo.Congruent A C a c := bookZero_sumOfParts Geo A B C a b c hAB hBC hABC habc
    exact CongruentReverseBoth Geo A C a c hACac
  · by_cases hBDeq : B = D
    · subst D
      have hbdeq : b = d := bookZero_nullSegment1 Geo b d B (hilbert_congruent_symmetry Geo B B b d hBD)
      subst d
      exact CongruentReverseBoth Geo B C b c hBC
    · have habdCol : Collinear Geo a b d :=
        bookZero_collinearTriple_transfer Geo A B D a b d hABDcol hAB hAD hBD
      have hadne : a ≠ d := bookZero_nullSegment3 Geo A D a d hADeq hAD
      have hbdne : b ≠ d := bookZero_nullSegment3 Geo B D b d hBDeq hBD
      rcases hilbert_between_trichotomy Geo A B D hABne hBDeq hADeq hABDcol with hABD | hBAD | hADB
      · have habd : Geo.Between a b d :=
          bookZero_17_three_points Geo A B D a b d hABD habne hbdne hadne hAB hAD hBD
        by_cases hBCD : Geo.Between B C D
        · rcases HilbertOrder.between_extension b c ((HilbertOrder.between_incidence a b c habc).2.1) with ⟨r, hbcr⟩
          have hcr : c ≠ r := (HilbertOrder.between_incidence b c r hbcr).2.1
          rcases HilbertCongruence.segment_construction (Geo := Geo) C D c r hcr with ⟨e, hcre, hceCD⟩
          have hcbRay : HilbertSameRay Geo c b b := hilbert_sameRay_refl Geo c b ((HilbertOrder.between_incidence a b c habc).2.1)
          have hbce : Geo.Between b c e := hilbert_between_transport_sameRays Geo b c r b e hbcr hcbRay hcre
          have hCDce : Geo.Congruent C D c e := hilbert_congruent_symmetry Geo c e C D hceCD
          have hBDbe : Geo.Congruent B D b e := bookZero_sumOfParts Geo B C D b c e hBC hCDce hBCD hbce
          have hbed : Geo.Congruent b e b d :=
            hilbert_congruent_transitivity Geo b e B D b d (hilbert_congruent_symmetry Geo B D b e hBDbe) hBD
          have habe : Geo.Between a b e := bookZero_3_7b Geo a b c e habc hbce
          have hed : e = d := bookZero_extensionUnique Geo a b e d habe habd hbed
          subst e
          exact hilbert_congruent_symmetry Geo c d C D hceCD
        · by_cases hBDC : Geo.Between B D C
          · rcases HilbertOrder.between_extension b d hbdne with ⟨r, hbdr⟩
            have hdr : d ≠ r := (HilbertOrder.between_incidence b d r hbdr).2.1
            rcases HilbertCongruence.segment_construction (Geo := Geo) D C d r hdr with ⟨e, hdre, hdeDC⟩
            have hdbRay : HilbertSameRay Geo d b b := hilbert_sameRay_refl Geo d b hbdne
            have hbde : Geo.Between b d e := hilbert_between_transport_sameRays Geo b d r b e hbdr hdbRay hdre
            have hDCde : Geo.Congruent D C d e := hilbert_congruent_symmetry Geo d e D C hdeDC
            have hBCbe : Geo.Congruent B C b e := bookZero_sumOfParts Geo B D C b d e hBD hDCde hBDC hbde
            have hbebc : Geo.Congruent b e b c :=
              hilbert_congruent_transitivity Geo b e B C b c (hilbert_congruent_symmetry Geo B C b e hBCbe) hBC
            have habe : Geo.Between a b e := bookZero_3_7b Geo a b d e habd hbde
            have hec : e = c := bookZero_extensionUnique Geo a b e c habe habc hbebc
            subst e
            have hDCdc : Geo.Congruent D C d c := hilbert_congruent_symmetry Geo d c D C hdeDC
            exact CongruentReverseBoth Geo D C d c hDCdc
          · have hCD : C = D := bookZero_18_outerConnectivity Geo A B C D hABC hABD hBCD hBDC
            subst D
            have hbcbd : Geo.Congruent b c b d :=
              hilbert_congruent_transitivity Geo b c B C b d (hilbert_congruent_symmetry Geo B C b c hBC) hBD
            have hcd : c = d := bookZero_extensionUnique Geo a b c d habc habd hbcbd
            subst d
            exact bookZero_nullSegment2 Geo C c
      · have hBAba : Geo.Congruent B A b a := CongruentReverseBoth Geo A B a b hAB
        have hbad : Geo.Between b a d :=
          bookZero_17_three_points Geo B A D b a d hBAD habne.symm hadne hbdne hBAba hBD hAD
        have hDAB : Geo.Between D A B := (HilbertOrder.between_incidence B A D hBAD).2.2.2.2
        have hdab : Geo.Between d a b := (HilbertOrder.between_incidence b a d hbad).2.2.2.2
        have hDAda : Geo.Congruent D A d a := CongruentReverseBoth Geo A D a d hAD
        have hDBdb : Geo.Congruent D B d b := bookZero_sumOfParts Geo D A B d a b hDAda hAB hDAB hdab
        have hDBC : Geo.Between D B C := bookZero_3_7a Geo D A B C hDAB hABC
        have hdbc : Geo.Between d b c := bookZero_3_7a Geo d a b c hdab habc
        have hDCdc : Geo.Congruent D C d c := bookZero_sumOfParts Geo D B C d b c hDBdb hBC hDBC hdbc
        exact CongruentReverseBoth Geo D C d c hDCdc
      · have hDBdb : Geo.Congruent D B d b := CongruentReverseBoth Geo B D b d hBD
        have hadb : Geo.Between a d b :=
          bookZero_17_three_points Geo A D B a d b hADB hadne hbdne.symm habne hAD hAB hDBdb
        have hDBC : Geo.Between D B C := bookZero_3_6a Geo A D B C hADB hABC
        have hdbc : Geo.Between d b c := bookZero_3_6a Geo a d b c hadb habc
        have hDCdc : Geo.Congruent D C d c := bookZero_sumOfParts Geo D B C d b c hDBdb hBC hDBC hdbc
        exact CongruentReverseBoth Geo D C d c hDCdc

theorem bookZero_fiveLine
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d) :
    Geo.Congruent C D c d := by
  by_cases hABD : Collinear Geo A B D
  · exact bookZero_fiveLine_collinear Geo A B C a b c D d hABC habc hAB hBC hAD hBD hABD
  · exact bookZero_fiveLine_nondegenerate Geo A B C a b c D d hABC habc hAB hBC hAD hBD hABD

theorem bookZero_19_interior5
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hCD : Geo.Congruent C D c d) :
    Geo.Congruent B D b d := by
  have hCA : C ≠ A := (HilbertOrder.between_incidence A B C hABC).2.2.1.symm
  have hca : c ≠ a := (HilbertOrder.between_incidence a b c habc).2.2.1.symm
  rcases HilbertOrder.between_extension C A hCA with ⟨R, hCAR⟩
  have hAR : A ≠ R := (HilbertOrder.between_incidence C A R hCAR).2.1
  rcases HilbertCongruence.segment_construction (Geo := Geo) B C A R hAR with ⟨M, hRayM, hAMBC⟩
  have hRayC : HilbertSameRay Geo A C C := hilbert_sameRay_refl Geo A C hCA
  have hCAM : Geo.Between C A M := hilbert_between_transport_sameRays Geo C A R C M hCAR hRayC hRayM
  rcases HilbertOrder.between_extension c a hca with ⟨r, hcar⟩
  have har : a ≠ r := (HilbertOrder.between_incidence c a r hcar).2.1
  rcases HilbertCongruence.segment_construction (Geo := Geo) b c a r har with ⟨m, hRaym, hambc⟩
  have hRayc : HilbertSameRay Geo a c c := hilbert_sameRay_refl Geo a c hca
  have hcam : Geo.Between c a m := hilbert_between_transport_sameRays Geo c a r c m hcar hRayc hRaym
  have hbcam : Geo.Congruent b c a m := hilbert_congruent_symmetry Geo a m b c hambc
  have hAMbc : Geo.Congruent A M b c := hilbert_congruent_transitivity Geo A M B C b c hAMBC hBC
  have hAMam : Geo.Congruent A M a m := hilbert_congruent_transitivity Geo A M b c a m hAMbc hbcam
  have hAC : Geo.Congruent A C a c :=
    HilbertCongruence.segment_additivity (Geo := Geo) A B C a b c hABC habc hAB hBC
  have hCAca : Geo.Congruent C A c a :=
    hilbert_congruent_symmetry Geo c a C A (bookZero_doubleReverse Geo A C a c hAC).1
  have hMDmd : Geo.Congruent M D m d :=
    bookZero_fiveLine Geo C A M c a m D d hCAM hcam hCAca hAMam hCD hAD
  have hCBA : Geo.Between C B A := (HilbertOrder.between_incidence A B C hABC).2.2.2.2
  have hBAM : Geo.Between B A M := bookZero_3_6a Geo C B A M hCBA hCAM
  have hMAB : Geo.Between M A B := (HilbertOrder.between_incidence B A M hBAM).2.2.2.2
  have hcba : Geo.Between c b a := (HilbertOrder.between_incidence a b c habc).2.2.2.2
  have hbam : Geo.Between b a m := bookZero_3_6a Geo c b a m hcba hcam
  have hmab : Geo.Between m a b := (HilbertOrder.between_incidence b a m hbam).2.2.2.2
  have hMAma : Geo.Congruent M A m a :=
    hilbert_congruent_symmetry Geo m a M A (bookZero_doubleReverse Geo A M a m hAMam).1
  exact bookZero_fiveLine Geo M A B m a b D d hMAB hmab hMAma hAB hMDmd hAD

------------------------------------------------------------------------
-- Zakończenieprzestrzeni nazw Geometry
------------------------------------------------------------------------
end Geometry
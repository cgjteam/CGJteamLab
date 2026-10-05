import CGJteamLab.Proposition5_16
import CGJteamLab.Hilbert3DProportion
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.Proposition32
import CGJteamLab.PropositionHilbertIV

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid V.22

Production consolidation of V.22 in the Eudoxus, raw planar,
and spatial raw proportion languages.
-/

/- BEGIN raw planar V.22 support -/
/-!
# Hilbert Supplement II -- raw alternando and ex aequali

This development isolates the exact remaining circle/similarity kernel
needed by the angle-coded Hilbert proportion calculus.

The primitive input of this file is NOT an axiom declaration.  It is the
explicit proposition `HilbertCrossingRaysTransfer`:

  A,C on one ray from O,
  B,D on one ray from O,
  angle OAD ~= angle OBC
  --------------------------------
  angle ODC ~= angle OAB.

This is the corrected nondegenerate crossing-rays theorem identified in
the Hilbert/Pascal audit.  From it we derive, synthetically:

  raw alternando:
      a : b = c : d  ->  a : c = b : d

and then Hilbert's first combination rule / Euclid V.22:

      a : b = a' : b'
      b : c = b' : c'
      ----------------
      a : c = a' : c'.

No temporary axiom from `HilbertPascal.lean` is imported or used.
-/

------------------------------------------------------------------------
-- 1. The exact crossing-rays kernel still to be discharged.
------------------------------------------------------------------------

theorem hilbert_right_angle_swap_V22
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo B O A := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hRefl :
      Geo.AngleCongruent
        B O A
        B O A :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      B O A
      hBOA

  have hCong :
      Geo.AngleCongruent
        A O B
        B O A := by
    unfold Geometry.Geo.AngleCongruent at hRefl
    unfold Geometry.Geo.AngleCongruent
    rw [Geometry.Geo.angle_swap Geo A O B]
    exact hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      B O A
      hAOB
      hBOA
      hRight
      hCong


/--
A right angle is unchanged when both arms are replaced by points on
the same respective rays.

This is the generic planar form of the ray-transport lemma used in the
Book XI development.
-/
theorem hilbert_rightAngle_transport_sameRays_V22
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U O V X Y : Geo.Point)
    (hRight : HilbertRightAngle Geo U O V)
    (hUX : HilbertSameRay Geo O U X)
    (hVY : HilbertSameRay Geo O V Y) :
    HilbertRightAngle Geo X O Y := by

  rcases hRight with
    ⟨C, hUOC, hAngle⟩

  have hCO : Ne C O :=
    (HilbertOrder.between_incidence
      U O C hUOC).2.1.symm

  have hCC :
      HilbertSameRay Geo O C C :=
    hilbert_sameRay_refl
      Geo O C hCO

  have hXOC :
      Geo.Between X O C :=
    hilbert_between_transport_sameRays
      Geo
      U O C
      X C
      hUOC
      hUX
      hCC

  have hLeftFirst :
      Geo.Angle U O V =
      Geo.Angle X O V :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O U X V
      hUX

  have hLeftSecond :
      Geo.Angle X O V =
      Geo.Angle X O Y :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      O X V Y
      hVY

  have hRightFirst :
      Geo.Angle V O C =
      Geo.Angle Y O C :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O V Y C
      hVY

  have hAngle' :
      Geo.AngleCongruent
        X O Y
        Y O C := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢
    rw [← hLeftSecond, ← hLeftFirst, ← hRightFirst]
    exact hAngle

  exact
    ⟨C,
     hXOC,
     hAngle'⟩


/--
Two proper right triangles with one pair of corresponding acute angles
congruent have the other pair of acute angles congruent.

This is the clean version of the helper which had previously lived in
the quarantined segment-multiplication file.  The only subtraction step
is discharged by the production theorem
`hilbert_angleDecomposition_angle_subtraction_right`.
-/
theorem hilbert_right_triangle_third_angle_congruent_V22
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O A B O' A' B' : Geo.Point)
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B')
    (hNoncol : Not (PrimCollinear Geo O A B))
    (hNoncol' : Not (PrimCollinear Geo O' A' B'))
    (hAngleB :
      Geo.AngleCongruent
        A B O
        A' B' O') :
    Geo.AngleCongruent
      O A B
      O' A' B' := by

  have hAO : A ≠ O :=
    (hilbert_noncollinear_ne_first
      Geo O A B hNoncol).symm

  have hA'O' : A' ≠ O' :=
    (hilbert_noncollinear_ne_first
      Geo O' A' B' hNoncol').symm

  obtain ⟨C, hAOC⟩ :=
    HilbertOrder.between_extension
      A O hAO

  obtain ⟨C', hA'O'C'⟩ :=
    HilbertOrder.between_extension
      A' O' hA'O'

  have hBAO :
      Not (PrimCollinear Geo B A O) := by
    intro h
    exact
      hNoncol
        (PrimCollinearRotate
          Geo O B A
          (PrimCollinearSwap
            Geo B O A
            (PrimCollinearRotate
              Geo B A O h)))

  have hB'A'O' :
      Not (PrimCollinear Geo B' A' O') := by
    intro h
    exact
      hNoncol'
        (PrimCollinearRotate
          Geo O' B' A'
          (PrimCollinearSwap
            Geo B' O' A'
            (PrimCollinearRotate
              Geo B' A' O' h)))

  obtain
      ⟨R, hBRC, hPart1, hPart2⟩ :=
    euclid_proposition_32_exterior
      (Geo := Geo)
      B A O C
      hBAO
      hAOC

  obtain
      ⟨R', hB'R'C', hPart1', hPart2'⟩ :=
    euclid_proposition_32_exterior
      (Geo := Geo)
      B' A' O' C'
      hB'A'O'
      hA'O'C'

  have hNoncolAOB :
      Not (PrimCollinear Geo A O B) := by
    intro h
    exact
      hNoncol
        (PrimCollinearSwap
          Geo A O B h)

  have hNoncolA'O'B' :
      Not (PrimCollinear Geo A' O' B') := by
    intro h
    exact
      hNoncol'
        (PrimCollinearSwap
          Geo A' O' B' h)

  have hRightCong :
      Geo.AngleCongruent
        A O B
        A' O' B' :=
    hilbert_all_right_angles_congruent
      Geo
      A O B
      A' O' B'
      hNoncolAOB
      hNoncolA'O'B'
      hRight
      hRight'

  have hSupp :
      Geo.AngleCongruent
        B O C
        B' O' C' :=
    hilbert_adjacent_angles_congruent
      Geo
      A O B C
      A' O' B' C'
      hAOC
      hA'O'C'
      hNoncolAOB
      hNoncolA'O'B'
      hRightCong

  have hBOR_ABO :
      Geo.AngleCongruent
        B O R
        A B O :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B O
      B O R
      hPart1

  have hBOR_AngleB :
      Geo.AngleCongruent
        B O R
        A' B' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O R
      A B O
      A' B' O'
      hBOR_ABO
      hAngleB

  have hB'O'R'_ABO' :
      Geo.AngleCongruent
        B' O' R'
        A' B' O' :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A' B' O'
      B' O' R'
      hPart1'

  have hBOR_B'O'R' :
      Geo.AngleCongruent
        B O R
        B' O' R' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O R
      A' B' O'
      B' O' R'
      hBOR_AngleB
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B' O' R'
        A' B' O'
        hB'O'R'_ABO')

  have hOC : O ≠ C :=
    (HilbertOrder.between_incidence
      A O C hAOC).2.1

  have hACO :
      PrimCollinear Geo A C O :=
    PrimCollinearRotate
      Geo A O C
      (HilbertOrder.between_incidence
        A O C hAOC).2.2.2.1

  have hBOC :
      Not (PrimCollinear Geo B O C) := by
    intro h
    rcases h with
      ⟨l, hBl, hOl, hCl⟩
    rcases hACO with
      ⟨m, hAm, hCm, hOm⟩
    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        O C hOC
        l m
        hOl hCl
        hOm hCm
    exact
      hNoncol
        ⟨m,
         hOm,
         hAm,
         hlm ▸ hBl⟩

  have hO'C' : O' ≠ C' :=
    (HilbertOrder.between_incidence
      A' O' C' hA'O'C').2.1

  have hA'C'O' :
      PrimCollinear Geo A' C' O' :=
    PrimCollinearRotate
      Geo A' O' C'
      (HilbertOrder.between_incidence
        A' O' C' hA'O'C').2.2.2.1

  have hB'O'C' :
      Not (PrimCollinear Geo B' O' C') := by
    intro h
    rcases h with
      ⟨l, hB'l, hO'l, hC'l⟩
    rcases hA'C'O' with
      ⟨m, hA'm, hC'm, hO'm⟩
    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        O' C' hO'C'
        l m
        hO'l hC'l
        hO'm hC'm
    exact
      hNoncol'
        ⟨m,
         hO'm,
         hA'm,
         hlm ▸ hB'l⟩

  have hRO : R ≠ O := by
    intro h
    apply hBOC
    have hPrim :
        PrimCollinear Geo B R C :=
      (HilbertOrder.between_incidence
        B R C hBRC).2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hR'O' : R' ≠ O' := by
    intro h
    apply hB'O'C'
    have hPrim :
        PrimCollinear Geo B' R' C' :=
      (HilbertOrder.between_incidence
        B' R' C' hB'R'C').2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hRInside :
      HilbertRayMeetsSegment
        Geo O R B C :=
    ⟨R,
     hBRC,
     hilbert_sameRay_refl
       Geo O R hRO⟩

  have hR'Inside :
      HilbertRayMeetsSegment
        Geo O' R' B' C' :=
    ⟨R',
     hB'R'C',
     hilbert_sameRay_refl
       Geo O' R' hR'O'⟩

  have hCOR_C'O'R' :
      Geo.AngleCongruent
        C O R
        C' O' R' :=
    hilbert_angleDecomposition_angle_subtraction_right
      Geo
      O B C R
      B' O' C' R'
      hBOC
      hB'O'C'
      hRInside
      hR'Inside
      hSupp
      hBOR_B'O'R'

  have hROC_C'O'R' :
      Geo.AngleCongruent
        R O C
        C' O' R' :=
    (Geo.angle_congruent_reverse_first
      C O R
      C' O' R').mp
      hCOR_C'O'R'

  have hROC_R'O'C' :
      Geo.AngleCongruent
        R O C
        R' O' C' :=
    (Geo.angle_congruent_reverse_second
      R O C
      C' O' R').mp
      hROC_C'O'R'

  have hFinal1 :
      Geo.AngleCongruent
        B A O
        R' O' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A O
      R O C
      R' O' C'
      hPart2
      hROC_R'O'C'

  have hFinal2 :
      Geo.AngleCongruent
        B A O
        B' A' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A O
      R' O' C'
      B' A' O'
      hFinal1
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B' A' O'
        R' O' C'
        hPart2')

  have hFinal3 :
      Geo.AngleCongruent
        O A B
        B' A' O' :=
    (Geo.angle_congruent_reverse_first
      B A O
      B' A' O').mp
      hFinal2

  exact
    (Geo.angle_congruent_reverse_second
      O A B
      B' A' O').mp
      hFinal3


------------------------------------------------------------------------
-- 3. Raw alternando from the crossing-rays kernel.
------------------------------------------------------------------------

/--
Hilbert Supplement II alternando for the concrete angle-coded ratio:

    PQ : RS = UV : WX
    -----------------
    PQ : UV = RS : WX.

The proof follows Hilbert's cross-placement idea.

A representative of `UV` is laid off on the denominator ray of the
first ratio, and a representative of `WX` on its numerator ray.
The crossing-rays theorem supplies equality of the complementary
cross angles.  The clean right-triangle third-angle theorem then turns
that equality into the defining ratio angle for the alternated
proportion.
-/
theorem hilbertSegmentProportionRaw_alternando_of_crossing_V22
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (hCross :
      HilbertCrossingRaysTransfer
        (Geo := Geo))
    (P Q R S U V W X : Geo.Point)
    (h :
      HilbertSegmentProportionRaw
        Geo
        P Q R S
        U V W X) :
    HilbertSegmentProportionRaw
      Geo
      P Q U V
      R S W X := by

  rcases h with
    ⟨w1, w2, hAngle12⟩

  --------------------------------------------------------------------
  -- Lay c = UV on the denominator ray OA of w1.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        U V
        w1.O w1.A
        w1.hOA
    with
    ⟨C, hRayAC, hOC_UV⟩

  --------------------------------------------------------------------
  -- Lay d = WX on the numerator ray OB of w1.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        W X
        w1.O w1.B
        w1.hOB
    with
    ⟨D, hRayBD, hOD_WX⟩

  have hRayAA :
      HilbertSameRay Geo
        w1.O w1.A w1.A :=
    hilbert_sameRay_refl
      Geo
      w1.O w1.A
      w1.hOA.symm

  have hRayBB :
      HilbertSameRay Geo
        w1.O w1.B w1.B :=
    hilbert_sameRay_refl
      Geo
      w1.O w1.B
      w1.hOB.symm

  have hAOB :
      Not
        (PrimCollinear
          Geo w1.A w1.O w1.B) := by
    intro hCol
    exact
      w1.hNoncol
        (PrimCollinearSwap
          Geo w1.A w1.O w1.B hCol)

  have hBOA :
      Not
        (PrimCollinear
          Geo w1.B w1.O w1.A) := by
    intro hCol
    exact
      w1.hNoncol
        (PrimCollinearCycle
          Geo w1.B w1.O w1.A hCol)

  --------------------------------------------------------------------
  -- The copied legs give a genuine right-triangle witness for c:d.
  --------------------------------------------------------------------

  have hDOC :
      Not
        (PrimCollinear
          Geo D w1.O C) :=
    hilbert_noncollinear_of_sameRays
      Geo
      w1.B w1.O w1.A
      D C
      hBOA
      hRayBD
      hRayAC

  have hODC :
      Not
        (PrimCollinear
          Geo w1.O D C) := by
    intro hCol
    exact
      hDOC
        (PrimCollinearSwap
          Geo w1.O D C hCol)

  have hRightBOA :
      HilbertRightAngle
        Geo w1.B w1.O w1.A :=
    hilbert_right_angle_swap_V22
      (Geo := Geo)
      w1.A w1.O w1.B
      hAOB
      w1.hRight

  have hRightDOC :
      HilbertRightAngle
        Geo D w1.O C :=
    hilbert_rightAngle_transport_sameRays_V22
      (Geo := Geo)
      w1.B w1.O w1.A
      D C
      hRightBOA
      hRayBD
      hRayAC

  let wCD :
      HilbertSegmentRatioWitnessRaw
        Geo U V W X :=
    {
      O := w1.O
      A := D
      B := C
      hOA := hRayBD.2.1.symm
      hOB := hRayAC.2.1.symm
      hNoncol := hODC
      hRight := hRightDOC
      hNumerator := hOC_UV
      hDenominator := hOD_WX
    }

  have hW2_CD :
      Geo.AngleCongruent
        w2.O w2.A w2.B
        wCD.O wCD.A wCD.B :=
    hilbertSegmentRatioWitnessRaw_angle_congruent
      (Geo := Geo)
      U V W X
      w2 wCD

  have hAngle1_CD :
      Geo.AngleCongruent
        w1.O w1.A w1.B
        w1.O D C := by
    have hTmp :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        w1.O w1.A w1.B
        w2.O w2.A w2.B
        wCD.O wCD.A wCD.B
        hAngle12
        hW2_CD

    simpa [wCD] using hTmp

  --------------------------------------------------------------------
  -- Crossing-rays transfer.
  --
  -- Use A,C on the first ray and D,B on the second:
  --
  --   angle OAB ~= angle ODC
  --       ->
  --   angle OBC ~= angle OAD.
  --------------------------------------------------------------------

  have hAOD :
      Not
        (PrimCollinear
          Geo w1.A w1.O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      w1.A w1.O w1.B
      w1.A D
      hAOB
      hRayAA
      hRayBD

  have hRayDB :
      HilbertSameRay
        Geo w1.O D w1.B :=
    hilbert_sameRay_symm
      Geo
      w1.O w1.B D
      hRayBD

  have hCrossAngle :
      Geo.AngleCongruent
        w1.O w1.B C
        w1.O w1.A D :=
    hCross
      w1.O
      w1.A C
      D w1.B
      hAOD
      hRayAC
      hRayDB
      hAngle1_CD

  --------------------------------------------------------------------
  -- Build the two right triangles representing a:c and b:d.
  --------------------------------------------------------------------

  have hCOB :
      Not
        (PrimCollinear
          Geo C w1.O w1.B) :=
    hilbert_noncollinear_of_sameRays
      Geo
      w1.A w1.O w1.B
      C w1.B
      hAOB
      hRayAC
      hRayBB

  have hOCB :
      Not
        (PrimCollinear
          Geo w1.O C w1.B) := by
    intro hCol
    exact
      hCOB
        (PrimCollinearSwap
          Geo w1.O C w1.B hCol)

  have hDOA :
      Not
        (PrimCollinear
          Geo D w1.O w1.A) :=
    hilbert_noncollinear_of_sameRays
      Geo
      w1.B w1.O w1.A
      D w1.A
      hBOA
      hRayBD
      hRayAA

  have hODA :
      Not
        (PrimCollinear
          Geo w1.O D w1.A) := by
    intro hCol
    exact
      hDOA
        (PrimCollinearSwap
          Geo w1.O D w1.A hCol)

  have hRightCOB :
      HilbertRightAngle
        Geo C w1.O w1.B :=
    hilbert_rightAngle_transport_sameRays_V22
      (Geo := Geo)
      w1.A w1.O w1.B
      C w1.B
      w1.hRight
      hRayAC
      hRayBB

  have hRightDOA :
      HilbertRightAngle
        Geo D w1.O w1.A :=
    hilbert_rightAngle_transport_sameRays_V22
      (Geo := Geo)
      w1.B w1.O w1.A
      D w1.A
      hRightBOA
      hRayBD
      hRayAA

  let wAC :
      HilbertSegmentRatioWitnessRaw
        Geo P Q U V :=
    {
      O := w1.O
      A := C
      B := w1.B
      hOA := hRayAC.2.1.symm
      hOB := w1.hOB
      hNoncol := hOCB
      hRight := hRightCOB
      hNumerator := w1.hNumerator
      hDenominator := hOC_UV
    }

  let wBD :
      HilbertSegmentRatioWitnessRaw
        Geo R S W X :=
    {
      O := w1.O
      A := D
      B := w1.A
      hOA := hRayBD.2.1.symm
      hOB := w1.hOA
      hNoncol := hODA
      hRight := hRightDOA
      hNumerator := w1.hDenominator
      hDenominator := hOD_WX
    }

  --------------------------------------------------------------------
  -- The crossing angle is the equality of the *other* acute angles
  -- in these two right triangles.
  --------------------------------------------------------------------

  have hAtB1 :
      Geo.AngleCongruent
        C w1.B w1.O
        w1.O w1.A D :=
    (Geo.angle_congruent_reverse_first
      w1.O w1.B C
      w1.O w1.A D).mp
      hCrossAngle

  have hAtB :
      Geo.AngleCongruent
        C w1.B w1.O
        D w1.A w1.O :=
    (Geo.angle_congruent_reverse_second
      C w1.B w1.O
      w1.O w1.A D).mp
      hAtB1

  have hAlternatedAngle :
      Geo.AngleCongruent
        w1.O C w1.B
        w1.O D w1.A :=
    hilbert_right_triangle_third_angle_congruent_V22
      (Geo := Geo)
      w1.O C w1.B
      w1.O D w1.A
      hRightCOB
      hRightDOA
      hOCB
      hODA
      hAtB

  refine
    ⟨wAC, wBD, ?_⟩

  simpa [wAC, wBD] using hAlternatedAngle


------------------------------------------------------------------------
-- 4. Hilbert first combination rule / Euclid V.22.
------------------------------------------------------------------------

/--
Hilbert's first combination rule in the concrete raw ratio language.

From

    a : b = a' : b'
    b : c = b' : c'

we obtain

    a : c = a' : c'.

The proof is exactly Hilbert's Supplement II argument:

  alternando on the first proportion:
      a : a' = b : b'

  alternando on the second:
      b : b' = c : c'

  transitivity:
      a : a' = c : c'

  alternando once more:
      a : c = a' : c'.
-/
theorem hilbertSegmentProportionRaw_V22_of_crossing
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (hCross :
      HilbertCrossingRaysTransfer
        (Geo := Geo))
    (A0 A1 B0 B1 C0 C1 : Geo.Point)
    (Ap0 Ap1 Bp0 Bp1 Cp0 Cp1 : Geo.Point)
    (h1 :
      HilbertSegmentProportionRaw
        Geo
        A0 A1 B0 B1
        Ap0 Ap1 Bp0 Bp1)
    (h2 :
      HilbertSegmentProportionRaw
        Geo
        B0 B1 C0 C1
        Bp0 Bp1 Cp0 Cp1) :
    HilbertSegmentProportionRaw
      Geo
      A0 A1 C0 C1
      Ap0 Ap1 Cp0 Cp1 := by

  have h1Alt :
      HilbertSegmentProportionRaw
        Geo
        A0 A1 Ap0 Ap1
        B0 B1 Bp0 Bp1 :=
    hilbertSegmentProportionRaw_alternando_of_crossing_V22
      (Geo := Geo)
      hCross
      A0 A1 B0 B1
      Ap0 Ap1 Bp0 Bp1
      h1

  have h2Alt :
      HilbertSegmentProportionRaw
        Geo
        B0 B1 Bp0 Bp1
        C0 C1 Cp0 Cp1 :=
    hilbertSegmentProportionRaw_alternando_of_crossing_V22
      (Geo := Geo)
      hCross
      B0 B1 C0 C1
      Bp0 Bp1 Cp0 Cp1
      h2

  have hChain :
      HilbertSegmentProportionRaw
        Geo
        A0 A1 Ap0 Ap1
        C0 C1 Cp0 Cp1 :=
    hilbertSegmentProportionRaw_trans
      (Geo := Geo)
      A0 A1
      Ap0 Ap1
      B0 B1
      Bp0 Bp1
      C0 C1
      Cp0 Cp1
      h1Alt
      h2Alt

  exact
    hilbertSegmentProportionRaw_alternando_of_crossing_V22
      (Geo := Geo)
      hCross
      A0 A1 Ap0 Ap1
      C0 C1 Cp0 Cp1
      hChain
/- END raw planar V.22 support -/

/- BEGIN spatial raw V.22 support -/
/-!
# Hilbert Supplement II in ambient three-space

The planar raw alternando / V.22 block is already clean.  This file lifts
the same argument to the Book XI ambient-space ratio language without
installing a global planar Hilbert structure on `Geo`.

The only open input is the same corrected crossing-rays theorem, required
uniformly in every plane slice:

    forall pi, HilbertCrossingRaysTransfer (PlaneGeo Geo pi).

No new axiom is declared.
-/

------------------------------------------------------------------------
-- 1. Plane-wise crossing-rays kernel for ambient space.
------------------------------------------------------------------------

def HilbertSpaceCrossingRaysTransfer
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo] : Prop :=
  forall pi : S.Plane,
    HilbertCrossingRaysTransfer
      (Geo := PlaneGeo Geo pi)


------------------------------------------------------------------------
-- 2. Spatial raw alternando.
------------------------------------------------------------------------

/--
Spatial Hilbert Supplement II alternando.

The two spatial ratio witnesses may initially live in unrelated planes.
The proof chooses the carrier plane of the first witness, copies the two
legs of the second ratio onto the two rays of that first right triangle,
and performs Hilbert's crossing-rays argument entirely inside that
`PlaneGeo` slice.

Thus no global `HilbertOrder Geo` or `HilbertCongruence Geo` is installed.
-/
theorem hilbertSpaceSegmentProportionRaw_alternando_of_crossing
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (hCross :
      HilbertSpaceCrossingRaysTransfer
        (Geo := Geo))
    (P Q R T U V W X : Geo.Point)
    (h :
      HilbertSpaceSegmentProportionRaw
        Geo
        P Q R T
        U V W X) :
    HilbertSpaceSegmentProportionRaw
      Geo
      P Q U V
      R T W X := by

  rcases h with
    ⟨w1, w2, hAngle12⟩

  --------------------------------------------------------------------
  -- Carrier plane of the first right-triangle ratio witness.
  --------------------------------------------------------------------

  rcases
      HSI.plane_through
        w1.O w1.A w1.B
        w1.hNoncol
    with
    ⟨pi, hOpi, hApi, hBpi⟩

  --------------------------------------------------------------------
  -- Copy c = UV onto OA and d = WX onto OB.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        U V
        w1.O w1.A
        w1.hOA
    with
    ⟨C, hRayAC, hOC_UV⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        W X
        w1.O w1.B
        w1.hOB
    with
    ⟨D, hRayBD, hOD_WX⟩

  have hCpi :
      S.OnPlane C pi :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      pi
      w1.O w1.A C
      w1.hOA
      hOpi hApi
      hRayAC.2.2.1

  have hDpi :
      S.OnPlane D pi :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      pi
      w1.O w1.B D
      w1.hOB
      hOpi hBpi
      hRayBD.2.2.1

  --------------------------------------------------------------------
  -- PlaneGeo names.
  --------------------------------------------------------------------

  let Op : PlanePoint Geo pi :=
    ⟨w1.O, hOpi⟩

  let Ap : PlanePoint Geo pi :=
    ⟨w1.A, hApi⟩

  let Bp : PlanePoint Geo pi :=
    ⟨w1.B, hBpi⟩

  let Cp : PlanePoint Geo pi :=
    ⟨C, hCpi⟩

  let Dp : PlanePoint Geo pi :=
    ⟨D, hDpi⟩

  have hOpAp : Ne Op Ap := by
    intro hEq
    apply w1.hOA
    exact congrArg Subtype.val hEq

  have hOpBp : Ne Op Bp := by
    intro hEq
    apply w1.hOB
    exact congrArg Subtype.val hEq

  have hAOBp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Ap Op Bp) := by
    intro hCol
    apply w1.hNoncol
    exact
      PrimCollinearSwap
        Geo w1.A w1.O w1.B
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi
          Ap Op Bp
          hCol)

  have hBOAp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Bp Op Ap) := by
    intro hCol
    exact
      hAOBp
        (PrimCollinearSymm
          (PlaneGeo Geo pi)
          Bp Op Ap hCol)

  have hRightAOBp :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Ap Op Bp :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      pi
      Ap Op Bp).mpr
      w1.hRight

  have hRightBOAp :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Bp Op Ap :=
    hilbert_right_angle_swap_V22
      (Geo := PlaneGeo Geo pi)
      Ap Op Bp
      hAOBp
      hRightAOBp

  have hRayACp :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Ap Cp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi
        Op Ap Cp).mpr
    simpa [Op, Ap, Cp] using hRayAC

  have hRayBDp :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Bp Dp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi
        Op Bp Dp).mpr
    simpa [Op, Bp, Dp] using hRayBD

  have hRayAAp :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Ap Ap :=
    hilbert_sameRay_refl
      (PlaneGeo Geo pi)
      Op Ap
      hOpAp.symm

  have hRayBBp :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Bp Bp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo pi)
      Op Bp
      hOpBp.symm

  --------------------------------------------------------------------
  -- A copied ambient witness for c:d.
  --------------------------------------------------------------------

  have hDOCp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Dp Op Cp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo pi)
      Bp Op Ap
      Dp Cp
      hBOAp
      hRayBDp
      hRayACp

  have hODCp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Op Dp Cp) := by
    intro hCol
    exact
      hDOCp
        (PrimCollinearSwap
          (PlaneGeo Geo pi)
          Op Dp Cp hCol)

  have hRightDOCp :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Dp Op Cp :=
    hilbert_rightAngle_transport_sameRays_V22
      (Geo := PlaneGeo Geo pi)
      Bp Op Ap
      Dp Cp
      hRightBOAp
      hRayBDp
      hRayACp

  have hRightDOC :
      HilbertRightAngle
        Geo D w1.O C := by
    have h0 :=
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        pi
        Dp Op Cp).mp
        hRightDOCp
    simpa [Dp, Op, Cp] using h0

  have hODC :
      Not
        (PrimCollinear
          Geo w1.O D C) := by
    have h0 :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi
        Op Dp Cp
        hODCp
    simpa [Op, Dp, Cp] using h0

  let wCD :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo U V W X :=
    {
      O := w1.O
      A := D
      B := C
      hOA := hRayBD.2.1.symm
      hOB := hRayAC.2.1.symm
      hNoncol := hODC
      hRight := hRightDOC
      hNumerator := hOC_UV
      hDenominator := hOD_WX
    }

  have hW2_CD :
      Geo.AngleCongruent
        w2.O w2.A w2.B
        wCD.O wCD.A wCD.B :=
    hilbertSpaceSegmentRatioWitnessRaw_angle_congruent
      (Geo := Geo)
      U V W X
      w2 wCD

  have hAngle1_CD :
      Geo.AngleCongruent
        w1.O w1.A w1.B
        w1.O D C := by
    have h0 :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        w1.O w1.A w1.B
        w2.O w2.A w2.B
        wCD.O wCD.A wCD.B
        hAngle12
        hW2_CD

    simpa [wCD] using h0

  have hAngle1_CD_plane :
      (PlaneGeo Geo pi).AngleCongruent
        Op Ap Bp
        Op Dp Cp := by
    apply
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi
        Op Ap Bp
        Op Dp Cp).mpr
    simpa [Op, Ap, Bp, Dp, Cp] using hAngle1_CD

  --------------------------------------------------------------------
  -- Hilbert crossing-rays transfer inside this one PlaneGeo.
  --------------------------------------------------------------------

  have hAODp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Ap Op Dp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo pi)
      Ap Op Bp
      Ap Dp
      hAOBp
      hRayAAp
      hRayBDp

  have hRayDBp :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Dp Bp :=
    hilbert_sameRay_symm
      (PlaneGeo Geo pi)
      Op Bp Dp
      hRayBDp

  have hCrossAnglePlane :
      (PlaneGeo Geo pi).AngleCongruent
        Op Bp Cp
        Op Ap Dp :=
    (hCross pi)
      Op
      Ap Cp
      Dp Bp
      hAODp
      hRayACp
      hRayDBp
      hAngle1_CD_plane

  --------------------------------------------------------------------
  -- The two alternated right triangles:
  --
  --   C-O-B  represents a:c,
  --   D-O-A  represents b:d.
  --------------------------------------------------------------------

  have hCOBp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Cp Op Bp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo pi)
      Ap Op Bp
      Cp Bp
      hAOBp
      hRayACp
      hRayBBp

  have hOCBp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Op Cp Bp) := by
    intro hCol
    exact
      hCOBp
        (PrimCollinearSwap
          (PlaneGeo Geo pi)
          Op Cp Bp hCol)

  have hDOAp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Dp Op Ap) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo pi)
      Bp Op Ap
      Dp Ap
      hBOAp
      hRayBDp
      hRayAAp

  have hODAp :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Op Dp Ap) := by
    intro hCol
    exact
      hDOAp
        (PrimCollinearSwap
          (PlaneGeo Geo pi)
          Op Dp Ap hCol)

  have hRightCOBp :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Cp Op Bp :=
    hilbert_rightAngle_transport_sameRays_V22
      (Geo := PlaneGeo Geo pi)
      Ap Op Bp
      Cp Bp
      hRightAOBp
      hRayACp
      hRayBBp

  have hRightDOAp :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Dp Op Ap :=
    hilbert_rightAngle_transport_sameRays_V22
      (Geo := PlaneGeo Geo pi)
      Bp Op Ap
      Dp Ap
      hRightBOAp
      hRayBDp
      hRayAAp

  have hAtB1 :
      (PlaneGeo Geo pi).AngleCongruent
        Cp Bp Op
        Op Ap Dp :=
    ((PlaneGeo Geo pi).angle_congruent_reverse_first
      Op Bp Cp
      Op Ap Dp).mp
      hCrossAnglePlane

  have hAtB :
      (PlaneGeo Geo pi).AngleCongruent
        Cp Bp Op
        Dp Ap Op :=
    ((PlaneGeo Geo pi).angle_congruent_reverse_second
      Cp Bp Op
      Op Ap Dp).mp
      hAtB1

  have hAlternatedAnglePlane :
      (PlaneGeo Geo pi).AngleCongruent
        Op Cp Bp
        Op Dp Ap :=
    hilbert_right_triangle_third_angle_congruent_V22
      (Geo := PlaneGeo Geo pi)
      Op Cp Bp
      Op Dp Ap
      hRightCOBp
      hRightDOAp
      hOCBp
      hODAp
      hAtB

  have hAlternatedAngle :
      Geo.AngleCongruent
        w1.O C w1.B
        w1.O D w1.A := by
    have h0 :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi
        Op Cp Bp
        Op Dp Ap).mp
        hAlternatedAnglePlane
    simpa [Op, Cp, Bp, Dp, Ap] using h0

  --------------------------------------------------------------------
  -- Package the two spatial raw witnesses for the alternated ratio.
  --------------------------------------------------------------------

  have hOCB :
      Not
        (PrimCollinear
          Geo w1.O C w1.B) := by
    have h0 :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi
        Op Cp Bp
        hOCBp
    simpa [Op, Cp, Bp] using h0

  have hODA :
      Not
        (PrimCollinear
          Geo w1.O D w1.A) := by
    have h0 :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi
        Op Dp Ap
        hODAp
    simpa [Op, Dp, Ap] using h0

  have hRightCOB :
      HilbertRightAngle
        Geo C w1.O w1.B := by
    have h0 :=
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        pi
        Cp Op Bp).mp
        hRightCOBp
    simpa [Cp, Op, Bp] using h0

  have hRightDOA :
      HilbertRightAngle
        Geo D w1.O w1.A := by
    have h0 :=
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        pi
        Dp Op Ap).mp
        hRightDOAp
    simpa [Dp, Op, Ap] using h0

  let wAC :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo P Q U V :=
    {
      O := w1.O
      A := C
      B := w1.B
      hOA := hRayAC.2.1.symm
      hOB := w1.hOB
      hNoncol := hOCB
      hRight := hRightCOB
      hNumerator := w1.hNumerator
      hDenominator := hOC_UV
    }

  let wBD :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo R T W X :=
    {
      O := w1.O
      A := D
      B := w1.A
      hOA := hRayBD.2.1.symm
      hOB := w1.hOA
      hNoncol := hODA
      hRight := hRightDOA
      hNumerator := w1.hDenominator
      hDenominator := hOD_WX
    }

  refine
    ⟨wAC, wBD, ?_⟩

  simpa [wAC, wBD] using hAlternatedAngle


------------------------------------------------------------------------
-- 3. Spatial V.22 / Hilbert first combination rule.
------------------------------------------------------------------------

/--
Spatial Hilbert first combination rule / Euclid V.22.

This is the exact rule required by Euclid XI.27.
-/
theorem hilbertSpaceSegmentProportionRaw_V22_of_crossing
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (hCross :
      HilbertSpaceCrossingRaysTransfer
        (Geo := Geo))
    (A0 A1 B0 B1 C0 C1 : Geo.Point)
    (Ap0 Ap1 Bp0 Bp1 Cp0 Cp1 : Geo.Point)
    (h1 :
      HilbertSpaceSegmentProportionRaw
        Geo
        A0 A1 B0 B1
        Ap0 Ap1 Bp0 Bp1)
    (h2 :
      HilbertSpaceSegmentProportionRaw
        Geo
        B0 B1 C0 C1
        Bp0 Bp1 Cp0 Cp1) :
    HilbertSpaceSegmentProportionRaw
      Geo
      A0 A1 C0 C1
      Ap0 Ap1 Cp0 Cp1 := by

  have h1Alt :
      HilbertSpaceSegmentProportionRaw
        Geo
        A0 A1 Ap0 Ap1
        B0 B1 Bp0 Bp1 :=
    hilbertSpaceSegmentProportionRaw_alternando_of_crossing
      (Geo := Geo)
      hCross
      A0 A1 B0 B1
      Ap0 Ap1 Bp0 Bp1
      h1

  have h2Alt :
      HilbertSpaceSegmentProportionRaw
        Geo
        B0 B1 Bp0 Bp1
        C0 C1 Cp0 Cp1 :=
    hilbertSpaceSegmentProportionRaw_alternando_of_crossing
      (Geo := Geo)
      hCross
      B0 B1 C0 C1
      Bp0 Bp1 Cp0 Cp1
      h2

  have hChain :
      HilbertSpaceSegmentProportionRaw
        Geo
        A0 A1 Ap0 Ap1
        C0 C1 Cp0 Cp1 :=
    hilbertSpaceSegmentProportionRaw_trans
      (Geo := Geo)
      A0 A1
      Ap0 Ap1
      B0 B1
      Bp0 Bp1
      C0 C1
      Cp0 Cp1
      h1Alt
      h2Alt

  exact
    hilbertSpaceSegmentProportionRaw_alternando_of_crossing
      (Geo := Geo)
      hCross
      A0 A1 Ap0 Ap1
      C0 C1 Cp0 Cp1
      hChain
/- END spatial raw V.22 support -/

/- BEGIN closed raw V.22 theorems -/
/-!
# Hilbert Supplement II -- crossing rays, alternando, and V.22

Production closure of the crossing-rays block.

The development in `V22_crossing_block_v3` proves alternando and V.22
from the explicit interface `HilbertCrossingRaysTransfer`.
The circle development through stage 62 now proves that interface, so the
production theorems below have no remaining crossing hypothesis.
-/

theorem hilbertSegmentProportionRaw_alternando_V22
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (P Q R S U V W X : Geo.Point)
    (h :
      HilbertSegmentProportionRaw
        Geo
        P Q R S
        U V W X) :
    HilbertSegmentProportionRaw
      Geo
      P Q U V
      R S W X := by
  exact
    hilbertSegmentProportionRaw_alternando_of_crossing_V22
      (Geo := Geo)
      (hilbert_crossing_rays_transfer Geo)
      P Q R S U V W X
      h

/--
Hilbert's first combination rule / Euclid V.22.
-/
theorem hilbertSegmentProportionRaw_V22
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (A0 A1 B0 B1 C0 C1 : Geo.Point)
    (Ap0 Ap1 Bp0 Bp1 Cp0 Cp1 : Geo.Point)
    (h1 :
      HilbertSegmentProportionRaw
        Geo
        A0 A1 B0 B1
        Ap0 Ap1 Bp0 Bp1)
    (h2 :
      HilbertSegmentProportionRaw
        Geo
        B0 B1 C0 C1
        Bp0 Bp1 Cp0 Cp1) :
    HilbertSegmentProportionRaw
      Geo
      A0 A1 C0 C1
      Ap0 Ap1 Cp0 Cp1 := by
  exact
    hilbertSegmentProportionRaw_V22_of_crossing
      (Geo := Geo)
      (hilbert_crossing_rays_transfer Geo)
      A0 A1 B0 B1 C0 C1
      Ap0 Ap1 Bp0 Bp1 Cp0 Cp1
      h1 h2
/- END closed raw V.22 theorems -/

/- BEGIN Eudoxus V.22 -/
/-!
# Euclid V.22

Production formalization of Euclid, Book V, Proposition 22
(ex aequali / first combination rule) for the current Eudoxus
positive-segment proportion.

If

    a : b = a' : b'
    b : c = b' : c'

then

    a : c = a' : c'.

The proof follows Hilbert, Supplement II:

1. alternando on the first proportion:
       a : a' = b : b'
2. alternando on the second proportion:
       b : b' = c : c'
3. V.11:
       a : a' = c : c'
4. alternando:
       a : c = a' : c'.

No new proportion machinery is introduced here.
-/

/--
Euclid V.22 (ex aequali) for Eudoxus proportions.
-/
theorem euclid_proposition_5_22
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b c a' b' c' : HilbertPositiveSegmentClass Geo)
    (h1 :
      HilbertEudoxusProportion Geo a b a' b')
    (h2 :
      HilbertEudoxusProportion Geo b c b' c') :
    HilbertEudoxusProportion Geo a c a' c' := by

  have h1Alt :
      HilbertEudoxusProportion Geo a a' b b' :=
    euclid_proposition_5_16
      Geo a b a' b' h1

  have h2Alt :
      HilbertEudoxusProportion Geo b b' c c' :=
    euclid_proposition_5_16
      Geo b c b' c' h2

  have hChain :
      HilbertEudoxusProportion Geo a a' c c' :=
    euclid_proposition_5_11
      Geo
      a a'
      b b'
      c c'
      h1Alt
      h2Alt

  exact
    euclid_proposition_5_16
      Geo a a' c c' hChain
/- END Eudoxus V.22 -/

end Geometry

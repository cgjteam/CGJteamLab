import CGJteamLab.HilbertAngleSumComparison
import CGJteamLab.HilbertEqualRadiusChord
import CGJteamLab.HilbertSegmentSum
import CGJteamLab.Proposition20

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Equal-radius angle comparison and chord sums

Dimension-free lemmas used by Euclid XI.22.

This file starts with the two elementary branches of
`HilbertTwoAnglesGreaterThanAngle`:

1. the target angle is strictly smaller than the first summand;
2. the target angle is congruent to the first summand.

The decomposition branch is treated separately because it contains the
geometric core of XI.22.
-/

/--
If the target angle EQF is strictly smaller than AOB, and the two
angles are cut by equal radii, then the target chord EF is shorter
than AB. Since CD is a non-null chord of a proper second angle,

    AB + CD > EF.
-/
theorem hilbert_equalRadiusChordSum_of_first_greater
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hLess :
      HilbertAngleLess Geo E Q F A O B)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F) :
    HilbertSegmentSumGreater
      Geo
      A B
      C D
      E F := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hFirst
        (PrimCollinearSwap
          Geo O A B h)

  have hQEF :
      Not (PrimCollinear Geo Q E F) := by
    intro h
    exact
      hTarget
        (PrimCollinearSwap
          Geo Q E F h)

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q E
      hOA_QE

  have hQF_OA :
      Geo.Congruent Q F O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q F
      hOA_QF

  have hQF_OB :
      Geo.Congruent Q F O B :=
    hilbert_congruent_transitivity
      Geo
      Q F
      O A
      O B
      hQF_OA
      hOA_OB

  have hEF_AB :
      HilbertSegmentLess Geo E F A B :=
    hilbert_equalRadiusChord_less
      Geo
      Q E F
      O A B
      hQEF
      hOAB
      hQE_OA
      hQF_OB
      hLess

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo
      A B O
      (by
        intro h
        exact
          hFirst
            (PrimCollinearRotate
              Geo A B O h))

  have hCD :
      Not (C = D) :=
    hilbert_noncollinear_ne_first
      Geo
      C D P
      (by
        intro h
        exact
          hSecond
            (PrimCollinearRotate
              Geo C D P h))

  exact
    hilbertSegmentSumGreater_of_less_first
      Geo
      A B
      C D
      E F
      hAB
      hCD
      hEF_AB


/--
If the target angle EQF is congruent to AOB, and the two angles are
cut by equal radii, then the target chord EF is congruent to AB.
The proper second angle supplies a non-null chord CD, hence

    AB + CD > EF.
-/
theorem hilbert_equalRadiusChordSum_of_first_equal
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hEq :
      Geo.AngleCongruent E Q F A O B)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F) :
    HilbertSegmentSumGreater
      Geo
      A B
      C D
      E F := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hFirst
        (PrimCollinearSwap
          Geo O A B h)

  have hQEF :
      Not (PrimCollinear Geo Q E F) := by
    intro h
    exact
      hTarget
        (PrimCollinearSwap
          Geo Q E F h)

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q E
      hOA_QE

  have hQF_OA :
      Geo.Congruent Q F O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q F
      hOA_QF

  have hQF_OB :
      Geo.Congruent Q F O B :=
    hilbert_congruent_transitivity
      Geo
      Q F
      O A
      O B
      hQF_OA
      hOA_OB

  have hEF_AB :
      Geo.Congruent E F A B :=
    hilbert_equalRadiusChord_congruent
      Geo
      Q E F
      O A B
      hQEF
      hOAB
      hQE_OA
      hQF_OB
      hEq

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo
      A B O
      (by
        intro h
        exact
          hFirst
            (PrimCollinearRotate
              Geo A B O h))

  have hCD :
      Not (C = D) :=
    hilbert_noncollinear_ne_first
      Geo
      C D P
      (by
        intro h
        exact
          hSecond
            (PrimCollinearRotate
              Geo C D P h))

  exact
    hilbertSegmentSumGreater_of_congruent_first
      Geo
      A B
      C D
      E F
      hAB
      hCD
      hEF_AB


/--
Core of the decomposition branch.

The point R is already chosen on the interior ray QX at the common
radius. The additional hypothesis that E,R,F are noncollinear isolates
the only remaining geometric obligation in XI.22.

Under these assumptions:

* AB is congruent to ER;
* RF is strictly shorter than CD;
* I.20 in triangle ERF gives EF < ER + RF;
* additivity of strict segment comparison gives
  ER + RF < AB + CD.

Hence

    AB + CD > EF.
-/
theorem hilbert_equalRadiusChordSum_of_decomposition_core
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F X R : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hInside :
      HilbertRayMeetsSegment Geo Q X E F)
    (hFirstPart :
      Geo.AngleCongruent A O B E Q X)
    (hRemainder :
      HilbertAngleLess Geo X Q F C P D)
    (hRayQXR :
      HilbertSameRay Geo Q X R)
    (hQR_OA :
      Geo.Congruent Q R O A)
    (hERF :
      Not (PrimCollinear Geo E R F))
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F) :
    HilbertSegmentSumGreater
      Geo
      A B
      C D
      E F := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hFirst
        (PrimCollinearSwap
          Geo O A B h)

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact
      hSecond
        (PrimCollinearSwap
          Geo P C D h)

  have hEQX_less :
      HilbertAngleLess Geo E Q X E Q F :=
    hilbert_interior_angle_less
      Geo
      Q X E F
      hTarget
      hInside

  have hEQX :
      Not (PrimCollinear Geo E Q X) :=
    hEQX_less.1

  have hXQF :
      Not (PrimCollinear Geo X Q F) :=
    hRemainder.1

  have hQR :
      Not (Q = R) :=
    hRayQXR.2.1.symm

  have hQXR :
      PrimCollinear Geo Q X R :=
    hRayQXR.2.2.1

  have hQRX :
      PrimCollinear Geo Q R X :=
    PrimCollinearRotate
      Geo Q X R hQXR

  have hEQR :
      Not (PrimCollinear Geo E Q R) := by
    intro hEQRcol

    have hEQXcol :
        PrimCollinear Geo E Q X :=
      hilbert_primCollinear_trans
        Geo
        E Q R X
        hQR
        hEQRcol
        hQRX

    exact hEQX hEQXcol

  have hXQR :
      PrimCollinear Geo X Q R :=
    PrimCollinearSwap
      Geo Q X R hQXR

  have hRQF :
      Not (PrimCollinear Geo R Q F) := by
    intro hRQFcol

    have hQRFcol :
        PrimCollinear Geo Q R F :=
      PrimCollinearSwap
        Geo R Q F hRQFcol

    have hXQFcol :
        PrimCollinear Geo X Q F :=
      hilbert_primCollinear_trans
        Geo
        X Q R F
        hQR
        hXQR
        hQRFcol

    exact hXQF hXQFcol

  have hQER :
      Not (PrimCollinear Geo Q E R) := by
    intro h
    exact
      hEQR
        (PrimCollinearSwap
          Geo Q E R h)

  have hQRF :
      Not (PrimCollinear Geo Q R F) := by
    intro h
    exact
      hRQF
        (PrimCollinearSwap
          Geo Q R F h)

  have hEQX_eq_EQR :
      Geo.Angle E Q X =
      Geo.Angle E Q R :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      Q E X R
      hRayQXR

  have hFirstPartR :
      Geo.AngleCongruent A O B E Q R := by
    unfold Geometry.Geo.AngleCongruent
      at hFirstPart |-
    rw [<- hEQX_eq_EQR]
    exact hFirstPart

  have hXQF_eq_RQF :
      Geo.Angle X Q F =
      Geo.Angle R Q F :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      Q X R F
      hRayQXR

  have hRQF_XQF :
      Geo.AngleCongruent R Q F X Q F := by
    have hRefl :
        Geo.AngleCongruent X Q F X Q F :=
      Geometry.Geo.angle_congruent_reflexive
        Geo X Q F

    unfold Geometry.Geo.AngleCongruent
      at hRefl |-
    rw [<- hXQF_eq_RQF]
    exact hRefl

  have hRemainderR :
      HilbertAngleLess Geo R Q F C P D :=
    hilbert_angleLess_transport_left
      Geo
      X Q F
      R Q F
      C P D
      hRemainder
      hRQF
      hRQF_XQF

  have hOB_OA :
      Geo.Congruent O B O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      O B
      hOA_OB

  have hOA_QR :
      Geo.Congruent O A Q R :=
    hilbert_congruent_symmetry
      Geo
      Q R
      O A
      hQR_OA

  have hOB_QR :
      Geo.Congruent O B Q R :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      Q R
      hOB_OA
      hOA_QR

  have hAB_ER :
      Geo.Congruent A B E R :=
    hilbert_equalRadiusChord_congruent
      Geo
      O A B
      Q E R
      hOAB
      hQER
      hOA_QE
      hOB_QR
      hFirstPartR

  have hQR_PC :
      Geo.Congruent Q R P C :=
    hilbert_congruent_transitivity
      Geo
      Q R
      O A
      P C
      hQR_OA
      hOA_PC

  have hQF_OA :
      Geo.Congruent Q F O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q F
      hOA_QF

  have hQF_PD :
      Geo.Congruent Q F P D :=
    hilbert_congruent_transitivity
      Geo
      Q F
      O A
      P D
      hQF_OA
      hOA_PD

  have hRF_CD :
      HilbertSegmentLess Geo R F C D :=
    hilbert_equalRadiusChord_less
      Geo
      Q R F
      P C D
      hQRF
      hPCD
      hQR_PC
      hQF_PD
      hRemainderR

  have hREF :
      Not (PrimCollinear Geo R E F) := by
    intro h
    exact
      hERF
        (PrimCollinearSwap
          Geo R E F h)

  cases
      euclid_proposition_20
        Geo
        R E F
        hREF with
  | intro T hT =>

      have hERT :
          Geo.Between E R T :=
        hT.1

      have hRT_RF :
          Geo.Congruent R T R F :=
        hT.2.1

      have hEF_ET :
          HilbertSegmentLess Geo E F E T :=
        hT.2.2

      have hAB :
          Not (A = B) :=
        hilbert_noncollinear_ne_first
          Geo
          A B O
          (by
            intro h
            exact
              hFirst
                (PrimCollinearRotate
                  Geo A B O h))

      have hCD :
          Not (C = D) :=
        hilbert_noncollinear_ne_first
          Geo
          C D P
          (by
            intro h
            exact
              hSecond
                (PrimCollinearRotate
                  Geo C D P h))

      cases
          hilbert_segmentSum_witness
            Geo
            A B C D
            hAB
            hCD with
      | intro S hS =>

          have hABS :
              Geo.Between A B S :=
            hS.1

          have hBS_CD :
              Geo.Congruent B S C D :=
            hS.2

          have hRF_RT :
              Geo.Congruent R F R T :=
            hilbert_congruent_symmetry
              Geo
              R T
              R F
              hRT_RF

          have hRF_TR :
              Geo.Congruent R F T R :=
            CongruentSwapSecond
              Geo
              R F
              R T
              hRF_RT

          have hTR_CD :
              HilbertSegmentLess Geo T R C D :=
            bookZero_32_lessThanCongruence2
              Geo
              R F
              C D
              T R
              hRF_CD
              hRF_TR

          have hCD_BS :
              Geo.Congruent C D B S :=
            hilbert_congruent_symmetry
              Geo
              B S
              C D
              hBS_CD

          have hCD_SB :
              Geo.Congruent C D S B :=
            CongruentSwapSecond
              Geo
              C D
              B S
              hCD_BS

          have hTR_SB :
              HilbertSegmentLess Geo T R S B :=
            bookZero_30_lessThanCongruence
              Geo
              T R
              C D
              S B
              hTR_CD
              hCD_SB

          have hTRE :
              Geo.Between T R E :=
            (HilbertOrder.between_incidence
              E R T hERT).2.2.2.2

          have hSBA :
              Geo.Between S B A :=
            (HilbertOrder.between_incidence
              A B S hABS).2.2.2.2

          have hBA_RE :
              Geo.Congruent B A R E :=
            CongruentReverseBoth
              Geo
              A B
              E R
              hAB_ER

          have hRE_BA :
              Geo.Congruent R E B A :=
            hilbert_congruent_symmetry
              Geo
              B A
              R E
              hBA_RE

          have hTE_SA :
              HilbertSegmentLess Geo T E S A :=
            bookZero_53_lessThanAdditive
              Geo
              T R
              S B
              E A
              hTR_SB
              hTRE
              hSBA
              hRE_BA

          have hET_TE :
              Geo.Congruent E T T E :=
            CongruentSwapSecond
              Geo
              E T
              E T
              (hilbert_congruent_reflexive
                Geo E T)

          have hEF_TE :
              HilbertSegmentLess Geo E F T E :=
            bookZero_30_lessThanCongruence
              Geo
              E F
              E T
              T E
              hEF_ET
              hET_TE

          have hEF_SA :
              HilbertSegmentLess Geo E F S A :=
            bookZero_52_lessThanTransitive
              Geo
              E F
              T E
              S A
              hEF_TE
              hTE_SA

          have hSA_AS :
              Geo.Congruent S A A S :=
            CongruentReverseFirst
              Geo
              A S
              A S
              (hilbert_congruent_reflexive
                Geo A S)

          have hEF_AS :
              HilbertSegmentLess Geo E F A S :=
            bookZero_30_lessThanCongruence
              Geo
              E F
              S A
              A S
              hEF_SA
              hSA_AS

          exact
            Exists.intro S
              (And.intro hABS
                (And.intro hBS_CD hEF_AS))


/--
Collinear branch of the decomposition argument.

If R is collinear with E,F, then the interior-ray crossing forces
R itself to be the intersection point with the open segment EF.
Hence E-R-F.  Since AB ~= ER and RF < CD, strict additivity gives

    EF = ER + RF < AB + CD.
-/
theorem hilbert_chordSum_of_collinear_decomposition
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E Q F X R : Geo.Point)
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hInside :
      HilbertRayMeetsSegment Geo Q X E F)
    (hRayQXR :
      HilbertSameRay Geo Q X R)
    (hERFcol :
      PrimCollinear Geo E R F)
    (hAB_ER :
      Geo.Congruent A B E R)
    (hRF_CD :
      HilbertSegmentLess Geo R F C D)
    (hAB :
      Not (A = B))
    (hCD :
      Not (C = D)) :
    HilbertSegmentSumGreater
      Geo
      A B
      C D
      E F := by

  rcases hInside with
    ⟨H, hEHF, hRayQXH⟩

  have hEFQ :
      Not (PrimCollinear Geo E F Q) := by
    intro h
    exact
      hTarget
        (PrimCollinearRotate
          Geo E F Q h)

  have hEF :
      Not (E = F) :=
    hilbert_noncollinear_ne_first
      Geo
      E F Q
      hEFQ

  have hEHFcol :
      PrimCollinear Geo E H F :=
    (HilbertOrder.between_incidence
      E H F hEHF).2.2.2.1

  have hRH :
      R = H := by

    by_contra hRHne

    have hRayQRH :
        HilbertSameRay Geo Q R H :=
      hilbert_sameRay_of_common
        Geo
        Q X R H
        hRayQXR
        hRayQXH

    have hQRHcol :
        PrimCollinear Geo Q R H :=
      hRayQRH.2.2.1

    rcases hERFcol with
      ⟨l, hEl, hRl, hFl⟩

    have hHl :
        HilbertIncidence.OnLine H l :=
      hilbert_collinear_on_line
        Geo
        E F H
        l
        hEF
        hEl
        hFl
        (PrimCollinearRotate
          Geo E H F hEHFcol)

    rcases hQRHcol with
      ⟨m, hQm, hRm, hHm⟩

    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        R H
        hRHne
        l m
        hRl hHl
        hRm hHm

    have hQl :
        HilbertIncidence.OnLine Q l := by
      rw [hlm]
      exact hQm

    exact
      hTarget
        ⟨l, hEl, hQl, hFl⟩

  have hERF :
      Geo.Between E R F := by
    subst H
    exact hEHF

  cases
      hilbert_segmentSum_witness
        Geo
        A B C D
        hAB
        hCD with
  | intro S hS =>

      have hABS :
          Geo.Between A B S :=
        hS.1

      have hBS_CD :
          Geo.Congruent B S C D :=
        hS.2

      have hRF_FR :
          Geo.Congruent R F F R :=
        CongruentSwapSecond
          Geo
          R F
          R F
          (hilbert_congruent_reflexive
            Geo R F)

      have hFR_CD :
          HilbertSegmentLess Geo F R C D :=
        bookZero_32_lessThanCongruence2
          Geo
          R F
          C D
          F R
          hRF_CD
          hRF_FR

      have hCD_BS :
          Geo.Congruent C D B S :=
        hilbert_congruent_symmetry
          Geo
          B S
          C D
          hBS_CD

      have hCD_SB :
          Geo.Congruent C D S B :=
        CongruentSwapSecond
          Geo
          C D
          B S
          hCD_BS

      have hFR_SB :
          HilbertSegmentLess Geo F R S B :=
        bookZero_30_lessThanCongruence
          Geo
          F R
          C D
          S B
          hFR_CD
          hCD_SB

      have hFRE :
          Geo.Between F R E :=
        (HilbertOrder.between_incidence
          E R F hERF).2.2.2.2

      have hSBA :
          Geo.Between S B A :=
        (HilbertOrder.between_incidence
          A B S hABS).2.2.2.2

      have hBA_RE :
          Geo.Congruent B A R E :=
        CongruentReverseBoth
          Geo
          A B
          E R
          hAB_ER

      have hRE_BA :
          Geo.Congruent R E B A :=
        hilbert_congruent_symmetry
          Geo
          B A
          R E
          hBA_RE

      have hFE_SA :
          HilbertSegmentLess Geo F E S A :=
        bookZero_53_lessThanAdditive
          Geo
          F R
          S B
          E A
          hFR_SB
          hFRE
          hSBA
          hRE_BA

      have hFE_EF :
          Geo.Congruent F E E F :=
        CongruentSwapSecond
          Geo
          F E
          F E
          (hilbert_congruent_reflexive
            Geo F E)

      have hEF_SA :
          HilbertSegmentLess Geo E F S A :=
        bookZero_32_lessThanCongruence2
          Geo
          F E
          S A
          E F
          hFE_SA
          hFE_EF

      have hSA_AS :
          Geo.Congruent S A A S :=
        CongruentSwapSecond
          Geo
          S A
          S A
          (hilbert_congruent_reflexive
            Geo S A)

      have hEF_AS :
          HilbertSegmentLess Geo E F A S :=
        bookZero_30_lessThanCongruence
          Geo
          E F
          S A
          A S
          hEF_SA
          hSA_AS

      exact
        Exists.intro S
          (And.intro hABS
            (And.intro hBS_CD hEF_AS))


/--
Complete decomposition branch.

No noncollinearity assumption on E,R,F is required.

If E,R,F are noncollinear, use I.20.
If they are collinear, the crossing point lies between E and F and
strictness comes from replacing RF by the longer chord CD.
-/
theorem hilbert_equalRadiusChordSum_of_decomposition
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F X R : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hInside :
      HilbertRayMeetsSegment Geo Q X E F)
    (hFirstPart :
      Geo.AngleCongruent A O B E Q X)
    (hRemainder :
      HilbertAngleLess Geo X Q F C P D)
    (hRayQXR :
      HilbertSameRay Geo Q X R)
    (hQR_OA :
      Geo.Congruent Q R O A)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F) :
    HilbertSegmentSumGreater
      Geo
      A B
      C D
      E F := by

  by_cases hERFcol :
      PrimCollinear Geo E R F

  ·
    have hOAB :
        Not (PrimCollinear Geo O A B) := by
      intro h
      exact
        hFirst
          (PrimCollinearSwap
            Geo O A B h)

    have hPCD :
        Not (PrimCollinear Geo P C D) := by
      intro h
      exact
        hSecond
          (PrimCollinearSwap
            Geo P C D h)

    have hEQX_less :
        HilbertAngleLess Geo E Q X E Q F :=
      hilbert_interior_angle_less
        Geo
        Q X E F
        hTarget
        hInside

    have hEQX :
        Not (PrimCollinear Geo E Q X) :=
      hEQX_less.1

    have hXQF :
        Not (PrimCollinear Geo X Q F) :=
      hRemainder.1

    have hQR :
        Not (Q = R) :=
      hRayQXR.2.1.symm

    have hQXR :
        PrimCollinear Geo Q X R :=
      hRayQXR.2.2.1

    have hQRX :
        PrimCollinear Geo Q R X :=
      PrimCollinearRotate
        Geo Q X R hQXR

    have hEQR :
        Not (PrimCollinear Geo E Q R) := by
      intro hEQRcol

      have hEQXcol :
          PrimCollinear Geo E Q X :=
        hilbert_primCollinear_trans
          Geo
          E Q R X
          hQR
          hEQRcol
          hQRX

      exact hEQX hEQXcol

    have hXQR :
        PrimCollinear Geo X Q R :=
      PrimCollinearSwap
        Geo Q X R hQXR

    have hRQF :
        Not (PrimCollinear Geo R Q F) := by
      intro hRQFcol

      have hQRFcol :
          PrimCollinear Geo Q R F :=
        PrimCollinearSwap
          Geo R Q F hRQFcol

      have hXQFcol :
          PrimCollinear Geo X Q F :=
        hilbert_primCollinear_trans
          Geo
          X Q R F
          hQR
          hXQR
          hQRFcol

      exact hXQF hXQFcol

    have hQER :
        Not (PrimCollinear Geo Q E R) := by
      intro h
      exact
        hEQR
          (PrimCollinearSwap
            Geo Q E R h)

    have hQRF :
        Not (PrimCollinear Geo Q R F) := by
      intro h
      exact
        hRQF
          (PrimCollinearSwap
            Geo Q R F h)

    have hEQX_eq_EQR :
        Geo.Angle E Q X =
        Geo.Angle E Q R :=
      hilbert_angle_eq_of_sameRay_second
        Geo
        Q E X R
        hRayQXR

    have hFirstPartR :
        Geo.AngleCongruent A O B E Q R := by
      unfold Geometry.Geo.AngleCongruent
        at hFirstPart |-
      rw [<- hEQX_eq_EQR]
      exact hFirstPart

    have hXQF_eq_RQF :
        Geo.Angle X Q F =
        Geo.Angle R Q F :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        Q X R F
        hRayQXR

    have hRQF_XQF :
        Geo.AngleCongruent R Q F X Q F := by
      have hRefl :
          Geo.AngleCongruent X Q F X Q F :=
        Geometry.Geo.angle_congruent_reflexive
          Geo X Q F

      unfold Geometry.Geo.AngleCongruent
        at hRefl |-
      rw [<- hXQF_eq_RQF]
      exact hRefl

    have hRemainderR :
        HilbertAngleLess Geo R Q F C P D :=
      hilbert_angleLess_transport_left
        Geo
        X Q F
        R Q F
        C P D
        hRemainder
        hRQF
        hRQF_XQF

    have hOB_OA :
        Geo.Congruent O B O A :=
      hilbert_congruent_symmetry
        Geo
        O A
        O B
        hOA_OB

    have hOA_QR :
        Geo.Congruent O A Q R :=
      hilbert_congruent_symmetry
        Geo
        Q R
        O A
        hQR_OA

    have hOB_QR :
        Geo.Congruent O B Q R :=
      hilbert_congruent_transitivity
        Geo
        O B
        O A
        Q R
        hOB_OA
        hOA_QR

    have hAB_ER :
        Geo.Congruent A B E R :=
      hilbert_equalRadiusChord_congruent
        Geo
        O A B
        Q E R
        hOAB
        hQER
        hOA_QE
        hOB_QR
        hFirstPartR

    have hQR_PC :
        Geo.Congruent Q R P C :=
      hilbert_congruent_transitivity
        Geo
        Q R
        O A
        P C
        hQR_OA
        hOA_PC

    have hQF_OA :
        Geo.Congruent Q F O A :=
      hilbert_congruent_symmetry
        Geo
        O A
        Q F
        hOA_QF

    have hQF_PD :
        Geo.Congruent Q F P D :=
      hilbert_congruent_transitivity
        Geo
        Q F
        O A
        P D
        hQF_OA
        hOA_PD

    have hRF_CD :
        HilbertSegmentLess Geo R F C D :=
      hilbert_equalRadiusChord_less
        Geo
        Q R F
        P C D
        hQRF
        hPCD
        hQR_PC
        hQF_PD
        hRemainderR

    have hAB :
        Not (A = B) :=
      hilbert_noncollinear_ne_first
        Geo
        A B O
        (by
          intro h
          exact
            hFirst
              (PrimCollinearRotate
                Geo A B O h))

    have hCD :
        Not (C = D) :=
      hilbert_noncollinear_ne_first
        Geo
        C D P
        (by
          intro h
          exact
            hSecond
              (PrimCollinearRotate
                Geo C D P h))

    exact
      hilbert_chordSum_of_collinear_decomposition
        Geo
        A B C D
        E Q F X R
        hTarget
        hInside
        hRayQXR
        hERFcol
        hAB_ER
        hRF_CD
        hAB
        hCD

  ·
    exact
      hilbert_equalRadiusChordSum_of_decomposition_core
        Geo
        A O B
        C P D
        E Q F
        X R
        hFirst
        hSecond
        hTarget
        hInside
        hFirstPart
        hRemainder
        hRayQXR
        hQR_OA
        hERFcol
        hOA_OB
        hOA_PC
        hOA_PD
        hOA_QE
        hOA_QF


/--
Equal-radius chord-sum theorem for the synthetic angle-sum relation.

If

    angle AOB + angle CPD > angle EQF

in the witness-based sense of `HilbertTwoAnglesGreaterThanAngle`,
and all six radial sides have the same length, then the two source
chords are jointly longer than the target chord:

    AB + CD > EF.

This is the dimension-free chord-comparison core of Euclid XI.22.
-/
theorem hilbert_twoAnglesGreaterThanAngle_equalRadius_chordSumGreater
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (hSum :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F) :
    HilbertSegmentSumGreater
      Geo
      A B
      C D
      E F := by

  rcases hSum with
    ⟨hFirst,
      hSecond,
      hTarget,
      hCases⟩

  rcases hCases with
    hLess | hRest

  · exact
      hilbert_equalRadiusChordSum_of_first_greater
        Geo
        A O B
        C P D
        E Q F
        hFirst
        hSecond
        hTarget
        hLess
        hOA_OB
        hOA_QE
        hOA_QF

  · rcases hRest with
      hEq | hDecomp

    · exact
        hilbert_equalRadiusChordSum_of_first_equal
          Geo
          A O B
          C P D
          E Q F
          hFirst
          hSecond
          hTarget
          hEq
          hOA_OB
          hOA_QE
          hOA_QF

    · rcases hDecomp with
        ⟨X,
          hInside,
          hFirstPart,
          hRemainder⟩

      rcases hInside with
        ⟨H,
          hEHF,
          hRayQXH⟩

      have hXQ :
          Not (X = Q) :=
        hRayQXH.1

      have hQX :
          Not (Q = X) := by
        intro h
        exact hXQ h.symm

      have hAO :
          Not (A = O) :=
        hilbert_noncollinear_ne_first
          Geo
          A O B
          hFirst

      have hOA :
          Not (O = A) := by
        intro h
        exact hAO h.symm

      cases
          bookZero_49_layoff
            Geo
            Q X
            O A
            hQX
            hOA with
      | intro R hR =>

          have hRayQXR :
              HilbertSameRay Geo Q X R :=
            hR.1

          have hQR_OA :
              Geo.Congruent Q R O A :=
            hR.2

          have hInside' :
              HilbertRayMeetsSegment Geo Q X E F :=
            ⟨H, hEHF, hRayQXH⟩

          exact
            hilbert_equalRadiusChordSum_of_decomposition
              Geo
              A O B
              C P D
              E Q F
              X R
              hFirst
              hSecond
              hTarget
              hInside'
              hFirstPart
              hRemainder
              hRayQXR
              hQR_OA
              hOA_OB
              hOA_PC
              hOA_PD
              hOA_QE
              hOA_QF

end Geometry

import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)


/--
First Proposition I.22 test.

This isolates only the transport step needed for the "outside"
point in the circle-circle construction.

If Aa < BP and BP is congruent to FH, then Aa < FH.
-/
theorem euclid_proposition_22_outside_transport_test
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B P F H : Geo.Point)
    (hAa_BP : HilbertSegmentLess Geo A a B P)
    (hBP_FH : Geo.Congruent B P F H) :
    HilbertSegmentLess Geo A a F H := by

  exact
    bookZero_30_lessThanCongruence
      Geo
      A a
      B P
      F H
      hAa_BP
      hBP_FH

/--
Euclid I.22: construction of the outside point.

If BP represents the sum of Bb and Cc, while FH is composed
of congruent parts FG and GH, then Aa < BP implies Aa < FH.
-/
theorem euclid_proposition_22_outside_helper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c F G H P : Geo.Point)
    (hFG_Bb : Geo.Congruent F G B b)
    (hGH_Cc : Geo.Congruent G H C c)
    (hFGH : Geo.Between F G H)
    (hBbP : Geo.Between B b P)
    (hbP_Cc : Geo.Congruent b P C c)
    (hAa_BP : HilbertSegmentLess Geo A a B P) :
    HilbertSegmentLess Geo A a F H := by

  have hBb_FG :
      Geo.Congruent B b F G :=
    hilbert_congruent_symmetry
      Geo F G B b hFG_Bb

  have hCc_GH :
      Geo.Congruent C c G H :=
    hilbert_congruent_symmetry
      Geo G H C c hGH_Cc

  have hbP_GH :
      Geo.Congruent b P G H :=
    bookZero_congruenceTransitive
      Geo
      b P
      C c
      G H
      hbP_Cc
      hCc_GH

  have hBP_FH :
      Geo.Congruent B P F H :=
    bookZero_sumOfParts
      Geo
      B b P
      F G H
      hBb_FG
      hbP_GH
      hBbP
      hFGH

  exact
    bookZero_30_lessThanCongruence
      Geo
      A a
      B P
      F H
      hAa_BP
      hBP_FH

/--
Euclid I.22: construct the second point of the circle centered at G.

The point N lies on the ray GF and satisfies GN congruent Cc.
-/
theorem euclid_proposition_22_inside_point_test
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C c F G : Geo.Point)
    (hFG : F ≠ G) :
    ∃ N : Geo.Point,
      HilbertSameRay Geo G F N ∧
      Geo.Congruent G N C c := by

  have hGF : G ≠ F :=
    hFG.symm

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        C c
        G F
        hGF with
    ⟨N, hRayGFN, hGN_Cc⟩

  exact
    ⟨N, hRayGFN, hGN_Cc⟩


theorem euclid_proposition_22_sameRay_trichotomy
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (G F N : Geo.Point)
    (hGF : G ≠ F)
    (hGN : G ≠ N)
    (hRayGN : HilbertSameRay Geo G F N) :
    Geo.Between G N F ∨
    N = F ∨
    Geo.Between G F N := by

  by_cases hGN_GF :
      HilbertSegmentLess Geo G N G F

  · left

    have hRayGNF :
        HilbertSameRay Geo G N F :=
      bookZero_39_ray5
        Geo G F N hRayGN

    exact
      bookZero_51_lessThanBetween
        Geo
        G N F
        hGN_GF
        hRayGNF

  · by_cases hGF_GN :
        HilbertSegmentLess Geo G F G N

    · right
      right

      exact
        bookZero_51_lessThanBetween
          Geo
          G F N
          hGF_GN
          hRayGN

    · have hGF_GN_cong :
          Geo.Congruent G F G N :=
        bookZero_31_trichotomy1
          Geo
          G F
          G N
          hGF_GN
          hGN_GF
          hGF
          hGN

      have hRayGFF :
          HilbertSameRay Geo G F F :=
        hilbert_sameRay_refl
          Geo G F hGF.symm

      have hFN :
          F = N :=
        bookZero_50_layoffUnique
          Geo
          G F
          F N
          hRayGFF
          hRayGN
          hGF_GN_cong

      right
      left
      exact hFN.symm

/--
Cancellation of equal added parts for strict segment inequality.

If A-B-E and C-D-F, the added parts BE and DF are congruent,
and AE < CF, then AB < CD.
-/
theorem euclid_proposition_22_lessThan_cancel_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B E C D F : Geo.Point)
    (hABE : Geo.Between A B E)
    (hCDF : Geo.Between C D F)
    (hBE_DF : Geo.Congruent B E D F)
    (hAE_CF : HilbertSegmentLess Geo A E C F) :
    HilbertSegmentLess Geo A B C D := by

  by_cases hAB_CD :
      HilbertSegmentLess Geo A B C D

  · exact hAB_CD

  · by_cases hCD_AB :
        HilbertSegmentLess Geo C D A B

    · have hDF_BE :
          Geo.Congruent D F B E :=
        hilbert_congruent_symmetry
          Geo B E D F hBE_DF

      have hCF_AE :
          HilbertSegmentLess Geo C F A E :=
        bookZero_53_lessThanAdditive
          Geo
          C D
          A B
          F E
          hCD_AB
          hCDF
          hABE
          hDF_BE

      exact False.elim
        ((bookZero_47_trichotomy2
            Geo A E C F hAE_CF) hCF_AE)

    · have hAB : A ≠ B :=
        (HilbertOrder.between_incidence
          A B E hABE).1

      have hCD : C ≠ D :=
        (HilbertOrder.between_incidence
          C D F hCDF).1

      have hAB_CD_cong :
          Geo.Congruent A B C D :=
        bookZero_31_trichotomy1
          Geo
          A B
          C D
          hAB_CD
          hCD_AB
          hAB
          hCD

      have hAE_CF_cong :
          Geo.Congruent A E C F :=
        bookZero_sumOfParts
          Geo
          A B E
          C D F
          hAB_CD_cong
          hBE_DF
          hABE
          hCDF

      have hCF_AE_cong :
          Geo.Congruent C F A E :=
        hilbert_congruent_symmetry
          Geo A E C F hAE_CF_cong

      have hAE_AE :
          HilbertSegmentLess Geo A E A E :=
        bookZero_30_lessThanCongruence
          Geo
          A E
          C F
          A E
          hAE_CF
          hCF_AE_cong

      exact False.elim
        ((bookZero_47_trichotomy2
            Geo A E A E hAE_AE) hAE_AE)

/--
Euclid I.22: inside case G-N-F.

If G-N-F, GF represents Bb, GN represents Cc, and AP represents
Aa + Cc, then the triangle inequality Bb < Aa + Cc implies FN < Aa.
-/
theorem euclid_proposition_22_inside_left
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c F G N P : Geo.Point)
    (hGNF : Geo.Between G N F)
    (hGF_Bb : Geo.Congruent G F B b)
    (hGN_Cc : Geo.Congruent G N C c)
    (hAaP : Geo.Between A a P)
    (haP_Cc : Geo.Congruent a P C c)
    (hBb_AP : HilbertSegmentLess Geo B b A P) :
    HilbertSegmentLess Geo F N A a := by

  ----------------------------------------------------------------------
  -- Reverse G-N-F to F-N-G.
  ----------------------------------------------------------------------

  have hFNG :
      Geo.Between F N G :=
    (HilbertOrder.between_incidence
      G N F hGNF).2.2.2.2

  ----------------------------------------------------------------------
  -- Transport Bb < AP to FG < AP.
  ----------------------------------------------------------------------

  have hBb_GF :
      Geo.Congruent B b G F :=
    hilbert_congruent_symmetry
      Geo G F B b hGF_Bb

  have hBb_FG :
      Geo.Congruent B b F G :=
    CongruentSwapSecond
      Geo B b G F hBb_GF

  have hFG_AP :
      HilbertSegmentLess Geo F G A P :=
    bookZero_32_lessThanCongruence2
      Geo
      B b
      A P
      F G
      hBb_AP
      hBb_FG

  ----------------------------------------------------------------------
  -- NG and aP are congruent copies of Cc.
  ----------------------------------------------------------------------

  have hNG_Cc :
      Geo.Congruent N G C c :=
    CongruentReverseFirst
      Geo G N C c hGN_Cc

  have hCc_aP :
      Geo.Congruent C c a P :=
    hilbert_congruent_symmetry
      Geo a P C c haP_Cc

  have hNG_aP :
      Geo.Congruent N G a P :=
    bookZero_congruenceTransitive
      Geo
      N G
      C c
      a P
      hNG_Cc
      hCc_aP

  ----------------------------------------------------------------------
  -- Cancel the common added part NG ~= aP:
  --
  --     FN + NG < Aa + aP
  --
  -- hence
  --
  --     FN < Aa.
  ----------------------------------------------------------------------

  exact
    euclid_proposition_22_lessThan_cancel_right
      Geo
      F N G
      A a P
      hFNG
      hAaP
      hNG_aP
      hFG_AP

theorem euclid_proposition_22_inside_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c F G N P : Geo.Point)
    (hGFN : Geo.Between G F N)
    (hGF_Bb : Geo.Congruent G F B b)
    (hGN_Cc : Geo.Congruent G N C c)
    (hAaP : Geo.Between A a P)
    (haP_Bb : Geo.Congruent a P B b)
    (hCc_AP : HilbertSegmentLess Geo C c A P) :
    HilbertSegmentLess Geo F N A a := by

  have hNFG :
      Geo.Between N F G :=
    (HilbertOrder.between_incidence
      G F N hGFN).2.2.2.2

  have hNG_Cc :
      Geo.Congruent N G C c :=
    CongruentReverseFirst
      Geo G N C c hGN_Cc

  have hCc_NG :
      Geo.Congruent C c N G :=
    hilbert_congruent_symmetry
      Geo N G C c hNG_Cc

  have hNG_AP :
      HilbertSegmentLess Geo N G A P :=
    bookZero_32_lessThanCongruence2
      Geo
      C c
      A P
      N G
      hCc_AP
      hCc_NG

  have hBb_aP :
      Geo.Congruent B b a P :=
    hilbert_congruent_symmetry
      Geo a P B b haP_Bb

  have hGF_aP :
      Geo.Congruent G F a P :=
    bookZero_congruenceTransitive
      Geo
      G F
      B b
      a P
      hGF_Bb
      hBb_aP

  have hFG_aP :
      Geo.Congruent F G a P :=
    CongruentReverseFirst
      Geo G F a P hGF_aP

  have hNF_Aa :
      HilbertSegmentLess Geo N F A a :=
    euclid_proposition_22_lessThan_cancel_right
      Geo
      N F G
      A a P
      hNFG
      hAaP
      hFG_aP
      hNG_AP

  have hNF_FN :
      Geo.Congruent N F F N :=
    CongruentReverseFirst
      Geo F N F N
      (hilbert_congruent_reflexive Geo F N)

  exact
    bookZero_32_lessThanCongruence2
      Geo
      N F
      A a
      F N
      hNF_Aa
      hNF_FN

/--
Euclid I.22: the inside point for the circle-circle construction.

N lies on the ray GF and GN is congruent to Cc.
The two relevant triangle inequalities imply that N is either F
or FN is strictly shorter than Aa.
-/
theorem euclid_proposition_22_inside_helper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c F G N P Q : Geo.Point)
    (hGF : G ≠ F)
    (hGN : G ≠ N)
    (hRayGN : HilbertSameRay Geo G F N)
    (hGF_Bb : Geo.Congruent G F B b)
    (hGN_Cc : Geo.Congruent G N C c)

    -- P represents Aa + Cc and Bb < AP.
    (hAaP : Geo.Between A a P)
    (haP_Cc : Geo.Congruent a P C c)
    (hBb_AP : HilbertSegmentLess Geo B b A P)

    -- Q represents Aa + Bb and Cc < AQ.
    (hAaQ : Geo.Between A a Q)
    (haQ_Bb : Geo.Congruent a Q B b)
    (hCc_AQ : HilbertSegmentLess Geo C c A Q) :
    N = F ∨ HilbertSegmentLess Geo F N A a := by

  have hCases :
      Geo.Between G N F ∨
      N = F ∨
      Geo.Between G F N :=
    euclid_proposition_22_sameRay_trichotomy
      Geo
      G F N
      hGF
      hGN
      hRayGN

  rcases hCases with hGNF | hEq | hGFN

  · right

    exact
      euclid_proposition_22_inside_left
        Geo
        A a B b C c
        F G N P
        hGNF
        hGF_Bb
        hGN_Cc
        hAaP
        haP_Cc
        hBb_AP

  · left
    exact hEq

  · right

    exact
      euclid_proposition_22_inside_right
        Geo
        A a B b C c
        F G N Q
        hGFN
        hGF_Bb
        hGN_Cc
        hAaQ
        haQ_Bb
        hCc_AQ

/--
Auxiliary construction for Euclid I.22.

Given two distinct points F,G and a nondegenerate segment Cc,
construct a point H beyond G on line FG such that GH is
congruent to Cc.
-/
theorem euclid_proposition_22_extend_with_segment
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (F G C c : Geo.Point)
    (hFG : F ≠ G)
    (hCc : C ≠ c) :
    ∃ H : Geo.Point,
      Geo.Between F G H ∧
      Geo.Congruent G H C c := by

  rcases HilbertOrder.between_extension F G hFG with
    ⟨R, hFGR⟩

  have hGR : G ≠ R :=
    (HilbertOrder.between_incidence F G R hFGR).2.1

  rcases bookZero_49_layoff
      Geo G R C c hGR hCc with
    ⟨H, hRayH, hGHCc⟩

  have hRayF : HilbertSameRay Geo G F F :=
    hilbert_sameRay_refl Geo G F hFG

  have hFGH : Geo.Between F G H :=
    hilbert_between_transport_sameRays
      Geo
      F G R
      F H
      hFGR
      hRayF
      hRayH

  exact ⟨H, hFGH, hGHCc⟩

/--
Euclid I.22: prepare the inside/outside witnesses for circle-circle.

We use the given segment Bb itself as the distance between the
two circle centers: F := B and G := b.

H lies beyond b from B and satisfies bH ~= Cc.
N lies on ray bB and satisfies bN ~= Cc.

The three triangle inequalities then give:
* Aa < BH,
* N = B or BN < Aa.
-/
theorem euclid_proposition_22_circle_witnesses
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c P Q R : Geo.Point)
    (_hAa : A ≠ a)
    (hBb : B ≠ b)
    (hCc : C ≠ c)

    -- P represents Bb + Cc, and Aa < BP.
    (hBbP : Geo.Between B b P)
    (hbP_Cc : Geo.Congruent b P C c)
    (hAa_BP : HilbertSegmentLess Geo A a B P)

    -- Q represents Aa + Cc, and Bb < AQ.
    (hAaQ : Geo.Between A a Q)
    (haQ_Cc : Geo.Congruent a Q C c)
    (hBb_AQ : HilbertSegmentLess Geo B b A Q)

    -- R represents Aa + Bb, and Cc < AR.
    (hAaR : Geo.Between A a R)
    (haR_Bb : Geo.Congruent a R B b)
    (hCc_AR : HilbertSegmentLess Geo C c A R) :
    ∃ H N : Geo.Point,
      Geo.Between B b H ∧
      Geo.Congruent b H C c ∧
      HilbertSegmentLess Geo A a B H ∧
      HilbertSameRay Geo b B N ∧
      Geo.Congruent b N C c ∧
      (N = B ∨ HilbertSegmentLess Geo B N A a) := by

  ----------------------------------------------------------------------
  -- Construct H beyond b with bH ~= Cc.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_22_extend_with_segment
        (Geo := Geo)
        B b C c
        hBb hCc with
    ⟨H, hBbH, hbH_Cc⟩

  ----------------------------------------------------------------------
  -- H is outside the circle centered at B with radius Aa.
  ----------------------------------------------------------------------

  have hAa_BH :
      HilbertSegmentLess Geo A a B H :=
    euclid_proposition_22_outside_helper
      Geo
      A a
      B b
      C c
      B b H P
      (hilbert_congruent_reflexive Geo B b)
      hbH_Cc
      hBbH
      hBbP
      hbP_Cc
      hAa_BP

  ----------------------------------------------------------------------
  -- Construct N on ray bB with bN ~= Cc.
  ----------------------------------------------------------------------

  rcases
      bookZero_49_layoff
        Geo
        b B
        C c
        hBb.symm
        hCc with
    ⟨N, hRaybBN, hbN_Cc⟩

  have hbN : b ≠ N :=
    bookZero_nullSegment3
      Geo
      C c
      b N
      hCc
      (hilbert_congruent_symmetry
        Geo b N C c hbN_Cc)

  ----------------------------------------------------------------------
  -- The base segment bB is congruent to Bb.
  ----------------------------------------------------------------------

  have hbB_Bb :
      Geo.Congruent b B B b :=
    CongruentReverseFirst
      Geo B b B b
      (hilbert_congruent_reflexive Geo B b)

  ----------------------------------------------------------------------
  -- N is inside the circle centered at B with radius Aa.
  ----------------------------------------------------------------------

  have hNinside :
      N = B ∨ HilbertSegmentLess Geo B N A a :=
    euclid_proposition_22_inside_helper
      Geo
      A a
      B b
      C c
      B b N
      Q R
      hBb.symm
      hbN
      hRaybBN
      hbB_Bb
      hbN_Cc
      hAaQ
      haQ_Cc
      hBb_AQ
      hAaR
      haR_Bb
      hCc_AR

  exact
    ⟨H, N,
     hBbH,
     hbH_Cc,
     hAa_BH,
     hRaybBN,
     hbN_Cc,
     hNinside⟩

/--
Euclid I.22: apply circle-circle continuity.

H and N lie on the circle centered at b with radius Cc.
N is inside the circle centered at B with radius Aa,
while H is outside it.

Hence the two circles meet at a point K.
-/
theorem euclid_proposition_22_circle_intersection
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c H N : Geo.Point)
    (_hAa : A ≠ a)
    (hBb : B ≠ b)
    (hCc : C ≠ c)
    (hbH_Cc : Geo.Congruent b H C c)
    (hAa_BH : HilbertSegmentLess Geo A a B H)
    (hbN_Cc : Geo.Congruent b N C c)
    (hNinside :
      N = B ∨ HilbertSegmentLess Geo B N A a) :
    ∃ K : Geo.Point,
      Geo.Congruent B K A a ∧
      Geo.Congruent b K C c := by

  ----------------------------------------------------------------------
  -- Represent the radius Aa by a segment BT from the center B.
  ----------------------------------------------------------------------

  rcases
      bookZero_49_layoff
        Geo
        B b
        A a
        hBb
        _hAa with
    ⟨T, hRayBT, hBT_Aa⟩

  have hAa_BT :
      Geo.Congruent A a B T :=
    hilbert_congruent_symmetry
      Geo B T A a hBT_Aa

  have hBT : B ≠ T :=
    bookZero_nullSegment3
      Geo
      A a
      B T
      _hAa
      hAa_BT

  ----------------------------------------------------------------------
  -- N is nondegenerate as a radius point of the second circle.
  ----------------------------------------------------------------------

  have hCc_bN :
      Geo.Congruent C c b N :=
    hilbert_congruent_symmetry
      Geo b N C c hbN_Cc

  have hbN : b ≠ N :=
    bookZero_nullSegment3
      Geo
      C c
      b N
      hCc
      hCc_bN

  ----------------------------------------------------------------------
  -- Both N and H lie on the circle centered at b with radius bN.
  ----------------------------------------------------------------------

  have hNon2 :
      Geo.Congruent b N b N :=
    hilbert_congruent_reflexive
      Geo b N

  have hbH_bN :
      Geo.Congruent b H b N :=
    bookZero_congruenceTransitive
      Geo
      b H
      C c
      b N
      hbH_Cc
      hCc_bN

  ----------------------------------------------------------------------
  -- Transport "inside" from radius Aa to the represented radius BT.
  ----------------------------------------------------------------------

  have hNinsideBT :
      N = B ∨ HilbertSegmentLess Geo B N B T := by

    rcases hNinside with hNB | hBN_Aa

    · exact Or.inl hNB

    · right
      exact
        bookZero_30_lessThanCongruence
          Geo
          B N
          A a
          B T
          hBN_Aa
          hAa_BT

  ----------------------------------------------------------------------
  -- Transport "outside" from Aa < BH to BT < BH.
  ----------------------------------------------------------------------

  have hBT_BH :
      HilbertSegmentLess Geo B T B H :=
    bookZero_32_lessThanCongruence2
      Geo
      A a
      B H
      B T
      hAa_BH
      hAa_BT

  ----------------------------------------------------------------------
  -- Circle-circle continuity.
  --
  -- Circle 1: center B, radius BT ~= Aa
  -- Circle 2: center b, radius bN ~= Cc
  -- inside point:  N
  -- outside point: H
  ----------------------------------------------------------------------

  rcases
      hilbert_circle_circle_intersection
        Geo
        B T
        b N
        N H
        hBT
        hbN
        hNon2
        hbH_bN
        hNinsideBT
        hBT_BH with
    ⟨K, hBK_BT, hbK_bN⟩

  ----------------------------------------------------------------------
  -- Return to the original given segments Aa and Cc.
  ----------------------------------------------------------------------

  have hBK_Aa :
      Geo.Congruent B K A a :=
    bookZero_congruenceTransitive
      Geo
      B K
      B T
      A a
      hBK_BT
      hBT_Aa

  have hbK_Cc :
      Geo.Congruent b K C c :=
    bookZero_congruenceTransitive
      Geo
      b K
      b N
      C c
      hbK_bN
      hbN_Cc

  exact ⟨K, hBK_Aa, hbK_Cc⟩

/--
Euclid I.22: core construction.

Assume the three triangle inequalities are represented by
three constructed sums:

* P represents Bb + Cc, with Aa < BP,
* Q represents Aa + Cc, with Bb < AQ,
* R represents Aa + Bb, with Cc < AR.

Then there exists a point K such that

* BK ~= Aa,
* bK ~= Cc.

Together with the given base Bb, this is the required triangle.
-/
theorem euclid_proposition_22_core
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c P Q R : Geo.Point)
    (hAa : A ≠ a)
    (hBb : B ≠ b)
    (hCc : C ≠ c)

    -- P represents Bb + Cc, and Aa < BP.
    (hBbP : Geo.Between B b P)
    (hbP_Cc : Geo.Congruent b P C c)
    (hAa_BP : HilbertSegmentLess Geo A a B P)

    -- Q represents Aa + Cc, and Bb < AQ.
    (hAaQ : Geo.Between A a Q)
    (haQ_Cc : Geo.Congruent a Q C c)
    (hBb_AQ : HilbertSegmentLess Geo B b A Q)

    -- R represents Aa + Bb, and Cc < AR.
    (hAaR : Geo.Between A a R)
    (haR_Bb : Geo.Congruent a R B b)
    (hCc_AR : HilbertSegmentLess Geo C c A R) :
    ∃ K : Geo.Point,
      Geo.Congruent B K A a ∧
      Geo.Congruent b K C c := by

  rcases
      euclid_proposition_22_circle_witnesses
        Geo
        A a
        B b
        C c
        P Q R
        hAa
        hBb
        hCc
        hBbP
        hbP_Cc
        hAa_BP
        hAaQ
        haQ_Cc
        hBb_AQ
        hAaR
        haR_Bb
        hCc_AR with
    ⟨H, N,
     _hBbH,
     hbH_Cc,
     hAa_BH,
     _hRaybBN,
     hbN_Cc,
     hNinside⟩

  exact
    euclid_proposition_22_circle_intersection
      Geo
      A a
      B b
      C c
      H N
      hAa
      hBb
      hCc
      hbH_Cc
      hAa_BH
      hbN_Cc
      hNinside

/--
Euclid I.22: final construction layer over the circle argument.

The points P, Q, R represent the three sums

  BP = Bb + Cc,
  AQ = Aa + Cc,
  AR = Aa + Bb.

Assuming the corresponding triangle inequalities, there exists
a point K such that BK ~= Aa and bK ~= Cc.
-/
theorem euclid_proposition_22_from_sum_witnesses
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c P Q R : Geo.Point)
    (hAa : A ≠ a)
    (hBb : B ≠ b)
    (hCc : C ≠ c)

    -- Triangle inequalities, expressed using the three sum segments.
    (hAa_BP : HilbertSegmentLess Geo A a B P)
    (hBb_AQ : HilbertSegmentLess Geo B b A Q)
    (hCc_AR : HilbertSegmentLess Geo C c A R)

    -- The sum points lie beyond the corresponding endpoints.
    (hBbP : Geo.Between B b P)
    (hbP_Cc : Geo.Congruent b P C c)

    (hAaQ : Geo.Between A a Q)
    (haQ_Cc : Geo.Congruent a Q C c)

    (hAaR : Geo.Between A a R)
    (haR_Bb : Geo.Congruent a R B b) :
    ∃ K : Geo.Point,
      Geo.Congruent B K A a ∧
      Geo.Congruent b K C c := by

  exact
    euclid_proposition_22_core
      Geo
      A a
      B b
      C c
      P Q R
      hAa
      hBb
      hCc
      hBbP
      hbP_Cc
      hAa_BP
      hAaQ
      haQ_Cc
      hBb_AQ
      hAaR
      haR_Bb
      hCc_AR

theorem euclid_proposition_22
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A a B b C c : Geo.Point)
    (hAa : A ≠ a)
    (hBb : B ≠ b)
    (hCc : C ≠ c)
    (hAa_lt_BbCc :
      HilbertSegmentSumGreater Geo B b C c A a)
    (hBb_lt_AaCc :
      HilbertSegmentSumGreater Geo A a C c B b)
    (hCc_lt_AaBb :
      HilbertSegmentSumGreater Geo A a B b C c) :
    ∃ K : Geo.Point,
      Geo.Congruent B K A a ∧
      Geo.Congruent b K C c := by

  rcases hAa_lt_BbCc with
    ⟨P, hBbP, hbP_Cc, hAa_BP⟩

  rcases hBb_lt_AaCc with
    ⟨Q, hAaQ, haQ_Cc, hBb_AQ⟩

  rcases hCc_lt_AaBb with
    ⟨R, hAaR, haR_Bb, hCc_AR⟩

  exact
    euclid_proposition_22_from_sum_witnesses
      Geo
      A a B b C c
      P Q R
      hAa
      hBb
      hCc
      hAa_BP
      hBb_AQ
      hCc_AR
      hBbP
      hbP_Cc
      hAaQ
      haQ_Cc
      hAaR
      haR_Bb

end Geometry

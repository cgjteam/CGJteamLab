import CGJteamLab.Proposition34
import CGJteamLab.HilbertScissors

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.43
--
-- In any parallelogram the complements of the parallelograms about
-- the diameter are equal to one another.
--
-- Setup: parallelogram A B C D with diagonal A C. K is a point on the
-- diagonal. G is a point on side A B, E on side A D, F on side B C,
-- H on side D C, positioned so that A G K E and K F C H are
-- themselves parallelograms (the two small parallelograms "about the
-- diagonal", sharing the diagonal points A-K and K-C respectively).
-- The two "complements" are the remaining regions: near B, the
-- quadrilateral G B F K (triangulated here via its diagonal B K as
-- triangle G B K + triangle K B F); near D, the quadrilateral E K H D
-- (triangulated via its diagonal K D as triangle E D K + triangle
-- K D H). The theorem: these two complements are equicomplementable.
--
-- This is purely relational (unlike I.42): the whole configuration is
-- taken as given data, exactly as I.34/I.37-I.41 take their
-- configurations as hypotheses. No new axiom is needed.
--
-- Proof (Euclid's own, "equals from equals"):
--
--   triangle ABC = triangle ACD                (I.34 on the big parallelogram)
--   triangle AGK = triangle AEK                 (I.34 on AGKE)
--   triangle KFC = triangle KHC                 (I.34 on KFCH)
--
--   triangle ABC  = AGK + (GBK + KBF) + KFC     (two cevian splits, at K then at G/F)
--   triangle ACD  = AEK + (EDK + KDH) + KHC     (two cevian splits, at K then at E/H)
--
-- Combining the three congruences with the two decompositions gives
--   (GBK+KBF) + (AGK+KFC) = (EDK+KDH) + (AEK+KHC)
-- which is exactly the defining equicomplementability of the two
-- complements, with common complement AGK+KFC ~ AEK+KHC.
------------------------------------------------------------------------

/--
Euclid I.43.

In parallelogram `ABCD` with diagonal `AC`, `K` a point on the
diagonal, and the two "diagonal" parallelograms `AGKE` (at `A`, with
`G` on `AB`, `E` on `AD`) and `KFCH` (at `C`, with `F` on `BC`, `H` on
`DC`), the two complements -- the quadrilateral `GBFK` (near `B`) and
the quadrilateral `EKHD` (near `D`), each triangulated via its own
diagonal -- are equicomplementable.
-/
theorem euclid_proposition_43
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D K G E F H : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D)
    (hAKC : Geo.Between A K C)
    (hAGB : Geo.Between A G B)
    (hAED : Geo.Between A E D)
    (hBFC : Geo.Between B F C)
    (hDHC : Geo.Between D H C)
    (hPar1 : IsParallelogram Geo A G K E)
    (hPar2 : IsParallelogram Geo K F C H) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo G B K +
       hilbertScissorsTriangle Geo K B F)
      (hilbertScissorsTriangle Geo E D K +
       hilbertScissorsTriangle Geo K D H) := by

  --------------------------------------------------------------------
  -- T1: triangle ABC decomposes as AGK + (GBK + KBF) + KFC.
  --
  -- First split off K from the diagonal AC (apex B), then split off
  -- G from AB inside the AK-piece (apex K), and F from BC inside the
  -- KC-piece (apex K).
  --------------------------------------------------------------------

  have hT1 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        ((hilbertScissorsTriangle Geo A G K +
          hilbertScissorsTriangle Geo G B K) +
         (hilbertScissorsTriangle Geo K B F +
          hilbertScissorsTriangle Geo K F C)) := by

    have h1 := HilbertScissorsEq.split (Geo := Geo) B A C K hAKC
    -- h1 : triangle B A C = triangle B A K + triangle B K C
    rw [← scissors_triangle_swap12 Geo A B C] at h1
    -- h1 : triangle A B C = triangle B A K + triangle B K C
    rw [scissors_triangle_cycle Geo B A K,
        scissors_triangle_swap12 Geo A K B] at h1
    -- h1 : triangle A B C = triangle K A B + triangle B K C
    rw [scissors_triangle_swap12 Geo B K C] at h1
    -- h1 : triangle A B C = triangle K A B + triangle K B C

    have h2 := HilbertScissorsEq.split (Geo := Geo) K A B G hAGB
    -- h2 : triangle K A B = triangle K A G + triangle K G B
    rw [scissors_triangle_cycle Geo K A G,
        scissors_triangle_cycle Geo K G B] at h2
    -- h2 : triangle K A B = triangle A G K + triangle G B K

    have h3 := HilbertScissorsEq.split (Geo := Geo) K B C F hBFC
    -- h3 : triangle K B C = triangle K B F + triangle K F C

    exact
      HilbertScissorsEq.trans (Geo := Geo) h1
        (HilbertScissorsEq.add (Geo := Geo) h2 h3)

  --------------------------------------------------------------------
  -- T2: triangle ACD decomposes as AEK + (EDK + KDH) + KHC,
  -- by the mirror-image construction on the D side.
  --------------------------------------------------------------------

  have hT2 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A C D)
        ((hilbertScissorsTriangle Geo E D K +
          hilbertScissorsTriangle Geo A E K) +
         (hilbertScissorsTriangle Geo K D H +
          hilbertScissorsTriangle Geo K H C)) := by

    have hDEA : Geo.Between D E A :=
      (HilbertOrder.between_incidence A E D hAED).2.2.2.2

    have h1 := HilbertScissorsEq.split (Geo := Geo) D A C K hAKC
    -- h1 : triangle D A C = triangle D A K + triangle D K C
    rw [← scissors_triangle_cycle Geo C D A,
        ← scissors_triangle_cycle Geo A C D] at h1
    -- h1 : triangle A C D = triangle D A K + triangle D K C
    rw [scissors_triangle_cycle Geo D A K,
        scissors_triangle_cycle Geo A K D,
        scissors_triangle_swap12 Geo D K C] at h1
    -- h1 : triangle A C D = triangle K D A + triangle K D C

    have h2 := HilbertScissorsEq.split (Geo := Geo) K D A E hDEA
    -- h2 : triangle K D A = triangle K D E + triangle K E A
    rw [scissors_triangle_swap12 Geo K D E,
        scissors_triangle_swap23 Geo D K E,
        scissors_triangle_swap12 Geo D E K] at h2
    -- h2 : triangle K D A = triangle E D K + triangle K E A
    rw [scissors_triangle_swap12 Geo K E A,
        scissors_triangle_swap23 Geo E K A,
        scissors_triangle_swap12 Geo E A K] at h2
    -- h2 : triangle K D A = triangle E D K + triangle A E K

    have h3 := HilbertScissorsEq.split (Geo := Geo) K D C H hDHC
    -- h3 : triangle K D C = triangle K D H + triangle K H C

    exact
      HilbertScissorsEq.trans (Geo := Geo) h1
        (HilbertScissorsEq.add (Geo := Geo) h2 h3)

  --------------------------------------------------------------------
  -- T3: triangle ABC = triangle ACD (I.34 on the big parallelogram).
  --------------------------------------------------------------------

  have hT3 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A C D) := by
    have hCong :=
      euclid_proposition_34_diagonal Geo A B C D hParallelogram
    have hRaw :
        HilbertScissorsEq Geo
          (hilbertScissorsTriangle Geo A B C)
          (hilbertScissorsTriangle Geo C D A) :=
      scissors_congruent Geo A B C C D A hCong
    rw [scissors_triangle_cycle Geo C D A,
        scissors_triangle_cycle Geo D A C] at hRaw
    exact hRaw

  --------------------------------------------------------------------
  -- T4: triangle AGK = triangle AEK (I.34 on AGKE).
  --------------------------------------------------------------------

  have hT4 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A G K)
        (hilbertScissorsTriangle Geo A E K) := by
    have hCong :=
      euclid_proposition_34_diagonal Geo A G K E hPar1
    have hRaw :
        HilbertScissorsEq Geo
          (hilbertScissorsTriangle Geo A G K)
          (hilbertScissorsTriangle Geo K E A) :=
      scissors_congruent Geo A G K K E A hCong
    rw [scissors_triangle_swap12 Geo K E A,
        scissors_triangle_swap23 Geo E K A,
        scissors_triangle_swap12 Geo E A K] at hRaw
    exact hRaw

  --------------------------------------------------------------------
  -- T5: triangle KFC = triangle KHC (I.34 on KFCH).
  --------------------------------------------------------------------

  have hT5 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo K F C)
        (hilbertScissorsTriangle Geo K H C) := by
    have hCong :=
      euclid_proposition_34_diagonal Geo K F C H hPar2
    have hRaw :
        HilbertScissorsEq Geo
          (hilbertScissorsTriangle Geo K F C)
          (hilbertScissorsTriangle Geo C H K) :=
      scissors_congruent Geo K F C C H K hCong
    rw [scissors_triangle_swap12 Geo C H K,
        scissors_triangle_swap23 Geo H C K,
        scissors_triangle_swap12 Geo H K C] at hRaw
    exact hRaw

  --------------------------------------------------------------------
  -- Master equality: the two full 4-piece decompositions agree.
  --------------------------------------------------------------------

  have hMaster :
      HilbertScissorsEq Geo
        ((hilbertScissorsTriangle Geo A G K +
          hilbertScissorsTriangle Geo G B K) +
         (hilbertScissorsTriangle Geo K B F +
          hilbertScissorsTriangle Geo K F C))
        ((hilbertScissorsTriangle Geo E D K +
          hilbertScissorsTriangle Geo A E K) +
         (hilbertScissorsTriangle Geo K D H +
          hilbertScissorsTriangle Geo K H C)) :=
    HilbertScissorsEq.trans (Geo := Geo)
      (HilbertScissorsEq.symm (Geo := Geo) hT1)
      (HilbertScissorsEq.trans (Geo := Geo) hT3 hT2)

  --------------------------------------------------------------------
  -- Regroup both sides: separate the "corner" pieces (AGK, KFC on
  -- the left; AEK, KHC on the right) from the "complement" pieces.
  --------------------------------------------------------------------

  have hRegroupLeft :
      (hilbertScissorsTriangle Geo A G K +
       hilbertScissorsTriangle Geo G B K) +
      (hilbertScissorsTriangle Geo K B F +
       hilbertScissorsTriangle Geo K F C)
        =
      (hilbertScissorsTriangle Geo G B K +
       hilbertScissorsTriangle Geo K B F) +
      (hilbertScissorsTriangle Geo A G K +
       hilbertScissorsTriangle Geo K F C) := by
    calc
      (hilbertScissorsTriangle Geo A G K + hilbertScissorsTriangle Geo G B K) +
      (hilbertScissorsTriangle Geo K B F + hilbertScissorsTriangle Geo K F C)
          = hilbertScissorsTriangle Geo A G K +
            (hilbertScissorsTriangle Geo G B K +
             (hilbertScissorsTriangle Geo K B F +
              hilbertScissorsTriangle Geo K F C)) := Multiset.add_assoc _ _ _
      _ = hilbertScissorsTriangle Geo A G K +
            ((hilbertScissorsTriangle Geo G B K +
              hilbertScissorsTriangle Geo K B F) +
             hilbertScissorsTriangle Geo K F C) := by
            rw [← Multiset.add_assoc
                  (hilbertScissorsTriangle Geo G B K)
                  (hilbertScissorsTriangle Geo K B F)
                  (hilbertScissorsTriangle Geo K F C)]
      _ = (hilbertScissorsTriangle Geo A G K +
           (hilbertScissorsTriangle Geo G B K +
            hilbertScissorsTriangle Geo K B F)) +
          hilbertScissorsTriangle Geo K F C :=
            (Multiset.add_assoc _ _ _).symm
      _ = ((hilbertScissorsTriangle Geo G B K +
            hilbertScissorsTriangle Geo K B F) +
           hilbertScissorsTriangle Geo A G K) +
          hilbertScissorsTriangle Geo K F C := by
            rw [Multiset.add_comm
                  (hilbertScissorsTriangle Geo A G K)
                  (hilbertScissorsTriangle Geo G B K +
                   hilbertScissorsTriangle Geo K B F)]
      _ = (hilbertScissorsTriangle Geo G B K +
           hilbertScissorsTriangle Geo K B F) +
          (hilbertScissorsTriangle Geo A G K +
           hilbertScissorsTriangle Geo K F C) := Multiset.add_assoc _ _ _

  have hRegroupRight :
      (hilbertScissorsTriangle Geo E D K +
       hilbertScissorsTriangle Geo A E K) +
      (hilbertScissorsTriangle Geo K D H +
       hilbertScissorsTriangle Geo K H C)
        =
      (hilbertScissorsTriangle Geo E D K +
       hilbertScissorsTriangle Geo K D H) +
      (hilbertScissorsTriangle Geo A E K +
       hilbertScissorsTriangle Geo K H C) := by
    calc
      (hilbertScissorsTriangle Geo E D K + hilbertScissorsTriangle Geo A E K) +
      (hilbertScissorsTriangle Geo K D H + hilbertScissorsTriangle Geo K H C)
          = hilbertScissorsTriangle Geo E D K +
            (hilbertScissorsTriangle Geo A E K +
             (hilbertScissorsTriangle Geo K D H +
              hilbertScissorsTriangle Geo K H C)) := Multiset.add_assoc _ _ _
      _ = hilbertScissorsTriangle Geo E D K +
            ((hilbertScissorsTriangle Geo A E K +
              hilbertScissorsTriangle Geo K D H) +
             hilbertScissorsTriangle Geo K H C) := by
            rw [← Multiset.add_assoc
                  (hilbertScissorsTriangle Geo A E K)
                  (hilbertScissorsTriangle Geo K D H)
                  (hilbertScissorsTriangle Geo K H C)]
      _ = hilbertScissorsTriangle Geo E D K +
            ((hilbertScissorsTriangle Geo K D H +
              hilbertScissorsTriangle Geo A E K) +
             hilbertScissorsTriangle Geo K H C) := by
            rw [Multiset.add_comm
                  (hilbertScissorsTriangle Geo A E K)
                  (hilbertScissorsTriangle Geo K D H)]
      _ = hilbertScissorsTriangle Geo E D K +
            (hilbertScissorsTriangle Geo K D H +
             (hilbertScissorsTriangle Geo A E K +
              hilbertScissorsTriangle Geo K H C)) := by
            rw [Multiset.add_assoc
                  (hilbertScissorsTriangle Geo K D H)
                  (hilbertScissorsTriangle Geo A E K)
                  (hilbertScissorsTriangle Geo K H C)]
      _ = (hilbertScissorsTriangle Geo E D K +
           hilbertScissorsTriangle Geo K D H) +
          (hilbertScissorsTriangle Geo A E K +
           hilbertScissorsTriangle Geo K H C) :=
            (Multiset.add_assoc _ _ _).symm

  rw [hRegroupLeft, hRegroupRight] at hMaster
  -- hMaster :
  --   (GBK+KBF) + (AGK+KFC) = (EDK+KDH) + (AEK+KHC)

  --------------------------------------------------------------------
  -- The common complement is AGK+KFC ~ AEK+KHC (from T4, T5); this
  -- is exactly the equicomplementability of the two complements.
  --------------------------------------------------------------------

  exact
    ⟨hilbertScissorsTriangle Geo A G K +
       hilbertScissorsTriangle Geo K F C,
     hilbertScissorsTriangle Geo A E K +
       hilbertScissorsTriangle Geo K H C,
     HilbertScissorsEq.add (Geo := Geo) hT4 hT5,
     hMaster⟩

end Geometry

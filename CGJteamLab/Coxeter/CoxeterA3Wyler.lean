import CGJteamLab.Coxeter.CoxeterRelations3DExistence
import CGJteamLab.Coxeter.CoxeterRelations
import CGJteamLab.Wyler.HilbertWylerInterface
import CGJteamLab.Proposition11_12

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 through the Wyler flat calculus

This module gives a structural reading of the existing spatial Coxeter A3
tetrahedral frame through Wyler-style flat calculus.

The development is layered as follows.

1. The mirror meets are computed as spatial line flats; for the distant
   pair one obtains

       pi1 meet pi3 = Span{F1,F3}.

2. The three pairwise mirror meets are recovered by joins:

       pi1 = q12 join q13,
       pi2 = q12 join q23,
       pi3 = q23 join q13.

3. Each meet line is identified exactly with the common fixed-point locus
   of the corresponding pair of spatial reflections.

4. For the adjacent pairs, explicit active plane slices reduce the spatial
   mirrors to ordinary planar reflection axes.  The equilateral-median
   Coxeter theorem then gives exact periods

       m12 = 3,
       m23 = 3.

5. For the distant pair, an explicit normal slice produces perpendicular
   planar reflection axes and hence

       m13 = 2.

The final theorem `wyler_A3_local_Coxeter_diagram` packages the local
Coxeter diagram 3--3 with distant exponent 2.

The module is entirely synthetic.  It uses no coordinates, vectors,
inner products, Gram matrices, numerical angle measure, cosine, or
trigonometry.
-/

namespace CoxeterA3TetrahedralFrame


section MeetSpan

variable
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]

/-- The midpoint F1 belongs to both distant mirrors pi1 and pi3. -/
theorem wyler_F1_on_pi1_and_pi3
    (T : CoxeterA3TetrahedralFrame Geo) :
    S.OnPlane T.F1 T.pi1 /\
    S.OnPlane T.F1 T.pi3 := by

  rcases T.AB_perp_pi1 with
    ⟨_n1, _hAn1, hPerp1⟩

  have hF1pi1 :
      S.OnPlane T.F1 T.pi1 :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp1).2

  have hMid1Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.A T.F1 T.B T.F1_mid_AB.1

  have hAB : Ne T.A T.B :=
    hMid1Data.2.2.1

  rcases hMid1Data.2.2.2.1 with
    ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

  have hlABpi3 :
      HilbertLineInPlane Geo lAB T.pi3 :=
    euclid_proposition_11_1_via_flats
      (Geo := Geo)
      T.pi3 lAB
      T.A T.B
      hAB
      hAlAB hBlAB
      T.A_on_pi3 T.B_on_pi3

  have hF1pi3 :
      S.OnPlane T.F1 T.pi3 :=
    hlABpi3 T.F1 hF1lAB

  exact ⟨hF1pi1, hF1pi3⟩

/-- The midpoint F3 belongs to both distant mirrors pi1 and pi3. -/
theorem wyler_F3_on_pi1_and_pi3
    (T : CoxeterA3TetrahedralFrame Geo) :
    S.OnPlane T.F3 T.pi1 /\
    S.OnPlane T.F3 T.pi3 := by

  rcases T.CD_perp_pi3 with
    ⟨_n3, _hCn3, hPerp3⟩

  have hF3pi3 :
      S.OnPlane T.F3 T.pi3 :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp3).2

  have hMid3Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.C T.F3 T.D T.F3_mid_CD.1

  have hCD : Ne T.C T.D :=
    hMid3Data.2.2.1

  rcases hMid3Data.2.2.2.1 with
    ⟨lCD, hClCD, hF3lCD, hDlCD⟩

  have hlCDpi1 :
      HilbertLineInPlane Geo lCD T.pi1 :=
    euclid_proposition_11_1_via_flats
      (Geo := Geo)
      T.pi1 lCD
      T.C T.D
      hCD
      hClCD hDlCD
      T.C_on_pi1 T.D_on_pi1

  have hF3pi1 :
      S.OnPlane T.F3 T.pi1 :=
    hlCDpi1 T.F3 hF3lCD

  exact ⟨hF3pi1, hF3pi3⟩

variable [HilbertPlaneIncidence Geo]

/-- The two opposite edge midpoints F1 and F3 are distinct. -/
theorem wyler_F1_ne_F3
    (T : CoxeterA3TetrahedralFrame Geo) :
    Ne T.F1 T.F3 := by

  have hMid1Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.A T.F1 T.B T.F1_mid_AB.1

  have hMid3Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.C T.F3 T.D T.F3_mid_CD.1

  rcases hMid1Data.2.2.2.1 with
    ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

  rcases hMid3Data.2.2.2.1 with
    ⟨lCD, hClCD, hF3lCD, hDlCD⟩

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.C T.D
      T.noncoplanar

  have hlABCD : Ne lAB lCD := by
    intro hEq

    have hClAB : H.OnLine T.C lAB := by
      rw [hEq]
      exact hClCD

    exact hABC
      ⟨lAB, hAlAB, hBlAB, hClAB⟩

  intro hF13

  have hF1lCD : H.OnLine T.F1 lCD := by
    rw [hF13]
    exact hF3lCD

  rcases
      euclid_proposition_11_2_via_join
        (Geo := Geo)
        lAB lCD T.F1
        hlABCD
        hF1lAB hF1lCD with
    ⟨pi, hlABpi, hlCDpi, _hJoin⟩

  exact T.noncoplanar
    ⟨pi,
     hlABpi T.A hAlAB,
     hlABpi T.B hBlAB,
     hlCDpi T.C hClCD,
     hlCDpi T.D hDlCD⟩

/--
Wyler meet calculation for the distant A3 mirrors.

The intersection of the two plane carriers is exactly the two-point span
of the opposite-edge midpoints F1 and F3.
-/
theorem wyler_pi1_meet_pi3_eq_span_F1_F3
    (T : CoxeterA3TetrahedralFrame Geo) :
    Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi3) =
      HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) := by

  have hF1 :=
    wyler_F1_on_pi1_and_pi3
      (Geo := Geo) T

  have hF3 :=
    wyler_F3_on_pi1_and_pi3
      (Geo := Geo) T

  have hF13 : Ne T.F1 T.F3 :=
    wyler_F1_ne_F3
      (Geo := Geo) T

  have hPi13 : Ne T.pi1 T.pi3 := by
    intro hEq
    apply T.A_off_pi1
    rw [hEq]
    exact T.A_on_pi3

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi1 T.pi3
        hPi13
        T.F1
        hF1.1 hF1.2 with
    ⟨q, hF1q, _hqpi1, _hqpi3, hMeet⟩

  have hF3Meet :
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi3)
        T.F3 :=
    ⟨hF3.1, hF3.2⟩

  have hF3q : H.OnLine T.F3 q := by
    change HilbertLineCarrier3D Geo q T.F3
    rw [← hMeet]
    exact hF3Meet

  have hSpan :
      HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) =
        HilbertLineCarrier3D Geo q :=
    hilbertSpan3D_pair_eq_lineCarrier
      (Geo := Geo)
      T.F1 T.F3 q
      hF13
      hF1q hF3q

  exact hMeet.trans hSpan.symm

end MeetSpan


section PairwiseMeets

variable
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]

/-- The first two A3 mirror planes are distinct. -/
theorem wyler_pi1_ne_pi2
    (T : CoxeterA3TetrahedralFrame Geo) :
    Ne T.pi1 T.pi2 := by

  intro hEq
  apply T.A_off_pi1
  rw [hEq]
  exact T.A_on_pi2

/-- The last two A3 mirror planes are distinct. -/
theorem wyler_pi2_ne_pi3
    (T : CoxeterA3TetrahedralFrame Geo) :
    Ne T.pi2 T.pi3 := by

  intro hEq
  apply T.B_off_pi2
  rw [hEq]
  exact T.B_on_pi3

/-- The distant A3 mirror planes are distinct. -/
theorem wyler_pi1_ne_pi3
    (T : CoxeterA3TetrahedralFrame Geo) :
    Ne T.pi1 T.pi3 := by

  intro hEq
  apply T.A_off_pi1
  rw [hEq]
  exact T.A_on_pi3

variable
    [HilbertPlaneIncidence Geo]
    [HSI : HilbertSpaceIncidence Geo]

/--
Wyler meet calculation for the adjacent mirrors pi1 and pi2.

Their exact carrier intersection is a line carrier, and D lies on that line.
-/
theorem wyler_pi1_meet_pi2_line_through_D
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 : Geo.Line,
      H.OnLine T.D q12 /\
      HilbertLineInPlane Geo q12 T.pi1 /\
      HilbertLineInPlane Geo q12 T.pi2 /\
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi2) =
      HilbertLineCarrier3D Geo q12 := by

  exact
    euclid_proposition_11_3_via_meet
      (Geo := Geo)
      T.pi1 T.pi2
      (wyler_pi1_ne_pi2 (Geo := Geo) T)
      T.D
      T.D_on_pi1
      T.D_on_pi2

/--
Wyler meet calculation for the adjacent mirrors pi2 and pi3.

Their exact carrier intersection is a line carrier, and A lies on that line.
-/
theorem wyler_pi2_meet_pi3_line_through_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q23 : Geo.Line,
      H.OnLine T.A q23 /\
      HilbertLineInPlane Geo q23 T.pi2 /\
      HilbertLineInPlane Geo q23 T.pi3 /\
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi2)
        (HilbertPlaneCarrier3D Geo T.pi3) =
      HilbertLineCarrier3D Geo q23 := by

  exact
    euclid_proposition_11_3_via_meet
      (Geo := Geo)
      T.pi2 T.pi3
      (wyler_pi2_ne_pi3 (Geo := Geo) T)
      T.A
      T.A_on_pi2
      T.A_on_pi3

/--
Package the two adjacent A3 meet lines at once.

This is the flat-incidence skeleton for the two braid pairs.
-/
theorem wyler_adjacent_mirror_meets
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 : Geo.Line,
      H.OnLine T.D q12 /\
      H.OnLine T.A q23 /\
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi2) =
        HilbertLineCarrier3D Geo q12 /\
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi2)
        (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q23 := by

  rcases
      wyler_pi1_meet_pi2_line_through_D
        (Geo := Geo) T with
    ⟨q12, hDq12, _hq12pi1, _hq12pi2, hMeet12⟩

  rcases
      wyler_pi2_meet_pi3_line_through_A
        (Geo := Geo) T with
    ⟨q23, hAq23, _hq23pi2, _hq23pi3, hMeet23⟩

  exact
    ⟨q12, q23,
     hDq12, hAq23,
     hMeet12, hMeet23⟩

end PairwiseMeets


section MeetPackage

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]

/--
The complete pairwise Wyler meet data for the three A3 mirror planes.
-/
theorem wyler_all_three_mirror_meets
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 q13 : Geo.Line,
      H.OnLine T.D q12 /\
      H.OnLine T.A q23 /\
      H.OnLine T.F1 q13 /\
      H.OnLine T.F3 q13 /\
      HilbertLineInPlane Geo q12 T.pi1 /\
      HilbertLineInPlane Geo q12 T.pi2 /\
      HilbertLineInPlane Geo q23 T.pi2 /\
      HilbertLineInPlane Geo q23 T.pi3 /\
      HilbertLineInPlane Geo q13 T.pi1 /\
      HilbertLineInPlane Geo q13 T.pi3 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) =
        HilbertLineCarrier3D Geo q12 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q23 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q13 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) := by

  rcases
      wyler_pi1_meet_pi2_line_through_D
        (Geo := Geo) T with
    ⟨q12, hDq12, hq12pi1, hq12pi2, hMeet12⟩

  rcases
      wyler_pi2_meet_pi3_line_through_A
        (Geo := Geo) T with
    ⟨q23, hAq23, hq23pi2, hq23pi3, hMeet23⟩

  have hF1 :=
    wyler_F1_on_pi1_and_pi3
      (Geo := Geo) T

  have hF3 :=
    wyler_F3_on_pi1_and_pi3
      (Geo := Geo) T

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi1 T.pi3
        (wyler_pi1_ne_pi3 (Geo := Geo) T)
        T.F1
        hF1.1 hF1.2 with
    ⟨q13, hF1q13, hq13pi1, hq13pi3, hMeet13⟩

  have hF3Meet :
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi3)
        T.F3 :=
    ⟨hF3.1, hF3.2⟩

  have hF3q13 : H.OnLine T.F3 q13 := by
    change HilbertLineCarrier3D Geo q13 T.F3
    rw [← hMeet13]
    exact hF3Meet

  have hMeet13Span :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) :=
    wyler_pi1_meet_pi3_eq_span_F1_F3
      (Geo := Geo) T

  exact
    ⟨q12, q23, q13,
     hDq12,
     hAq23,
     hF1q13,
     hF3q13,
     hq12pi1,
     hq12pi2,
     hq23pi2,
     hq23pi3,
     hq13pi1,
     hq13pi3,
     hMeet12,
     hMeet23,
     hMeet13,
     hMeet13Span⟩

/--
A compact corollary: every pair of A3 mirrors has rank-one meet.
-/
theorem wyler_each_mirror_pair_meets_in_line
    (T : CoxeterA3TetrahedralFrame Geo) :
    (exists q12 : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) =
        HilbertLineCarrier3D Geo q12) /\
    (exists q23 : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q23) /\
    (exists q13 : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q13) := by

  rcases
      wyler_all_three_mirror_meets
        (Geo := Geo) T with
    ⟨q12, q23, q13,
     _hDq12, _hAq23, _hF1q13, _hF3q13,
     _hq12pi1, _hq12pi2,
     _hq23pi2, _hq23pi3,
     _hq13pi1, _hq13pi3,
     hMeet12, hMeet23, hMeet13, _hMeet13Span⟩

  exact
    ⟨⟨q12, hMeet12⟩,
     ⟨q23, hMeet23⟩,
     ⟨q13, hMeet13⟩⟩

end MeetPackage


section JoinMeetCalculus

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
The second endpoint D of the edge CD is off the third mirror pi3.

The frame stores only C_off_pi3.  Since reflection in pi3 sends C to D,
if D were on pi3 then the second reflection would fix D.  Involutivity
would then force D = C, contradicting the midpoint data for CD.
-/
theorem wyler_D_off_pi3
    (T : CoxeterA3TetrahedralFrame Geo) :
    Not (S.OnPlane T.D T.pi3) := by

  intro hDpi3

  have hCD : Ne T.C T.D :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.C T.F3 T.D
      T.F3_mid_CD.1).2.2.1

  have hReflectC :
      planeReflect Geo T.pi3 T.C = T.D := by
    calc
      planeReflect Geo T.pi3 T.C =
          r3 (Geo := Geo) T T.C :=
        (r3_apply (Geo := Geo) T T.C).symm
      _ = T.D :=
        r3_C (Geo := Geo) T

  have hReflectD :
      planeReflect Geo T.pi3 T.D = T.D :=
    planeReflect_of_on_plane
      (Geo := Geo)
      T.pi3 T.D
      hDpi3

  have hInv :=
    planeReflect_involutive
      (Geo := Geo)
      T.pi3 T.C

  rw [hReflectC, hReflectD] at hInv

  exact hCD hInv.symm

/--
The three pairwise mirror-intersection lines are pairwise distinct.
-/
theorem wyler_three_meet_lines_pairwise_ne
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 q13 : Geo.Line,
      Ne q12 q23 /\
      Ne q12 q13 /\
      Ne q23 q13 /\
      HilbertLineInPlane Geo q12 T.pi1 /\
      HilbertLineInPlane Geo q12 T.pi2 /\
      HilbertLineInPlane Geo q23 T.pi2 /\
      HilbertLineInPlane Geo q23 T.pi3 /\
      HilbertLineInPlane Geo q13 T.pi1 /\
      HilbertLineInPlane Geo q13 T.pi3 := by

  rcases
      wyler_all_three_mirror_meets
        (Geo := Geo) T with
    ⟨q12, q23, q13,
     hDq12, hAq23, _hF1q13, _hF3q13,
     hq12pi1, hq12pi2,
     hq23pi2, hq23pi3,
     hq13pi1, hq13pi3,
     _hMeet12, _hMeet23, _hMeet13, _hMeet13Span⟩

  have hq12q23 : Ne q12 q23 := by
    intro hEq
    have hAq12 : H.OnLine T.A q12 := by
      rw [hEq]
      exact hAq23
    exact T.A_off_pi1 (hq12pi1 T.A hAq12)

  have hq12q13 : Ne q12 q13 := by
    intro hEq
    have hDq13 : H.OnLine T.D q13 := by
      rw [← hEq]
      exact hDq12
    exact
      (wyler_D_off_pi3 (Geo := Geo) T)
        (hq13pi3 T.D hDq13)

  have hq23q13 : Ne q23 q13 := by
    intro hEq
    have hAq13 : H.OnLine T.A q13 := by
      rw [← hEq]
      exact hAq23
    exact T.A_off_pi1 (hq13pi1 T.A hAq13)

  exact
    ⟨q12, q23, q13,
     hq12q23, hq12q13, hq23q13,
     hq12pi1, hq12pi2,
     hq23pi2, hq23pi3,
     hq13pi1, hq13pi3⟩

/--
Closed Wyler incidence calculus for the A3 mirror arrangement.

The three meet lines reconstruct all three mirror planes by joins.
-/
theorem wyler_A3_mirror_join_meet_calculus
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 q13 : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) =
        HilbertLineCarrier3D Geo q12 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q23 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q13 /\
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q12)
          (HilbertLineCarrier3D Geo q13) =
        HilbertPlaneCarrier3D Geo T.pi1 /\
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q12)
          (HilbertLineCarrier3D Geo q23) =
        HilbertPlaneCarrier3D Geo T.pi2 /\
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q23)
          (HilbertLineCarrier3D Geo q13) =
        HilbertPlaneCarrier3D Geo T.pi3 := by

  rcases
      wyler_all_three_mirror_meets
        (Geo := Geo) T with
    ⟨q12, q23, q13,
     hDq12, hAq23, _hF1q13, _hF3q13,
     hq12pi1, hq12pi2,
     hq23pi2, hq23pi3,
     hq13pi1, hq13pi3,
     hMeet12, hMeet23, hMeet13, _hMeet13Span⟩

  have hq12q23 : Ne q12 q23 := by
    intro hEq
    have hAq12 : H.OnLine T.A q12 := by
      rw [hEq]
      exact hAq23
    exact T.A_off_pi1 (hq12pi1 T.A hAq12)

  have hq12q13 : Ne q12 q13 := by
    intro hEq
    have hDq13 : H.OnLine T.D q13 := by
      rw [← hEq]
      exact hDq12
    exact
      (wyler_D_off_pi3 (Geo := Geo) T)
        (hq13pi3 T.D hDq13)

  have hq23q13 : Ne q23 q13 := by
    intro hEq
    have hAq13 : H.OnLine T.A q13 := by
      rw [← hEq]
      exact hAq23
    exact T.A_off_pi1 (hq13pi1 T.A hAq13)

  have hJoin1 :
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q12)
          (HilbertLineCarrier3D Geo q13) =
        HilbertPlaneCarrier3D Geo T.pi1 :=
    hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
      (Geo := Geo)
      T.pi1 q12 q13
      hq12q13
      hq12pi1 hq13pi1

  have hJoin2 :
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q12)
          (HilbertLineCarrier3D Geo q23) =
        HilbertPlaneCarrier3D Geo T.pi2 :=
    hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
      (Geo := Geo)
      T.pi2 q12 q23
      hq12q23
      hq12pi2 hq23pi2

  have hJoin3 :
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q23)
          (HilbertLineCarrier3D Geo q13) =
        HilbertPlaneCarrier3D Geo T.pi3 :=
    hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
      (Geo := Geo)
      T.pi3 q23 q13
      hq23q13
      hq23pi3 hq13pi3

  exact
    ⟨q12, q23, q13,
     hMeet12, hMeet23, hMeet13,
     hJoin1, hJoin2, hJoin3⟩

end JoinMeetCalculus


section FixedLinesAndCoxeter

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
A line contained in pi1 and pi2 is pointwise fixed by r1 and r2.
-/
theorem wyler_common_fixed_of_line_in_pi1_pi2
    (T : CoxeterA3TetrahedralFrame Geo)
    (q : Geo.Line)
    (hq1 : HilbertLineInPlane Geo q T.pi1)
    (hq2 : HilbertLineInPlane Geo q T.pi2) :
    forall P : Geo.Point,
      H.OnLine P q ->
      r1 (Geo := Geo) T P = P /\
      r2 (Geo := Geo) T P = P := by

  intro P hPq

  have hPpi1 : S.OnPlane P T.pi1 :=
    hq1 P hPq

  have hPpi2 : S.OnPlane P T.pi2 :=
    hq2 P hPq

  constructor

  · rw [r1_apply]
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        T.pi1 P hPpi1

  · rw [r2_apply]
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        T.pi2 P hPpi2

/--
A line contained in pi2 and pi3 is pointwise fixed by r2 and r3.
-/
theorem wyler_common_fixed_of_line_in_pi2_pi3
    (T : CoxeterA3TetrahedralFrame Geo)
    (q : Geo.Line)
    (hq2 : HilbertLineInPlane Geo q T.pi2)
    (hq3 : HilbertLineInPlane Geo q T.pi3) :
    forall P : Geo.Point,
      H.OnLine P q ->
      r2 (Geo := Geo) T P = P /\
      r3 (Geo := Geo) T P = P := by

  intro P hPq

  have hPpi2 : S.OnPlane P T.pi2 :=
    hq2 P hPq

  have hPpi3 : S.OnPlane P T.pi3 :=
    hq3 P hPq

  constructor

  · rw [r2_apply]
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        T.pi2 P hPpi2

  · rw [r3_apply]
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        T.pi3 P hPpi3

/--
A line contained in pi1 and pi3 is pointwise fixed by r1 and r3.
-/
theorem wyler_common_fixed_of_line_in_pi1_pi3
    (T : CoxeterA3TetrahedralFrame Geo)
    (q : Geo.Line)
    (hq1 : HilbertLineInPlane Geo q T.pi1)
    (hq3 : HilbertLineInPlane Geo q T.pi3) :
    forall P : Geo.Point,
      H.OnLine P q ->
      r1 (Geo := Geo) T P = P /\
      r3 (Geo := Geo) T P = P := by

  intro P hPq

  have hPpi1 : S.OnPlane P T.pi1 :=
    hq1 P hPq

  have hPpi3 : S.OnPlane P T.pi3 :=
    hq3 P hPq

  constructor

  · rw [r1_apply]
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        T.pi1 P hPpi1

  · rw [r3_apply]
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        T.pi3 P hPpi3

/--
The three Wyler meet lines of the A3 mirror arrangement are common fixed
lines of the corresponding pairs of reflections.
-/
theorem wyler_A3_meet_lines_are_common_fixed_lines
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 q13 : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) =
        HilbertLineCarrier3D Geo q12 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q23 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q13 /\
      (forall P : Geo.Point,
        H.OnLine P q12 ->
        r1 (Geo := Geo) T P = P /\
        r2 (Geo := Geo) T P = P) /\
      (forall P : Geo.Point,
        H.OnLine P q23 ->
        r2 (Geo := Geo) T P = P /\
        r3 (Geo := Geo) T P = P) /\
      (forall P : Geo.Point,
        H.OnLine P q13 ->
        r1 (Geo := Geo) T P = P /\
        r3 (Geo := Geo) T P = P) := by

  rcases
      wyler_all_three_mirror_meets
        (Geo := Geo) T with
    ⟨q12, q23, q13,
     _hDq12, _hAq23, _hF1q13, _hF3q13,
     hq12pi1, hq12pi2,
     hq23pi2, hq23pi3,
     hq13pi1, hq13pi3,
     hMeet12, hMeet23, hMeet13, _hMeet13Span⟩

  have hFix12 :=
    wyler_common_fixed_of_line_in_pi1_pi2
      (Geo := Geo) T q12
      hq12pi1 hq12pi2

  have hFix23 :=
    wyler_common_fixed_of_line_in_pi2_pi3
      (Geo := Geo) T q23
      hq23pi2 hq23pi3

  have hFix13 :=
    wyler_common_fixed_of_line_in_pi1_pi3
      (Geo := Geo) T q13
      hq13pi1 hq13pi3

  exact
    ⟨q12, q23, q13,
     hMeet12, hMeet23, hMeet13,
     hFix12, hFix23, hFix13⟩

/--
Wyler flat calculus and the Coxeter exponents for A3 in one statement.

The same three mirror pairs have:
* rank-one meets q12,q23,q13;
* pairwise joins reconstructing pi1,pi2,pi3;
* common fixed lines q12,q23,q13;
* Coxeter periods 3,3,2.
-/
theorem wyler_A3_flat_Coxeter_package
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 q13 : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) =
        HilbertLineCarrier3D Geo q12 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q23 /\
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertLineCarrier3D Geo q13 /\
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q12)
          (HilbertLineCarrier3D Geo q13) =
        HilbertPlaneCarrier3D Geo T.pi1 /\
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q12)
          (HilbertLineCarrier3D Geo q23) =
        HilbertPlaneCarrier3D Geo T.pi2 /\
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo q23)
          (HilbertLineCarrier3D Geo q13) =
        HilbertPlaneCarrier3D Geo T.pi3 /\
      (forall P : Geo.Point,
        H.OnLine P q12 ->
        r1 (Geo := Geo) T P = P /\
        r2 (Geo := Geo) T P = P) /\
      (forall P : Geo.Point,
        H.OnLine P q23 ->
        r2 (Geo := Geo) T P = P /\
        r3 (Geo := Geo) T P = P) /\
      (forall P : Geo.Point,
        H.OnLine P q13 ->
        r1 (Geo := Geo) T P = P /\
        r3 (Geo := Geo) T P = P) /\
      ((r12 (Geo := Geo) T).trans
          (r12 (Geo := Geo) T)).trans
          (r12 (Geo := Geo) T) =
        Equiv.refl Geo.Point /\
      ((r23 (Geo := Geo) T).trans
          (r23 (Geo := Geo) T)).trans
          (r23 (Geo := Geo) T) =
        Equiv.refl Geo.Point /\
      (r13 (Geo := Geo) T).trans
          (r13 (Geo := Geo) T) =
        Equiv.refl Geo.Point := by

  rcases
      wyler_A3_mirror_join_meet_calculus
        (Geo := Geo) T with
    ⟨q12, q23, q13,
     hMeet12, hMeet23, hMeet13,
     hJoin1, hJoin2, hJoin3⟩

  have hq12pi1 : HilbertLineInPlane Geo q12 T.pi1 := by
    intro P hPq
    have hMeetP :
        Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) P := by
      rw [hMeet12]
      exact hPq
    exact hMeetP.1

  have hq12pi2 : HilbertLineInPlane Geo q12 T.pi2 := by
    intro P hPq
    have hMeetP :
        Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi2) P := by
      rw [hMeet12]
      exact hPq
    exact hMeetP.2

  have hq23pi2 : HilbertLineInPlane Geo q23 T.pi2 := by
    intro P hPq
    have hMeetP :
        Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) P := by
      rw [hMeet23]
      exact hPq
    exact hMeetP.1

  have hq23pi3 : HilbertLineInPlane Geo q23 T.pi3 := by
    intro P hPq
    have hMeetP :
        Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo T.pi3) P := by
      rw [hMeet23]
      exact hPq
    exact hMeetP.2

  have hq13pi1 : HilbertLineInPlane Geo q13 T.pi1 := by
    intro P hPq
    have hMeetP :
        Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) P := by
      rw [hMeet13]
      exact hPq
    exact hMeetP.1

  have hq13pi3 : HilbertLineInPlane Geo q13 T.pi3 := by
    intro P hPq
    have hMeetP :
        Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) P := by
      rw [hMeet13]
      exact hPq
    exact hMeetP.2

  have hFix12 :=
    wyler_common_fixed_of_line_in_pi1_pi2
      (Geo := Geo) T q12
      hq12pi1 hq12pi2

  have hFix23 :=
    wyler_common_fixed_of_line_in_pi2_pi3
      (Geo := Geo) T q23
      hq23pi2 hq23pi3

  have hFix13 :=
    wyler_common_fixed_of_line_in_pi1_pi3
      (Geo := Geo) T q13
      hq13pi1 hq13pi3

  exact
    ⟨q12, q23, q13,
     hMeet12, hMeet23, hMeet13,
     hJoin1, hJoin2, hJoin3,
     hFix12, hFix23, hFix13,
     r12_cube_eq_refl (Geo := Geo) T,
     r23_cube_eq_refl (Geo := Geo) T,
     r13_sq_eq_refl (Geo := Geo) T⟩

end FixedLinesAndCoxeter


section ExactFixedLoci

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
The meet of pi1 and pi2 is exactly the common fixed-point set of r1 and r2.
-/
theorem wyler_pi1_pi2_meet_eq_commonFixed12
    (T : CoxeterA3TetrahedralFrame Geo) :
    Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi2) =
      {P : Geo.Point |
        r1 (Geo := Geo) T P = P /\
        r2 (Geo := Geo) T P = P} := by

  ext P
  constructor

  · intro hMeet

    have hFix1 :
        planeReflect Geo T.pi1 P = P :=
      (planeReflect_fixed_iff_on_plane
        (Geo := Geo)
        T.pi1 P).2 hMeet.1

    have hFix2 :
        planeReflect Geo T.pi2 P = P :=
      (planeReflect_fixed_iff_on_plane
        (Geo := Geo)
        T.pi2 P).2 hMeet.2

    exact
      ⟨by
        rw [r1_apply]
        exact hFix1,
       by
        rw [r2_apply]
        exact hFix2⟩

  · intro hFix

    have hFix1 :
        planeReflect Geo T.pi1 P = P := by
      rw [← r1_apply (Geo := Geo) T P]
      exact hFix.1

    have hFix2 :
        planeReflect Geo T.pi2 P = P := by
      rw [← r2_apply (Geo := Geo) T P]
      exact hFix.2

    exact
      ⟨(planeReflect_fixed_iff_on_plane
          (Geo := Geo)
          T.pi1 P).1 hFix1,
       (planeReflect_fixed_iff_on_plane
          (Geo := Geo)
          T.pi2 P).1 hFix2⟩

/--
The meet of pi2 and pi3 is exactly the common fixed-point set of r2 and r3.
-/
theorem wyler_pi2_pi3_meet_eq_commonFixed23
    (T : CoxeterA3TetrahedralFrame Geo) :
    Set.inter
        (HilbertPlaneCarrier3D Geo T.pi2)
        (HilbertPlaneCarrier3D Geo T.pi3) =
      {P : Geo.Point |
        r2 (Geo := Geo) T P = P /\
        r3 (Geo := Geo) T P = P} := by

  ext P
  constructor

  · intro hMeet

    have hFix2 :
        planeReflect Geo T.pi2 P = P :=
      (planeReflect_fixed_iff_on_plane
        (Geo := Geo)
        T.pi2 P).2 hMeet.1

    have hFix3 :
        planeReflect Geo T.pi3 P = P :=
      (planeReflect_fixed_iff_on_plane
        (Geo := Geo)
        T.pi3 P).2 hMeet.2

    exact
      ⟨by
        rw [r2_apply]
        exact hFix2,
       by
        rw [r3_apply]
        exact hFix3⟩

  · intro hFix

    have hFix2 :
        planeReflect Geo T.pi2 P = P := by
      rw [← r2_apply (Geo := Geo) T P]
      exact hFix.1

    have hFix3 :
        planeReflect Geo T.pi3 P = P := by
      rw [← r3_apply (Geo := Geo) T P]
      exact hFix.2

    exact
      ⟨(planeReflect_fixed_iff_on_plane
          (Geo := Geo)
          T.pi2 P).1 hFix2,
       (planeReflect_fixed_iff_on_plane
          (Geo := Geo)
          T.pi3 P).1 hFix3⟩

/--
The meet of pi1 and pi3 is exactly the common fixed-point set of r1 and r3.
-/
theorem wyler_pi1_pi3_meet_eq_commonFixed13
    (T : CoxeterA3TetrahedralFrame Geo) :
    Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo T.pi3) =
      {P : Geo.Point |
        r1 (Geo := Geo) T P = P /\
        r3 (Geo := Geo) T P = P} := by

  ext P
  constructor

  · intro hMeet

    have hFix1 :
        planeReflect Geo T.pi1 P = P :=
      (planeReflect_fixed_iff_on_plane
        (Geo := Geo)
        T.pi1 P).2 hMeet.1

    have hFix3 :
        planeReflect Geo T.pi3 P = P :=
      (planeReflect_fixed_iff_on_plane
        (Geo := Geo)
        T.pi3 P).2 hMeet.2

    exact
      ⟨by
        rw [r1_apply]
        exact hFix1,
       by
        rw [r3_apply]
        exact hFix3⟩

  · intro hFix

    have hFix1 :
        planeReflect Geo T.pi1 P = P := by
      rw [← r1_apply (Geo := Geo) T P]
      exact hFix.1

    have hFix3 :
        planeReflect Geo T.pi3 P = P := by
      rw [← r3_apply (Geo := Geo) T P]
      exact hFix.2

    exact
      ⟨(planeReflect_fixed_iff_on_plane
          (Geo := Geo)
          T.pi1 P).1 hFix1,
       (planeReflect_fixed_iff_on_plane
          (Geo := Geo)
          T.pi3 P).1 hFix3⟩

/--
The three Wyler meet lines are exactly the common fixed loci of the
three generator pairs.
-/
theorem wyler_A3_meet_lines_eq_commonFixed_loci
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists q12 q23 q13 : Geo.Line,
      HilbertLineCarrier3D Geo q12 =
        {P : Geo.Point |
          r1 (Geo := Geo) T P = P /\
          r2 (Geo := Geo) T P = P} /\
      HilbertLineCarrier3D Geo q23 =
        {P : Geo.Point |
          r2 (Geo := Geo) T P = P /\
          r3 (Geo := Geo) T P = P} /\
      HilbertLineCarrier3D Geo q13 =
        {P : Geo.Point |
          r1 (Geo := Geo) T P = P /\
          r3 (Geo := Geo) T P = P} := by

  rcases
      wyler_A3_mirror_join_meet_calculus
        (Geo := Geo) T with
    ⟨q12, q23, q13,
     hMeet12, hMeet23, hMeet13,
     _hJoin1, _hJoin2, _hJoin3⟩

  have hFix12 :=
    wyler_pi1_pi2_meet_eq_commonFixed12
      (Geo := Geo) T

  have hFix23 :=
    wyler_pi2_pi3_meet_eq_commonFixed23
      (Geo := Geo) T

  have hFix13 :=
    wyler_pi1_pi3_meet_eq_commonFixed13
      (Geo := Geo) T

  have hLine12 :
      HilbertLineCarrier3D Geo q12 =
        {P : Geo.Point |
          r1 (Geo := Geo) T P = P /\
          r2 (Geo := Geo) T P = P} := by
    rw [← hMeet12]
    exact hFix12

  have hLine23 :
      HilbertLineCarrier3D Geo q23 =
        {P : Geo.Point |
          r2 (Geo := Geo) T P = P /\
          r3 (Geo := Geo) T P = P} := by
    rw [← hMeet23]
    exact hFix23

  have hLine13 :
      HilbertLineCarrier3D Geo q13 =
        {P : Geo.Point |
          r1 (Geo := Geo) T P = P /\
          r3 (Geo := Geo) T P = P} := by
    rw [← hMeet13]
    exact hFix13

  exact
    ⟨q12, q23, q13,
     hLine12, hLine23, hLine13⟩

end ExactFixedLoci


section ActiveSlice12

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]

/--
The adjacent pair pi1,pi2 has the active section sigma = plane(A,B,C).

The two mirror traces in sigma are exact Wyler meets:
* a1 = pi1 meet sigma, through F1 and C;
* a2 = pi2 meet sigma, through F2 and A.
-/
theorem wyler_adjacent12_active_slice_lines
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      S.OnPlane T.A sigma /\
      S.OnPlane T.B sigma /\
      S.OnPlane T.C sigma /\
      exists a1 a2 : Geo.Line,
        H.OnLine T.F1 a1 /\
        H.OnLine T.C a1 /\
        H.OnLine T.F2 a2 /\
        H.OnLine T.A a2 /\
        HilbertLineInPlane Geo a1 T.pi1 /\
        HilbertLineInPlane Geo a1 sigma /\
        HilbertLineInPlane Geo a2 T.pi2 /\
        HilbertLineInPlane Geo a2 sigma /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo a1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo a2 := by

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.C T.D
      T.noncoplanar

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        T.A T.B T.C
        hABC with
    ⟨sigma, hAsigma, hBsigma, hCsigma⟩

  ----------------------------------------------------------------------
  -- F1 lies in sigma, because F1 lies on AB.
  ----------------------------------------------------------------------

  have hMid1 :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.A T.F1 T.B
      T.F1_mid_AB.1

  have hAB : Ne T.A T.B :=
    hMid1.2.2.1

  rcases hMid1.2.2.2.1 with
    ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

  have hlABsigma :
      HilbertLineInPlane Geo lAB sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      T.A T.B hAB
      lAB hAlAB hBlAB
      sigma hAsigma hBsigma

  have hF1sigma :
      S.OnPlane T.F1 sigma :=
    hlABsigma T.F1 hF1lAB

  have hF1pi1 :
      S.OnPlane T.F1 T.pi1 :=
    (wyler_F1_on_pi1_and_pi3
      (Geo := Geo) T).1

  have hF1C : Ne T.F1 T.C := by
    intro hEq

    have hClAB : H.OnLine T.C lAB := by
      rw [← hEq]
      exact hF1lAB

    exact
      hABC
        ⟨lAB, hAlAB, hBlAB, hClAB⟩

  have hPi1Sigma : Ne T.pi1 sigma := by
    intro hEq
    apply T.A_off_pi1
    rw [hEq]
    exact hAsigma

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi1 sigma
        hPi1Sigma
        T.F1
        hF1pi1
        hF1sigma with
    ⟨a1,
     hF1a1,
     ha1pi1,
     ha1sigma,
     hMeet1⟩

  have hCMeet1 :
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi1)
        (HilbertPlaneCarrier3D Geo sigma)
        T.C :=
    ⟨T.C_on_pi1, hCsigma⟩

  have hCa1 : H.OnLine T.C a1 := by
    change HilbertLineCarrier3D Geo a1 T.C
    rw [← hMeet1]
    exact hCMeet1

  ----------------------------------------------------------------------
  -- F2 lies in sigma, because F2 lies on BC.
  ----------------------------------------------------------------------

  have hMid2 :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.B T.F2 T.C
      T.F2_mid_BC.1

  have hBC : Ne T.B T.C :=
    hMid2.2.2.1

  rcases hMid2.2.2.2.1 with
    ⟨lBC, hBlBC, hF2lBC, hClBC⟩

  have hlBCsigma :
      HilbertLineInPlane Geo lBC sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      T.B T.C hBC
      lBC hBlBC hClBC
      sigma hBsigma hCsigma

  have hF2sigma :
      S.OnPlane T.F2 sigma :=
    hlBCsigma T.F2 hF2lBC

  rcases T.BC_perp_pi2 with
    ⟨_n2, _hBn2, hPerp2⟩

  have hF2pi2 :
      S.OnPlane T.F2 T.pi2 :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp2).2

  have hF2A : Ne T.F2 T.A := by
    intro hEq

    have hAlBC : H.OnLine T.A lBC := by
      rw [← hEq]
      exact hF2lBC

    exact
      hABC
        ⟨lBC, hAlBC, hBlBC, hClBC⟩

  have hPi2Sigma : Ne T.pi2 sigma := by
    intro hEq
    apply T.B_off_pi2
    rw [hEq]
    exact hBsigma

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi2 sigma
        hPi2Sigma
        T.F2
        hF2pi2
        hF2sigma with
    ⟨a2,
     hF2a2,
     ha2pi2,
     ha2sigma,
     hMeet2⟩

  have hAMeet2 :
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi2)
        (HilbertPlaneCarrier3D Geo sigma)
        T.A :=
    ⟨T.A_on_pi2, hAsigma⟩

  have hAa2 : H.OnLine T.A a2 := by
    change HilbertLineCarrier3D Geo a2 T.A
    rw [← hMeet2]
    exact hAMeet2

  exact
    ⟨sigma,
     hAsigma, hBsigma, hCsigma,
     a1, a2,
     hF1a1, hCa1,
     hF2a2, hAa2,
     ha1pi1, ha1sigma,
     ha2pi2, ha2sigma,
     hMeet1, hMeet2⟩

/--
The two traces in the active section ABC define genuine planar
reflection axes.

The first axis has distinguished points F1,C.
The second axis has distinguished points F2,A.
-/
theorem wyler_adjacent12_active_slice_axes
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      exists axis1 axis2 :
        ReflectionAxis (PlaneGeo Geo sigma),
        S.OnPlane T.A sigma /\
        S.OnPlane T.B sigma /\
        S.OnPlane T.C sigma /\
        HilbertLineInPlane
          Geo axis1.carrier.1 T.pi1 /\
        HilbertLineInPlane
          Geo axis2.carrier.1 T.pi2 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo axis1.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo axis2.carrier.1 := by

  rcases
      wyler_adjacent12_active_slice_lines
        (Geo := Geo) T with
    ⟨sigma,
     hAsigma, hBsigma, hCsigma,
     a1, a2,
     hF1a1, hCa1,
     hF2a2, hAa2,
     ha1pi1, ha1sigma,
     ha2pi2, ha2sigma,
     hMeet1, hMeet2⟩

  have hF1C : Ne T.F1 T.C := by
    intro hEq

    have hABC :
        Not (PrimCollinear Geo T.A T.B T.C) :=
      hilbert_noncoplanar4_not_collinear_first_three
        (Geo := Geo)
        T.A T.B T.C T.D
        T.noncoplanar

    have hMid1 :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        T.A T.F1 T.B
        T.F1_mid_AB.1

    rcases hMid1.2.2.2.1 with
      ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

    have hClAB : H.OnLine T.C lAB := by
      rw [← hEq]
      exact hF1lAB

    exact
      hABC
        ⟨lAB, hAlAB, hBlAB, hClAB⟩

  have hF2A : Ne T.F2 T.A := by
    intro hEq

    have hABC :
        Not (PrimCollinear Geo T.A T.B T.C) :=
      hilbert_noncoplanar4_not_collinear_first_three
        (Geo := Geo)
        T.A T.B T.C T.D
        T.noncoplanar

    have hMid2 :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        T.B T.F2 T.C
        T.F2_mid_BC.1

    rcases hMid2.2.2.2.1 with
      ⟨lBC, hBlBC, hF2lBC, hClBC⟩

    have hAlBC : H.OnLine T.A lBC := by
      rw [← hEq]
      exact hF2lBC

    exact
      hABC
        ⟨lBC, hAlBC, hBlBC, hClBC⟩

  let F1p : PlanePoint Geo sigma :=
    ⟨T.F1, ha1sigma T.F1 hF1a1⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨T.C, hCsigma⟩

  let F2p : PlanePoint Geo sigma :=
    ⟨T.F2, ha2sigma T.F2 hF2a2⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨T.A, hAsigma⟩

  let a1p : PlaneLine Geo sigma :=
    ⟨a1, ha1sigma⟩

  let a2p : PlaneLine Geo sigma :=
    ⟨a2, ha2sigma⟩

  have hF1Cp : Ne F1p Cp := by
    intro hEq
    apply hF1C
    exact congrArg Subtype.val hEq

  have hF2Ap : Ne F2p Ap := by
    intro hEq
    apply hF2A
    exact congrArg Subtype.val hEq

  let axis1 :
      ReflectionAxis (PlaneGeo Geo sigma) :=
    { carrier := a1p
      A := F1p
      B := Cp
      hAB := hF1Cp
      hA := hF1a1
      hB := hCa1 }

  let axis2 :
      ReflectionAxis (PlaneGeo Geo sigma) :=
    { carrier := a2p
      A := F2p
      B := Ap
      hAB := hF2Ap
      hA := hF2a2
      hB := hAa2 }

  exact
    ⟨sigma,
     axis1, axis2,
     hAsigma, hBsigma, hCsigma,
     ha1pi1,
     ha2pi2,
     hMeet1,
     hMeet2⟩

end ActiveSlice12


section ReflectionReduction12

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
On the active slice ABC, the ambient reflection r1 is the planar line
reflection in the trace pi1 meet sigma, at least on the distinguished
point A.  The image is B.
-/
theorem wyler_adjacent12_r1_reduces_to_lineReflect_on_A
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      exists axis1 :
        ReflectionAxis (PlaneGeo Geo sigma),
        exists Ap Bp :
          PlanePoint Geo sigma,
          Ap.1 = T.A /\
          Bp.1 = T.B /\
          lineReflect
              (PlaneGeo Geo sigma)
              axis1 Ap =
            Bp /\
          r1 (Geo := Geo) T T.A = T.B := by

  rcases
      wyler_adjacent12_active_slice_lines
        (Geo := Geo) T with
    ⟨sigma,
     hAsigma, hBsigma, hCsigma,
     a1, _a2,
     hF1a1, hCa1,
     _hF2a2, _hAa2,
     ha1pi1, ha1sigma,
     _ha2pi2, _ha2sigma,
     _hMeet1, _hMeet2⟩

  let F1p : PlanePoint Geo sigma :=
    ⟨T.F1, ha1sigma T.F1 hF1a1⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨T.C, hCsigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨T.A, hAsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨T.B, hBsigma⟩

  let a1p : PlaneLine Geo sigma :=
    ⟨a1, ha1sigma⟩

  have hF1C : Ne T.F1 T.C := by
    intro hEq

    have hABC :
        Not (PrimCollinear Geo T.A T.B T.C) :=
      hilbert_noncoplanar4_not_collinear_first_three
        (Geo := Geo)
        T.A T.B T.C T.D
        T.noncoplanar

    have hMid1 :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        T.A T.F1 T.B
        T.F1_mid_AB.1

    rcases hMid1.2.2.2.1 with
      ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

    have hClAB : H.OnLine T.C lAB := by
      rw [← hEq]
      exact hF1lAB

    exact
      hABC
        ⟨lAB, hAlAB, hBlAB, hClAB⟩

  have hF1Cp : Ne F1p Cp := by
    intro hEq
    apply hF1C
    exact congrArg Subtype.val hEq

  let axis1 :
      ReflectionAxis (PlaneGeo Geo sigma) :=
    { carrier := a1p
      A := F1p
      B := Cp
      hAB := hF1Cp
      hA := hF1a1
      hB := hCa1 }

  rcases T.AB_perp_pi1 with
    ⟨n1, hAn1, hPerp1⟩

  have hLineReflect :
      lineReflect
          (PlaneGeo Geo sigma)
          axis1 Ap =
        Bp := by

    exact
      planeReflect_eq_lineReflect_in_slice
        (Geo := Geo)
        T.pi1 sigma axis1
        Ap F1p Cp Bp
        n1
        T.A_off_pi1
        ha1pi1
        hF1a1
        hCa1
        hF1Cp.symm
        hAn1
        hPerp1
        T.F1_mid_AB

  exact
    ⟨sigma,
     axis1,
     Ap, Bp,
     rfl, rfl,
     hLineReflect,
     r1_A (Geo := Geo) T⟩

/--
On the same active slice ABC, the ambient reflection r2 is the planar
line reflection in the trace pi2 meet sigma, at the distinguished
point B.  The image is C.
-/
theorem wyler_adjacent12_r2_reduces_to_lineReflect_on_B
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      exists axis2 :
        ReflectionAxis (PlaneGeo Geo sigma),
        exists Bp Cp :
          PlanePoint Geo sigma,
          Bp.1 = T.B /\
          Cp.1 = T.C /\
          lineReflect
              (PlaneGeo Geo sigma)
              axis2 Bp =
            Cp /\
          r2 (Geo := Geo) T T.B = T.C := by

  rcases
      wyler_adjacent12_active_slice_lines
        (Geo := Geo) T with
    ⟨sigma,
     hAsigma, hBsigma, hCsigma,
     _a1, a2,
     _hF1a1, _hCa1,
     hF2a2, hAa2,
     _ha1pi1, _ha1sigma,
     ha2pi2, ha2sigma,
     _hMeet1, _hMeet2⟩

  let F2p : PlanePoint Geo sigma :=
    ⟨T.F2, ha2sigma T.F2 hF2a2⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨T.A, hAsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨T.B, hBsigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨T.C, hCsigma⟩

  let a2p : PlaneLine Geo sigma :=
    ⟨a2, ha2sigma⟩

  have hF2A : Ne T.F2 T.A := by
    intro hEq

    have hABC :
        Not (PrimCollinear Geo T.A T.B T.C) :=
      hilbert_noncoplanar4_not_collinear_first_three
        (Geo := Geo)
        T.A T.B T.C T.D
        T.noncoplanar

    have hMid2 :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        T.B T.F2 T.C
        T.F2_mid_BC.1

    rcases hMid2.2.2.2.1 with
      ⟨lBC, hBlBC, hF2lBC, hClBC⟩

    have hAlBC : H.OnLine T.A lBC := by
      rw [← hEq]
      exact hF2lBC

    exact
      hABC
        ⟨lBC, hAlBC, hBlBC, hClBC⟩

  have hF2Ap : Ne F2p Ap := by
    intro hEq
    apply hF2A
    exact congrArg Subtype.val hEq

  let axis2 :
      ReflectionAxis (PlaneGeo Geo sigma) :=
    { carrier := a2p
      A := F2p
      B := Ap
      hAB := hF2Ap
      hA := hF2a2
      hB := hAa2 }

  rcases T.BC_perp_pi2 with
    ⟨n2, hBn2, hPerp2⟩

  have hLineReflect :
      lineReflect
          (PlaneGeo Geo sigma)
          axis2 Bp =
        Cp := by

    exact
      planeReflect_eq_lineReflect_in_slice
        (Geo := Geo)
        T.pi2 sigma axis2
        Bp F2p Ap Cp
        n2
        T.B_off_pi2
        ha2pi2
        hF2a2
        hAa2
        hF2Ap.symm
        hBn2
        hPerp2
        T.F2_mid_BC

  exact
    ⟨sigma,
     axis2,
     Bp, Cp,
     rfl, rfl,
     hLineReflect,
     r2_B (Geo := Geo) T⟩

/--
Both adjacent generators admit planar line-reflection realizations in
the common active section ABC.
-/
theorem wyler_adjacent12_both_generators_planar_on_vertices
    (T : CoxeterA3TetrahedralFrame Geo) :
    (exists sigma : S.Plane,
      exists axis1 :
        ReflectionAxis (PlaneGeo Geo sigma),
        exists Ap Bp :
          PlanePoint Geo sigma,
          Ap.1 = T.A /\
          Bp.1 = T.B /\
          lineReflect
              (PlaneGeo Geo sigma)
              axis1 Ap =
            Bp) /\
    (exists sigma : S.Plane,
      exists axis2 :
        ReflectionAxis (PlaneGeo Geo sigma),
        exists Bp Cp :
          PlanePoint Geo sigma,
          Bp.1 = T.B /\
          Cp.1 = T.C /\
          lineReflect
              (PlaneGeo Geo sigma)
              axis2 Bp =
            Cp) := by

  rcases
      wyler_adjacent12_r1_reduces_to_lineReflect_on_A
        (Geo := Geo) T with
    ⟨sigma1, axis1, Ap, Bp,
     hAval, hBval, hLine1, _hr1⟩

  rcases
      wyler_adjacent12_r2_reduces_to_lineReflect_on_B
        (Geo := Geo) T with
    ⟨sigma2, axis2, Bp2, Cp,
     hBval2, hCval, hLine2, _hr2⟩

  exact
    ⟨⟨sigma1, axis1, Ap, Bp,
       hAval, hBval, hLine1⟩,
     ⟨sigma2, axis2, Bp2, Cp,
       hBval2, hCval, hLine2⟩⟩

end ReflectionReduction12


section PlanarPeriodThree12

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
The planar exact-period-three axes obtained from the equilateral triangle
A,C,B have the same geometric carrier lines as the two Wyler mirror traces:

* planar axis a has carrier pi2 meet sigma = AF2;
* planar axis b has carrier pi1 meet sigma = CF1.

No equality of `ReflectionAxis` records is required; only carrier equality
is geometrically meaningful here.
-/
theorem wyler_adjacent12_planar_period_three_axes_match_traces
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      exists a1 a2 : Geo.Line,
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo a1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo a2 /\
        exists a b :
          ReflectionAxis (PlaneGeo Geo sigma),
          a.carrier.1 = a2 /\
          b.carrier.1 = a1 /\
          ReflectionPairExactPeriod
            (PlaneGeo Geo sigma) a b 3 := by

  rcases
      wyler_adjacent12_active_slice_lines
        (Geo := Geo) T with
    ⟨sigma,
     hAsigma, hBsigma, hCsigma,
     a1, a2,
     hF1a1, hCa1,
     hF2a2, hAa2,
     _ha1pi1, ha1sigma,
     _ha2pi2, ha2sigma,
     hMeet1, hMeet2⟩

  ----------------------------------------------------------------------
  -- The three vertices and the two known midpoints inside PlaneGeo sigma.
  ----------------------------------------------------------------------

  let Ap : PlanePoint Geo sigma :=
    ⟨T.A, hAsigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨T.C, hCsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨T.B, hBsigma⟩

  let F1p : PlanePoint Geo sigma :=
    ⟨T.F1, ha1sigma T.F1 hF1a1⟩

  let F2p : PlanePoint Geo sigma :=
    ⟨T.F2, ha2sigma T.F2 hF2a2⟩

  ----------------------------------------------------------------------
  -- Noncollinearity of the ordered triangle A,C,B.
  ----------------------------------------------------------------------

  have hABCambient :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.C T.D
      T.noncoplanar

  have hACBambient :
      Not (PrimCollinear Geo T.A T.C T.B) := by
    intro h
    rcases h with
      ⟨l, hAl, hCl, hBl⟩
    exact
      hABCambient
        ⟨l, hAl, hBl, hCl⟩

  have hACBplane :
      Not
        (Collinear
          (PlaneGeo Geo sigma)
          Ap Cp Bp) := by
    intro hCol
    exact
      hACBambient
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma Ap Cp Bp
          hCol)

  ----------------------------------------------------------------------
  -- Equilateral side data in the ambient space.
  --
  -- pi2 fixes A and exchanges B,C, hence AC ~= AB.
  -- pi1 fixes C and exchanges A,B, hence CA ~= CB.
  ----------------------------------------------------------------------

  have hAC_AB_ambient :
      Geo.Congruent T.A T.C T.A T.B := by
    have h :=
      planeReflect_preserves_congruence
        (Geo := Geo)
        T.pi2
        T.A T.C
    rw [
      ← r2_apply (Geo := Geo) T T.A,
      ← r2_apply (Geo := Geo) T T.C,
      r2_A (Geo := Geo) T,
      r2_C (Geo := Geo) T
    ] at h
    exact h

  have hCA_CB_ambient :
      Geo.Congruent T.C T.A T.C T.B := by
    have h :=
      planeReflect_preserves_congruence
        (Geo := Geo)
        T.pi1
        T.C T.A
    rw [
      ← r1_apply (Geo := Geo) T T.C,
      ← r1_apply (Geo := Geo) T T.A,
      r1_C (Geo := Geo) T,
      r1_A (Geo := Geo) T
    ] at h
    exact h

  ----------------------------------------------------------------------
  -- Transfer the two directly obtained side equalities into PlaneGeo.
  --
  -- All remaining congruence algebra is deliberately done locally in the
  -- slice.  We do NOT install or require ambient `HilbertCongruence Geo`.
  ----------------------------------------------------------------------

  have hAC_AB_plane :
      (PlaneGeo Geo sigma).Congruent
        Ap Cp Ap Bp := by
    exact
      (planeGeo_congruent
        (Geo := Geo)
        sigma Ap Cp Ap Bp).mpr
        hAC_AB_ambient

  have hCA_CB_plane :
      (PlaneGeo Geo sigma).Congruent
        Cp Ap Cp Bp := by
    exact
      (planeGeo_congruent
        (Geo := Geo)
        sigma Cp Ap Cp Bp).mpr
        hCA_CB_ambient

  ----------------------------------------------------------------------
  -- Third equilateral side relation, entirely inside PlaneGeo:
  --
  --   CA ~= CB
  --   => AC ~= CB
  --   => CB ~= AC
  --   => BC ~= AC
  --   and AC ~= AB
  --   => BC ~= AB
  --   => BC ~= BA.
  ----------------------------------------------------------------------

  have hAC_CB_plane :
      (PlaneGeo Geo sigma).Congruent
        Ap Cp Cp Bp :=
    (Geometry.Geo.congruent_reverse_first
      (PlaneGeo Geo sigma)
      Cp Ap Cp Bp).mp
      hCA_CB_plane

  have hCB_AC_plane :
      (PlaneGeo Geo sigma).Congruent
        Cp Bp Ap Cp :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo sigma)
      Ap Cp Cp Bp
      hAC_CB_plane

  have hBC_AC_plane :
      (PlaneGeo Geo sigma).Congruent
        Bp Cp Ap Cp :=
    (Geometry.Geo.congruent_reverse_first
      (PlaneGeo Geo sigma)
      Cp Bp Ap Cp).mp
      hCB_AC_plane

  have hBC_AB_plane :
      (PlaneGeo Geo sigma).Congruent
        Bp Cp Ap Bp :=
    hilbert_congruent_transitivity
      (PlaneGeo Geo sigma)
      Bp Cp
      Ap Cp
      Ap Bp
      hBC_AC_plane
      hAC_AB_plane

  have hBC_BA_plane :
      (PlaneGeo Geo sigma).Congruent
        Bp Cp Bp Ap :=
    (Geometry.Geo.congruent_reverse_second
      (PlaneGeo Geo sigma)
      Bp Cp Ap Bp).mp
      hBC_AB_plane

  ----------------------------------------------------------------------
  -- The two stored tetrahedral midpoints become planar midpoints.
  ----------------------------------------------------------------------

  have hF1midPlane :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        F1p Ap Bp := by
    constructor
    · exact
        (planeGeo_between
          (Geo := Geo)
          sigma Ap F1p Bp).mpr
          T.F1_mid_AB.1
    · exact
        (planeGeo_congruent
          (Geo := Geo)
          sigma Ap F1p F1p Bp).mpr
          T.F1_mid_AB.2

  have hF2midPlaneBC :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        F2p Bp Cp := by
    constructor
    · exact
        (planeGeo_between
          (Geo := Geo)
          sigma Bp F2p Cp).mpr
          T.F2_mid_BC.1
    · exact
        (planeGeo_congruent
          (Geo := Geo)
          sigma Bp F2p F2p Cp).mpr
          T.F2_mid_BC.2

  have hF2midPlane :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        F2p Cp Bp :=
    MidpointSymmetry
      (PlaneGeo Geo sigma)
      F2p Bp Cp
      hF2midPlaneBC

  ----------------------------------------------------------------------
  -- The third midpoint: midpoint of C,A, constructed inside the slice.
  ----------------------------------------------------------------------

  have hCAambient : Ne T.C T.A :=
    (hilbert_noncollinear_ne_first
      Geo
      T.A T.C T.B
      hACBambient).symm

  have hCAp : Ne Cp Ap := by
    intro h
    apply hCAambient
    exact congrArg Subtype.val h

  rcases
      HilbertMidpointExists
        (PlaneGeo Geo sigma)
        Cp Ap hCAp with
    ⟨MCp, hMCmidPlane⟩

  ----------------------------------------------------------------------
  -- Apply the already proved planar p = 3 theorem to A,C,B.
  ----------------------------------------------------------------------

  rcases
      equilateral_median_reflections_exact_period_three
        (PlaneGeo Geo sigma)
        Ap Cp Bp
        F2p F1p MCp
        hACBplane
        hAC_AB_plane
        hCA_CB_plane
        hBC_BA_plane
        hF2midPlane
        hF1midPlane
        hMCmidPlane with
    ⟨a, b, _c,
     hAa, hF2a,
     hCb, hF1b,
     _hBc, _hMCc,
     hExact3⟩

  ----------------------------------------------------------------------
  -- Match the planar theorem's first two median carriers with the
  -- Wyler mirror traces a2 and a1.
  ----------------------------------------------------------------------

  have hAF2ambient : Ne T.A T.F2 := by
    intro hAF2

    have hMid2 :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        T.B T.F2 T.C
        T.F2_mid_BC.1

    rcases hMid2.2.2.2.1 with
      ⟨lBC, hBlBC, hF2lBC, hClBC⟩

    have hAlBC : H.OnLine T.A lBC := by
      rw [hAF2]
      exact hF2lBC

    exact
      hABCambient
        ⟨lBC, hAlBC, hBlBC, hClBC⟩

  have hCF1ambient : Ne T.C T.F1 := by
    intro hCF1

    have hMid1 :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        T.A T.F1 T.B
        T.F1_mid_AB.1

    rcases hMid1.2.2.2.1 with
      ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

    have hClAB : H.OnLine T.C lAB := by
      rw [hCF1]
      exact hF1lAB

    exact
      hABCambient
        ⟨lAB, hAlAB, hBlAB, hClAB⟩

  have hAaAmbient :
      H.OnLine T.A a.carrier.1 :=
    hAa

  have hF2aAmbient :
      H.OnLine T.F2 a.carrier.1 :=
    hF2a

  have hCbAmbient :
      H.OnLine T.C b.carrier.1 :=
    hCb

  have hF1bAmbient :
      H.OnLine T.F1 b.carrier.1 :=
    hF1b

  have haCarrier :
      a.carrier.1 = a2 :=
    HilbertPlaneIncidence.line_unique
      T.A T.F2
      hAF2ambient
      a.carrier.1 a2
      hAaAmbient hF2aAmbient
      hAa2 hF2a2

  have hbCarrier :
      b.carrier.1 = a1 :=
    HilbertPlaneIncidence.line_unique
      T.C T.F1
      hCF1ambient
      b.carrier.1 a1
      hCbAmbient hF1bAmbient
      hCa1 hF1a1

  exact
    ⟨sigma,
     a1, a2,
     hMeet1, hMeet2,
     a, b,
     haCarrier,
     hbCarrier,
     hExact3⟩

end PlanarPeriodThree12


section ExactPeriod12

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
The exact Coxeter exponent m12 = 3 lives directly on the two Wyler
mirror traces in the active section ABC.

The returned planar axes have exactly the carrier lines

  pi1 meet sigma
  pi2 meet sigma

in the natural mirror order.
-/
theorem wyler_adjacent12_traces_exact_period_three
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      exists axis1 axis2 :
        ReflectionAxis (PlaneGeo Geo sigma),
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo axis1.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo axis2.carrier.1 /\
        ReflectionPairExactPeriod
          (PlaneGeo Geo sigma)
          axis1 axis2 3 := by

  rcases
      wyler_adjacent12_planar_period_three_axes_match_traces
        (Geo := Geo) T with
    ⟨sigma,
     a1, a2,
     hMeet1, hMeet2,
     a, b,
     haCarrier,
     hbCarrier,
     hExactAB⟩

  have hMeetAxis1 :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo sigma) =
        HilbertLineCarrier3D Geo b.carrier.1 := by

    simpa [hbCarrier] using hMeet1

  have hMeetAxis2 :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo sigma) =
        HilbertLineCarrier3D Geo a.carrier.1 := by

    simpa [haCarrier] using hMeet2

  have hExactBA :
      ReflectionPairExactPeriod
        (PlaneGeo Geo sigma)
        b a 3 :=
    reflectionPairExactPeriod_symm
      (PlaneGeo Geo sigma)
      a b
      3
      hExactAB

  exact
    ⟨sigma,
     b, a,
     hMeetAxis1,
     hMeetAxis2,
     hExactBA⟩

end ExactPeriod12


section ExactPeriod23

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
The second adjacent pair of mirror traces has exact planar Coxeter period 3.

The returned axes are in the natural mirror order:
* axis2 is the trace of pi2;
* axis3 is the trace of pi3.
-/
theorem wyler_adjacent23_traces_exact_period_three
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists sigma : S.Plane,
      exists axis2 axis3 :
        ReflectionAxis (PlaneGeo Geo sigma),
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo axis2.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi3)
            (HilbertPlaneCarrier3D Geo sigma) =
          HilbertLineCarrier3D Geo axis3.carrier.1 /\
        ReflectionPairExactPeriod
          (PlaneGeo Geo sigma)
          axis2 axis3 3 := by

  ----------------------------------------------------------------------
  -- Noncollinearity of B,D,C from tetrahedral noncoplanarity.
  ----------------------------------------------------------------------

  have hNoncopBDCA :
      Not (HilbertCoplanar4 Geo T.B T.D T.C T.A) := by
    intro h
    rcases h with
      ⟨pi, hBpi, hDpi, hCpi, hApi⟩
    exact
      T.noncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hBDC :
      Not (PrimCollinear Geo T.B T.D T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.B T.D T.C T.A
      hNoncopBDCA

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        T.B T.D T.C
        hBDC with
    ⟨sigma, hBsigma, hDsigma, hCsigma⟩

  ----------------------------------------------------------------------
  -- F2 lies in sigma because it lies on BC.
  ----------------------------------------------------------------------

  have hMid2 :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.B T.F2 T.C
      T.F2_mid_BC.1

  have hBC : Ne T.B T.C :=
    hMid2.2.2.1

  rcases hMid2.2.2.2.1 with
    ⟨lBC, hBlBC, hF2lBC, hClBC⟩

  have hlBCsigma :
      HilbertLineInPlane Geo lBC sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      T.B T.C hBC
      lBC hBlBC hClBC
      sigma hBsigma hCsigma

  have hF2sigma :
      S.OnPlane T.F2 sigma :=
    hlBCsigma T.F2 hF2lBC

  rcases T.BC_perp_pi2 with
    ⟨_n2, _hBn2, hPerp2⟩

  have hF2pi2 :
      S.OnPlane T.F2 T.pi2 :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp2).2

  have hPi2Sigma : Ne T.pi2 sigma := by
    intro hEq
    apply T.B_off_pi2
    rw [hEq]
    exact hBsigma

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi2 sigma
        hPi2Sigma
        T.F2
        hF2pi2
        hF2sigma with
    ⟨a2,
     hF2a2,
     ha2pi2,
     ha2sigma,
     hMeet2⟩

  have hDMeet2 :
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi2)
        (HilbertPlaneCarrier3D Geo sigma)
        T.D :=
    ⟨T.D_on_pi2, hDsigma⟩

  have hDa2 : H.OnLine T.D a2 := by
    change HilbertLineCarrier3D Geo a2 T.D
    rw [← hMeet2]
    exact hDMeet2

  ----------------------------------------------------------------------
  -- F3 lies in sigma because it lies on CD.
  ----------------------------------------------------------------------

  have hMid3 :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.C T.F3 T.D
      T.F3_mid_CD.1

  have hCD : Ne T.C T.D :=
    hMid3.2.2.1

  rcases hMid3.2.2.2.1 with
    ⟨lCD, hClCD, hF3lCD, hDlCD⟩

  have hlCDsigma :
      HilbertLineInPlane Geo lCD sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      T.C T.D hCD
      lCD hClCD hDlCD
      sigma hCsigma hDsigma

  have hF3sigma :
      S.OnPlane T.F3 sigma :=
    hlCDsigma T.F3 hF3lCD

  rcases T.CD_perp_pi3 with
    ⟨_n3, _hCn3, hPerp3⟩

  have hF3pi3 :
      S.OnPlane T.F3 T.pi3 :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp3).2

  have hPi3Sigma : Ne T.pi3 sigma := by
    intro hEq
    apply T.C_off_pi3
    rw [hEq]
    exact hCsigma

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi3 sigma
        hPi3Sigma
        T.F3
        hF3pi3
        hF3sigma with
    ⟨a3,
     hF3a3,
     ha3pi3,
     ha3sigma,
     hMeet3⟩

  have hBMeet3 :
      Set.inter
        (HilbertPlaneCarrier3D Geo T.pi3)
        (HilbertPlaneCarrier3D Geo sigma)
        T.B :=
    ⟨T.B_on_pi3, hBsigma⟩

  have hBa3 : H.OnLine T.B a3 := by
    change HilbertLineCarrier3D Geo a3 T.B
    rw [← hMeet3]
    exact hBMeet3

  ----------------------------------------------------------------------
  -- PlaneGeo points.
  ----------------------------------------------------------------------

  let Bp : PlanePoint Geo sigma :=
    ⟨T.B, hBsigma⟩

  let Dp : PlanePoint Geo sigma :=
    ⟨T.D, hDsigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨T.C, hCsigma⟩

  let F2p : PlanePoint Geo sigma :=
    ⟨T.F2, ha2sigma T.F2 hF2a2⟩

  let F3p : PlanePoint Geo sigma :=
    ⟨T.F3, ha3sigma T.F3 hF3a3⟩

  have hBDCplane :
      Not
        (Collinear
          (PlaneGeo Geo sigma)
          Bp Dp Cp) := by
    intro hCol
    exact
      hBDC
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          sigma Bp Dp Cp
          hCol)

  ----------------------------------------------------------------------
  -- Equilateral side data for the ordered triangle B,D,C.
  --
  -- pi3 fixes B and exchanges D,C: BD ~= BC.
  -- pi2 fixes D and exchanges B,C: DB ~= DC.
  ----------------------------------------------------------------------

  have hBD_BC_ambient :
      Geo.Congruent T.B T.D T.B T.C := by
    have h :=
      planeReflect_preserves_congruence
        (Geo := Geo)
        T.pi3
        T.B T.D
    rw [
      ← r3_apply (Geo := Geo) T T.B,
      ← r3_apply (Geo := Geo) T T.D,
      r3_B (Geo := Geo) T,
      r3_D (Geo := Geo) T
    ] at h
    exact h

  have hDB_DC_ambient :
      Geo.Congruent T.D T.B T.D T.C := by
    have h :=
      planeReflect_preserves_congruence
        (Geo := Geo)
        T.pi2
        T.D T.B
    rw [
      ← r2_apply (Geo := Geo) T T.D,
      ← r2_apply (Geo := Geo) T T.B,
      r2_D (Geo := Geo) T,
      r2_B (Geo := Geo) T
    ] at h
    exact h

  have hBD_BC_plane :
      (PlaneGeo Geo sigma).Congruent
        Bp Dp Bp Cp := by
    exact
      (planeGeo_congruent
        (Geo := Geo)
        sigma Bp Dp Bp Cp).mpr
        hBD_BC_ambient

  have hDB_DC_plane :
      (PlaneGeo Geo sigma).Congruent
        Dp Bp Dp Cp := by
    exact
      (planeGeo_congruent
        (Geo := Geo)
        sigma Dp Bp Dp Cp).mpr
        hDB_DC_ambient

  ----------------------------------------------------------------------
  -- Third side relation CD ~= CB, locally inside PlaneGeo.
  ----------------------------------------------------------------------

  have hBD_CD_plane :
      (PlaneGeo Geo sigma).Congruent
        Bp Dp Cp Dp :=
    (Geometry.Geo.congruent_reverse_second
      (PlaneGeo Geo sigma)
      Bp Dp Dp Cp).mp
      ((Geometry.Geo.congruent_reverse_first
        (PlaneGeo Geo sigma)
        Dp Bp Dp Cp).mp
        hDB_DC_plane)

  have hCD_BD_plane :
      (PlaneGeo Geo sigma).Congruent
        Cp Dp Bp Dp :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo sigma)
      Bp Dp Cp Dp
      hBD_CD_plane

  have hCD_BC_plane :
      (PlaneGeo Geo sigma).Congruent
        Cp Dp Bp Cp :=
    hilbert_congruent_transitivity
      (PlaneGeo Geo sigma)
      Cp Dp
      Bp Dp
      Bp Cp
      hCD_BD_plane
      hBD_BC_plane

  have hCD_CB_plane :
      (PlaneGeo Geo sigma).Congruent
        Cp Dp Cp Bp :=
    (Geometry.Geo.congruent_reverse_second
      (PlaneGeo Geo sigma)
      Cp Dp Bp Cp).mp
      hCD_BC_plane

  ----------------------------------------------------------------------
  -- Midpoints for the planar theorem.
  --
  -- F3 is midpoint of D,C after symmetry.
  -- F2 is midpoint of B,C as stored.
  -- The midpoint of D,B is constructed locally.
  ----------------------------------------------------------------------

  have hF3midPlaneCD :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        F3p Cp Dp := by
    constructor
    · exact
        (planeGeo_between
          (Geo := Geo)
          sigma Cp F3p Dp).mpr
          T.F3_mid_CD.1
    · exact
        (planeGeo_congruent
          (Geo := Geo)
          sigma Cp F3p F3p Dp).mpr
          T.F3_mid_CD.2

  have hF3midPlane :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        F3p Dp Cp :=
    MidpointSymmetry
      (PlaneGeo Geo sigma)
      F3p Cp Dp
      hF3midPlaneCD

  have hF2midPlane :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        F2p Bp Cp := by
    constructor
    · exact
        (planeGeo_between
          (Geo := Geo)
          sigma Bp F2p Cp).mpr
          T.F2_mid_BC.1
    · exact
        (planeGeo_congruent
          (Geo := Geo)
          sigma Bp F2p F2p Cp).mpr
          T.F2_mid_BC.2

  have hDB : Ne Dp Bp := by
    intro hEq
    have hDBambient : T.D = T.B :=
      congrArg Subtype.val hEq
    apply
      hilbert_noncollinear_ne_first
        Geo
        T.B T.D T.C
        hBDC
    exact hDBambient.symm

  rcases
      HilbertMidpointExists
        (PlaneGeo Geo sigma)
        Dp Bp hDB with
    ⟨MDBp, hMDBmidPlane⟩

  ----------------------------------------------------------------------
  -- Planar p = 3 theorem on the ordered triangle B,D,C.
  ----------------------------------------------------------------------

  rcases
      equilateral_median_reflections_exact_period_three
        (PlaneGeo Geo sigma)
        Bp Dp Cp
        F3p F2p MDBp
        hBDCplane
        hBD_BC_plane
        hDB_DC_plane
        hCD_CB_plane
        hF3midPlane
        hF2midPlane
        hMDBmidPlane with
    ⟨a, b, _c,
     hBa, hF3a,
     hDb, hF2b,
     _hCc, _hMDBc,
     hExactAB⟩

  ----------------------------------------------------------------------
  -- Match planar median carriers with the two Wyler mirror traces.
  ----------------------------------------------------------------------

  have hBF3 : Ne T.B T.F3 := by
    intro hEq

    have hClCD' : H.OnLine T.B lCD := by
      rw [hEq]
      exact hF3lCD

    exact
      hBDC
        ⟨lCD, hClCD', hDlCD, hClCD⟩

  have hDF2 : Ne T.D T.F2 := by
    intro hEq

    have hDlBC : H.OnLine T.D lBC := by
      rw [hEq]
      exact hF2lBC

    exact
      hBDC
        ⟨lBC, hBlBC, hDlBC, hClBC⟩

  have haCarrier :
      a.carrier.1 = a3 :=
    HilbertPlaneIncidence.line_unique
      T.B T.F3
      hBF3
      a.carrier.1 a3
      hBa hF3a
      hBa3 hF3a3

  have hbCarrier :
      b.carrier.1 = a2 :=
    HilbertPlaneIncidence.line_unique
      T.D T.F2
      hDF2
      b.carrier.1 a2
      hDb hF2b
      hDa2 hF2a2

  have hMeetAxis2 :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi2)
          (HilbertPlaneCarrier3D Geo sigma) =
        HilbertLineCarrier3D Geo b.carrier.1 := by
    simpa [hbCarrier] using hMeet2

  have hMeetAxis3 :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi3)
          (HilbertPlaneCarrier3D Geo sigma) =
        HilbertLineCarrier3D Geo a.carrier.1 := by
    simpa [haCarrier] using hMeet3

  have hExactBA :
      ReflectionPairExactPeriod
        (PlaneGeo Geo sigma)
        b a 3 :=
    reflectionPairExactPeriod_symm
      (PlaneGeo Geo sigma)
      a b
      3
      hExactAB

  exact
    ⟨sigma,
     b, a,
     hMeetAxis2,
     hMeetAxis3,
     hExactBA⟩

end ExactPeriod23


section ExactPeriod13

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]

/--
The distant A3 mirrors admit a normal planar section whose two exact
mirror traces are perpendicular reflection axes of exact Coxeter period 2.
-/
theorem wyler_distant13_normal_slice_exact_period_two
    (T : CoxeterA3TetrahedralFrame Geo) :
    exists N : S.Plane,
      exists axis1 axis3 :
        ReflectionAxis (PlaneGeo Geo N),
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo T.pi3) =
          HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo N) =
          HilbertLineCarrier3D Geo axis1.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi3)
            (HilbertPlaneCarrier3D Geo N) =
          HilbertLineCarrier3D Geo axis3.carrier.1 /\
        exists _hAxes :
          ReflectionAxesPerpendicular
            (PlaneGeo Geo N)
            axis1 axis3,
          ReflectionPairExactPeriod
            (PlaneGeo Geo N)
            axis1 axis3 2 := by

  ----------------------------------------------------------------------
  -- The two opposite edge carriers AB and CD.
  ----------------------------------------------------------------------

  have hMid1 :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.A T.F1 T.B
      T.F1_mid_AB.1

  have hAB : Ne T.A T.B :=
    hMid1.2.2.1

  have hAF1 : Ne T.A T.F1 :=
    hMid1.1

  rcases hMid1.2.2.2.1 with
    ⟨lAB, hAlAB, hF1lAB, hBlAB⟩

  have hMid3 :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      T.C T.F3 T.D
      T.F3_mid_CD.1

  have hCD : Ne T.C T.D :=
    hMid3.2.2.1

  rcases hMid3.2.2.2.1 with
    ⟨lCD, hClCD, hF3lCD, hDlCD⟩

  ----------------------------------------------------------------------
  -- AB lies in pi3 and CD lies in pi1.
  ----------------------------------------------------------------------

  have hlABpi3 :
      HilbertLineInPlane Geo lAB T.pi3 :=
    euclid_proposition_11_1_via_flats
      (Geo := Geo)
      T.pi3 lAB
      T.A T.B
      hAB
      hAlAB hBlAB
      T.A_on_pi3 T.B_on_pi3

  have hlCDpi1 :
      HilbertLineInPlane Geo lCD T.pi1 :=
    euclid_proposition_11_1_via_flats
      (Geo := Geo)
      T.pi1 lCD
      T.C T.D
      hCD
      hClCD hDlCD
      T.C_on_pi1 T.D_on_pi1

  have hF1 :=
    wyler_F1_on_pi1_and_pi3
      (Geo := Geo) T

  have hF3 :=
    wyler_F3_on_pi1_and_pi3
      (Geo := Geo) T

  ----------------------------------------------------------------------
  -- F1 is not on the opposite edge carrier CD.
  --
  -- Otherwise AB and CD would meet at F1 and XI.2 would put all four
  -- tetrahedral vertices in one plane.
  ----------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.C T.D
      T.noncoplanar

  have hlABCD : Ne lAB lCD := by
    intro hEq

    have hClAB : H.OnLine T.C lAB := by
      rw [hEq]
      exact hClCD

    exact
      hABC
        ⟨lAB, hAlAB, hBlAB, hClAB⟩

  have hF1notCD : Not (H.OnLine T.F1 lCD) := by
    intro hF1lCD

    rcases
        euclid_proposition_11_2_via_join
          (Geo := Geo)
          lAB lCD T.F1
          hlABCD
          hF1lAB hF1lCD with
      ⟨rho, hlABrho, hlCDrho, _hJoin⟩

    exact
      T.noncoplanar
        ⟨rho,
         hlABrho T.A hAlAB,
         hlABrho T.B hBlAB,
         hlCDrho T.C hClCD,
         hlCDrho T.D hDlCD⟩

  ----------------------------------------------------------------------
  -- Through F1 inside pi1 construct s parallel to CD.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI12_parallel_through_point_in_plane
        (Geo := Geo)
        T.pi1
        lCD
        T.F1
        hlCDpi1
        hF1.1
        hF1notCD with
    ⟨s, hF1s, hParallelCDS⟩

  rcases hParallelCDS with
    ⟨tau, hlCDtau, hstau, hDisjointCDS⟩

  ----------------------------------------------------------------------
  -- The carrier plane supplied by spatial parallelism is exactly pi1.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        lCD T.F1
        hF1notCD with
    ⟨rho, hlCDrho, hF1rho, hUniqueRho⟩

  have hTauRho : tau = rho :=
    hUniqueRho
      tau
      hlCDtau
      (hstau T.F1 hF1s)

  have hPi1Rho : T.pi1 = rho :=
    hUniqueRho
      T.pi1
      hlCDpi1
      hF1.1

  have hTauPi1 : tau = T.pi1 :=
    hTauRho.trans hPi1Rho.symm

  have hsPi1 :
      HilbertLineInPlane Geo s T.pi1 := by
    intro X hXs
    rw [← hTauPi1]
    exact hstau X hXs

  ----------------------------------------------------------------------
  -- AB is the actual normal carrier used by AB_perp_pi1.
  ----------------------------------------------------------------------

  rcases T.AB_perp_pi1 with
    ⟨n1, hAn1, hPerp1⟩

  have hF1n1 :
      H.OnLine T.F1 n1 :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp1).1

  have hn1AB : n1 = lAB :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      T.A T.F1
      hAF1
      n1 lAB
      hAn1 hF1n1
      hAlAB hF1lAB

  have hN1perpS :
      HilbertLinesPerpendicularAt
        Geo n1 s T.F1 :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp1
      hsPi1
      hF1s

  have hABperpS :
      HilbertLinesPerpendicularAt
        Geo lAB s T.F1 := by
    rw [← hn1AB]
    exact hN1perpS

  have hSperpAB :
      HilbertLinesPerpendicularAt
        Geo s lAB T.F1 :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      lAB s T.F1
      hABperpS

  have hSAB : Ne s lAB := by
    have h :
        Ne lAB s :=
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        lAB s T.F1
        hABperpS
    exact h.symm

  ----------------------------------------------------------------------
  -- The active normal section N is the plane generated by s and AB.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_2_via_join
        (Geo := Geo)
        s lAB T.F1
        hSAB
        hF1s hF1lAB with
    ⟨N, hsN, hABN, _hJoinN⟩

  have hF1N :
      S.OnPlane T.F1 N :=
    hsN T.F1 hF1s

  ----------------------------------------------------------------------
  -- Exact first trace: pi1 meet N = s.
  ----------------------------------------------------------------------

  have hPi1N : Ne T.pi1 N := by
    intro hEq
    apply T.A_off_pi1
    rw [hEq]
    exact hABN T.A hAlAB

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi1 N
        hPi1N
        T.F1
        hF1.1 hF1N with
    ⟨q1, hF1q1, _hq1pi1, _hq1N, hMeet1⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        s T.F1 with
    ⟨U, hUF1, hUs⟩

  have hUq1 : H.OnLine U q1 := by
    change HilbertLineCarrier3D Geo q1 U
    rw [← hMeet1]
    exact
      ⟨hsPi1 U hUs,
       hsN U hUs⟩

  have hq1s : q1 = s :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      T.F1 U
      hUF1.symm
      q1 s
      hF1q1 hUq1
      hF1s hUs

  have hTrace1 :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo N) =
        HilbertLineCarrier3D Geo s := by
    rw [hq1s] at hMeet1
    exact hMeet1

  ----------------------------------------------------------------------
  -- N cannot equal pi3.
  --
  -- If N = pi3, then the already identified first trace says that every
  -- point of pi1 meet pi3 lies on s.  In particular F3 lies on s, which
  -- contradicts the disjointness of the parallel lines CD and s.
  ----------------------------------------------------------------------

  have hPi3N : Ne T.pi3 N := by
    intro hEq

    have hF3N :
        S.OnPlane T.F3 N := by
      rw [← hEq]
      exact hF3.2

    have hF3s : H.OnLine T.F3 s := by
      change HilbertLineCarrier3D Geo s T.F3
      rw [← hTrace1]
      exact ⟨hF3.1, hF3N⟩

    exact
      hDisjointCDS
        ⟨T.F3, hF3lCD, hF3s⟩

  ----------------------------------------------------------------------
  -- Exact second trace: pi3 meet N = AB.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        T.pi3 N
        hPi3N
        T.F1
        hF1.2 hF1N with
    ⟨q3, hF1q3, _hq3pi3, _hq3N, hMeet3⟩

  have hAq3 : H.OnLine T.A q3 := by
    change HilbertLineCarrier3D Geo q3 T.A
    rw [← hMeet3]
    exact
      ⟨T.A_on_pi3,
       hABN T.A hAlAB⟩

  have hq3AB : q3 = lAB :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      T.F1 T.A
      hAF1.symm
      q3 lAB
      hF1q3 hAq3
      hF1lAB hAlAB

  have hTrace3 :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi3)
          (HilbertPlaneCarrier3D Geo N) =
        HilbertLineCarrier3D Geo lAB := by
    rw [hq3AB] at hMeet3
    exact hMeet3

  ----------------------------------------------------------------------
  -- Package s and AB as planar reflection axes in PlaneGeo N.
  ----------------------------------------------------------------------

  let F1p : PlanePoint Geo N :=
    ⟨T.F1, hF1N⟩

  let Up : PlanePoint Geo N :=
    ⟨U, hsN U hUs⟩

  let Ap : PlanePoint Geo N :=
    ⟨T.A, hABN T.A hAlAB⟩

  let sp : PlaneLine Geo N :=
    ⟨s, hsN⟩

  let abp : PlaneLine Geo N :=
    ⟨lAB, hABN⟩

  have hF1pUp : Ne F1p Up := by
    intro hEq
    apply hUF1
    exact
      (congrArg Subtype.val hEq).symm

  have hF1pAp : Ne F1p Ap := by
    intro hEq
    apply hAF1
    exact
      (congrArg Subtype.val hEq).symm

  let axis1 :
      ReflectionAxis (PlaneGeo Geo N) :=
    { carrier := sp
      A := F1p
      B := Up
      hAB := hF1pUp
      hA := hF1s
      hB := hUs }

  let axis3 :
      ReflectionAxis (PlaneGeo Geo N) :=
    { carrier := abp
      A := F1p
      B := Ap
      hAB := hF1pAp
      hA := hF1lAB
      hB := hAlAB }

  ----------------------------------------------------------------------
  -- Ambient perpendicularity becomes planar perpendicularity.
  ----------------------------------------------------------------------

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo N)
        sp abp F1p :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      N sp abp F1p).2
      hSperpAB

  rcases hPerpPlane with
    ⟨hF1sp, hF1abp,
     Xp, Yp,
     hXF1, hYF1,
     hXsp, hYabp,
     hNonXY, hRightXY⟩

  have hAxes :
      ReflectionAxesPerpendicular
        (PlaneGeo Geo N)
        axis1 axis3 :=
    { O := F1p
      U := Xp
      V := Yp
      hO1 := hF1sp
      hO2 := hF1abp
      hU1 := hXsp
      hV2 := hYabp
      hOU := hXF1.symm
      hOV := hYF1.symm
      hNonCol := hNonXY
      hRight := hRightXY }

  have hExact2 :
      ReflectionPairExactPeriod
        (PlaneGeo Geo N)
        axis1 axis3 2 :=
    perpendicular_axes_reflections_exact_period_two
      (PlaneGeo Geo N)
      axis1 axis3
      hAxes

  ----------------------------------------------------------------------
  -- The distant Wyler meet, retained in the final package.
  ----------------------------------------------------------------------

  have hDistantMeet :
      Set.inter
          (HilbertPlaneCarrier3D Geo T.pi1)
          (HilbertPlaneCarrier3D Geo T.pi3) =
        HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) :=
    wyler_pi1_meet_pi3_eq_span_F1_F3
      (Geo := Geo) T

  exact
    ⟨N,
     axis1, axis3,
     hDistantMeet,
     by simpa [axis1, sp] using hTrace1,
     by simpa [axis3, abp] using hTrace3,
     ⟨hAxes, hExact2⟩⟩

end ExactPeriod13


section LocalDiagram

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

/--
Local Coxeter diagram A3 obtained from Wyler mirror traces:

  m12 = 3,  m23 = 3,  m13 = 2.

Each exponent is realized in an explicit `PlaneGeo` slice by the exact
traces of the corresponding spatial mirrors.
-/
theorem wyler_A3_local_Coxeter_diagram
    (T : CoxeterA3TetrahedralFrame Geo) :

    (exists sigma12 : S.Plane,
      exists axis1 axis2 :
        ReflectionAxis (PlaneGeo Geo sigma12),
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo sigma12) =
          HilbertLineCarrier3D Geo axis1.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma12) =
          HilbertLineCarrier3D Geo axis2.carrier.1 /\
        ReflectionPairExactPeriod
          (PlaneGeo Geo sigma12)
          axis1 axis2 3) /\

    (exists sigma23 : S.Plane,
      exists axis2 axis3 :
        ReflectionAxis (PlaneGeo Geo sigma23),
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi2)
            (HilbertPlaneCarrier3D Geo sigma23) =
          HilbertLineCarrier3D Geo axis2.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi3)
            (HilbertPlaneCarrier3D Geo sigma23) =
          HilbertLineCarrier3D Geo axis3.carrier.1 /\
        ReflectionPairExactPeriod
          (PlaneGeo Geo sigma23)
          axis2 axis3 3) /\

    (exists N : S.Plane,
      exists axis1 axis3 :
        ReflectionAxis (PlaneGeo Geo N),
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo T.pi3) =
          HilbertSpan3D Geo ({T.F1, T.F3} : Set Geo.Point) /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi1)
            (HilbertPlaneCarrier3D Geo N) =
          HilbertLineCarrier3D Geo axis1.carrier.1 /\
        Set.inter
            (HilbertPlaneCarrier3D Geo T.pi3)
            (HilbertPlaneCarrier3D Geo N) =
          HilbertLineCarrier3D Geo axis3.carrier.1 /\
        exists _hAxes :
          ReflectionAxesPerpendicular
            (PlaneGeo Geo N)
            axis1 axis3,
          ReflectionPairExactPeriod
            (PlaneGeo Geo N)
            axis1 axis3 2) := by

  constructor

  · exact
      wyler_adjacent12_traces_exact_period_three
        (Geo := Geo) T

  constructor

  · exact
      wyler_adjacent23_traces_exact_period_three
        (Geo := Geo) T

  · exact
      wyler_distant13_normal_slice_exact_period_two
        (Geo := Geo) T

end LocalDiagram


end CoxeterA3TetrahedralFrame

end Geometry

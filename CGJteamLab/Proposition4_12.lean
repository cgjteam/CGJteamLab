import CGJteamLab.HilbertInterfaceIV

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Forder IV.12 and IV.12.1
Production module for Forder IV.12 and IV.12.1.
Reusable circle/order/angle helpers live in `HilbertInterfaceIV`.

Reusable circle/order/angle helpers live in `HilbertInterfaceIV`.
The construction and case analysis specific to IV.12 live here.
-/

private theorem hilbert_forder_IV12_1_of_IV12_aux
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV12 :
      HilbertForderIV12CentralHalf
        (Geo := Geo)) :
    HilbertForderIV12_1SameSegment
      (Geo := Geo) := by

  intro K R A B C D chord
    hAB hAchord hBchord
    hAcircle hBcircle hCcircle hDcircle
    hSameCK hSameDK

  --------------------------------------------------------------------
  -- Since K is off chord AB, the central angle AKB is genuine.
  --------------------------------------------------------------------

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hABK :
      Not (PrimCollinear Geo A B K) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B K
      chord
      hAB
      hAchord
      hBchord
      hKoff

  have hAKB :
      Not (PrimCollinear Geo A K B) := by
    intro h
    exact
      hABK
        (PrimCollinearRotate
          Geo A K B h)

  --------------------------------------------------------------------
  -- Apply IV.12 to C and D.
  --------------------------------------------------------------------

  rcases
      hIV12
        K R A B C
        chord
        hAB
        hAchord
        hBchord
        hAcircle
        hBcircle
        hCcircle
        hSameCK
    with
    ⟨T,
      hInsideT,
      hBisectT,
      hACB_AKT⟩

  rcases
      hIV12
        K R A B D
        chord
        hAB
        hAchord
        hBchord
        hAcircle
        hBcircle
        hDcircle
        hSameDK
    with
    ⟨U,
      hInsideU,
      hBisectU,
      hADB_AKU⟩

  --------------------------------------------------------------------
  -- T and U bisect the same nondegenerate central angle AKB.
  -- Uniqueness of angle halves gives AKT ~= AKU.
  --------------------------------------------------------------------

  have hAKT_AKU :
      Geo.AngleCongruent
        A K T
        A K U :=
    hilbert_angleDecomposition_angle_half_unique
      Geo
      K A B T U
      hAKB
      hInsideT
      hInsideU
      hBisectT
      hBisectU

  --------------------------------------------------------------------
  -- Transport the two inscribed angles through the common half.
  --------------------------------------------------------------------

  have hAKU_ADB :
      Geo.AngleCongruent
        A K U
        A D B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A D B
      A K U
      hADB_AKU

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C B
      A K T
      A D B
      hACB_AKT
      (Geometry.Geo.angle_congruent_transitivity
        Geo
        A K T
        A K U
        A D B
        hAKT_AKU
        hAKU_ADB)

private theorem hilbert_forder_IV12_addition_configuration
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (chord axis : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKX : Geo.Between C K X)
    (hOppAB : HilbertOppositeSide Geo A B axis) :
    exists Y : Geo.Point,
      Geo.Between A Y B /\
      Geo.Between C K Y /\
      HilbertRayMeetsSegment Geo K X A B /\
      HilbertRayMeetsSegment Geo C K A B := by

  --------------------------------------------------------------------
  -- The axis meets the open chord AB at Y.
  --------------------------------------------------------------------

  rcases hOppAB.2.2 with
    ⟨Y, hAYB, hYaxis⟩

  --------------------------------------------------------------------
  -- C lies on the same axis because C-K-X.
  --------------------------------------------------------------------

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX, hCline, hKline, hXline⟩

  have hEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hEq]
    exact hCline

  have hCKYcol :
      PrimCollinear Geo C K Y :=
    ⟨axis,
      hCaxis,
      hKaxis,
      hYaxis⟩

  --------------------------------------------------------------------
  -- Stage 21 gives the decisive order C-K-Y.
  --------------------------------------------------------------------

  have hCKY :
      Geo.Between C K Y :=
    hilbert_circle_chord_axis_order
      Geo
      K R A B C Y
      chord
      hAB
      hAchord
      hBchord
      hAcircle
      hBcircle
      hCcircle
      hSameCK
      hAYB
      hCKYcol

  --------------------------------------------------------------------
  -- Hence X and Y lie on the same ray from K.
  --------------------------------------------------------------------

  have hRayKXY :
      HilbertSameRay Geo K X Y :=
    hilbert_sameRay_beyond_common_middle
      Geo
      C K X Y
      hCKX
      hCKY

  have hInsideCentral :
      HilbertRayMeetsSegment Geo K X A B :=
    ⟨Y,
      hAYB,
      hRayKXY⟩

  --------------------------------------------------------------------
  -- And K and Y lie on the same ray from C.
  --------------------------------------------------------------------

  have hRayCKY :
      HilbertSameRay Geo C K Y :=
    hilbert_sameRay_of_between
      Geo C K Y hCKY

  have hInsideInscribed :
      HilbertRayMeetsSegment Geo C K A B :=
    ⟨Y,
      hAYB,
      hRayCKY⟩

  exact
    ⟨Y,
      hAYB,
      hCKY,
      hInsideCentral,
      hInsideInscribed⟩

private theorem hilbert_forder_IV12_addition_case
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (chord axis : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKX : Geo.Between C K X)
    (hOppAB : HilbertOppositeSide Geo A B axis) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hLineEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hLineEq]
    exact hCline

  --------------------------------------------------------------------
  -- A,K,C and B,K,C are noncollinear because A,B are off axis KX.
  --------------------------------------------------------------------

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    intro h

    have hKCA :
        PrimCollinear Geo K C A :=
      PrimCollinearCycle
        Geo A K C h

    have hAaxis :
        H.OnLine A axis :=
      hilbert_collinear_on_line
        Geo
        K C A
        axis
        hCK.symm
        hKaxis
        hCaxis
        hKCA

    exact hOppAB.1 hAaxis

  have hBKC :
      Not (PrimCollinear Geo B K C) := by
    intro h

    have hKCB :
        PrimCollinear Geo K C B :=
      PrimCollinearCycle
        Geo B K C h

    have hBaxis :
        H.OnLine B axis :=
      hilbert_collinear_on_line
        Geo
        K C B
        axis
        hCK.symm
        hKaxis
        hCaxis
        hKCB

    exact hOppAB.2.1 hBaxis

  --------------------------------------------------------------------
  -- The central angle AKB is proper because K is off chord AB.
  --------------------------------------------------------------------

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hAKB :
      Not (PrimCollinear Geo A K B) := by
    intro h

    have hABK :
        PrimCollinear Geo A B K :=
      PrimCollinearRotate
        Geo A K B h

    have hKchord :
        H.OnLine K chord :=
      hilbert_collinear_on_line
        Geo
        A B K
        chord
        hAB
        hAchord
        hBchord
        hABK

    exact hKoff hKchord

  --------------------------------------------------------------------
  -- Stage 22 supplies the two common interior dividers.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV12_addition_configuration
        Geo
        K R A B C X
        chord axis
        hAB
        hAchord
        hBchord
        hKaxis
        hXaxis
        hAcircle
        hBcircle
        hCcircle
        hSameCK
        hCKX
        hOppAB
    with
    ⟨_Y,
      _hAYB,
      _hCKY,
      hInsideX,
      hInsideK⟩

  --------------------------------------------------------------------
  -- Stage 19 supplies the two local doubled-angle blocks.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_exterior_central_half
        Geo
        K R A C X
        hAcircle
        hCcircle
        hAKC
        hCKX
    with
    ⟨T,
      hInsideT,
      hAKT_XKT,
      hACK_AKT⟩

  rcases
      hilbert_circle_exterior_central_half
        Geo
        K R B C X
        hBcircle
        hCcircle
        hBKC
        hCKX
    with
    ⟨U,
      hInsideU_BX,
      hBKU_XKU,
      hBCK_BKU⟩

  have hInsideU_XB :
      HilbertRayMeetsSegment Geo K U X B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K U B X
      hInsideU_BX

  --------------------------------------------------------------------
  -- Rearrange alpha,alpha,beta,beta into two equal alpha+beta halves.
  --------------------------------------------------------------------

  rcases
      hilbert_angleDecomposition_double_sum_bisector
        Geo
        A K B X T U
        hAKB
        hInsideX
        hInsideT
        hInsideU_XB
        hAKT_XKT
        hBKU_XKU
    with
    ⟨E,
      hInsideE,
      hInsideT_AE,
      _hInsideU_EB,
      hBisect,
      hTKE_BKU⟩

  --------------------------------------------------------------------
  -- ACB is proper because C is off chord AB.
  --------------------------------------------------------------------

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAKE :
      Not (PrimCollinear Geo A K E) :=
    (hilbert_interior_angle_less
      Geo
      K E A B
      hAKB
      hInsideE).1

  --------------------------------------------------------------------
  -- Match the two decompositions:
  --
  --   ACB = ACK + KCB
  --   AKE = AKT + TKE.
  --------------------------------------------------------------------

  have hKCB_BKU :
      Geo.AngleCongruent
        K C B
        B K U :=
    (Geo.angle_congruent_reverse_first
      B C K
      B K U).mp
      hBCK_BKU

  have hKCB_TKE :
      Geo.AngleCongruent
        K C B
        T K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K C B
      B K U
      T K E
      hKCB_BKU
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        T K E
        B K U
        hTKE_BKU)

  have hACB_AKE :
      Geo.AngleCongruent
        A C B
        A K E :=
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      C A B K
      K A E T
      hACB
      hAKE
      hInsideK
      hInsideT_AE
      hACK_AKT
      hKCB_TKE

  exact
    ⟨E,
      hInsideE,
      hBisect,
      hACB_AKE⟩

private theorem hilbert_forder_IV12_sameSide_ray_orders
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (K A B C X : Geo.Point)
    (axis : Geo.Line)
    (hCKX : Geo.Between C K X)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAoff : Not (H.OnLine A axis))
    (hBoff : Not (H.OnLine B axis))
    (hSameAB : HilbertSameSide Geo A B axis)
    (hAKB : Not (PrimCollinear Geo A K B))
    (hACB : Not (PrimCollinear Geo A C B)) :
    (HilbertRayMeetsSegment Geo K A B X \/
     HilbertRayMeetsSegment Geo K B A X) /\
    (HilbertRayMeetsSegment Geo C A B K \/
     HilbertRayMeetsSegment Geo C B A K) := by

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X
      hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hEq]
    exact hCline

  have hOrderK :
      HilbertRayMeetsSegment Geo K A B X \/
      HilbertRayMeetsSegment Geo K B A X :=
    hilbert_sameSide_rays_order
      Geo
      K A X B
      axis
      hKX
      hKaxis
      hXaxis
      hAoff
      hBoff
      hSameAB
      hAKB

  have hOrderC :
      HilbertRayMeetsSegment Geo C A B K \/
      HilbertRayMeetsSegment Geo C B A K :=
    hilbert_sameSide_rays_order
      Geo
      C A K B
      axis
      hCK
      hCaxis
      hKaxis
      hAoff
      hBoff
      hSameAB
      hACB

  exact
    ⟨hOrderK,
      hOrderC⟩

private theorem hilbert_forder_IV12_sameSide_orders_synchronized
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (axis : Geo.Line)
    (hCKX : Geo.Between C K X)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameAB : HilbertSameSide Geo A B axis)
    (hAKB : Not (PrimCollinear Geo A K B))
    (hACB : Not (PrimCollinear Geo A C B)) :
    (HilbertRayMeetsSegment Geo K A B X /\
     HilbertRayMeetsSegment Geo C A B K) \/
    (HilbertRayMeetsSegment Geo K B A X /\
     HilbertRayMeetsSegment Geo C B A K) := by

  have hAoff :
      Not (H.OnLine A axis) :=
    hSameAB.1

  have hBoff :
      Not (H.OnLine B axis) :=
    hSameAB.2.1

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hLineEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hLineEq]
    exact hCline

  --------------------------------------------------------------------
  -- Proper local radius angles.
  --------------------------------------------------------------------

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    rintro ⟨lineAKC,
      hAline,
      hKline',
      hCline'⟩

    have hEq :
        lineAKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineAKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hBKC :
      Not (PrimCollinear Geo B K C) := by
    rintro ⟨lineBKC,
      hBline,
      hKline',
      hCline'⟩

    have hEq :
        lineBKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineBKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hXKA :
      Not (PrimCollinear Geo X K A) := by
    rintro ⟨lineXKA,
      hXline',
      hKline',
      hAline⟩

    have hEq :
        lineXKA = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineXKA axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hXKB :
      Not (PrimCollinear Geo X K B) := by
    rintro ⟨lineXKB,
      hXline',
      hKline',
      hBline⟩

    have hEq :
        lineXKB = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineXKB axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hACK :
      Not (PrimCollinear Geo A C K) := by
    rintro ⟨lineACK,
      hAline,
      hCline',
      hKline'⟩
    exact
      hAKC
        ⟨lineACK,
          hAline,
          hKline',
          hCline'⟩

  have hBCK :
      Not (PrimCollinear Geo B C K) := by
    rintro ⟨lineBCK,
      hBline,
      hCline',
      hKline'⟩
    exact
      hBKC
        ⟨lineBCK,
          hBline,
          hKline',
          hCline'⟩

  have hKCA :
      Not (PrimCollinear Geo K C A) := by
    rintro ⟨lineKCA,
      hKline',
      hCline',
      hAline⟩
    exact
      hACK
        ⟨lineKCA,
          hAline,
          hCline',
          hKline'⟩

  have hKCB :
      Not (PrimCollinear Geo K C B) := by
    rintro ⟨lineKCB,
      hKline',
      hCline',
      hBline⟩
    exact
      hBCK
        ⟨lineKCB,
          hBline,
          hCline',
          hKline'⟩

  --------------------------------------------------------------------
  -- Stage 19: the two local half-angle identifications.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_exterior_central_half
        Geo
        K R A C X
        hAcircle
        hCcircle
        hAKC
        hCKX
    with
    ⟨T,
      hInsideT_AX,
      hAKT_XKT,
      hACK_AKT⟩

  rcases
      hilbert_circle_exterior_central_half
        Geo
        K R B C X
        hBcircle
        hCcircle
        hBKC
        hCKX
    with
    ⟨U,
      hInsideU_BX,
      hBKU_XKU,
      hBCK_BKU⟩

  have hInsideT_XA :
      HilbertRayMeetsSegment Geo K T X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K T A X
      hInsideT_AX

  have hInsideU_XB :
      HilbertRayMeetsSegment Geo K U X B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K U B X
      hInsideU_BX

  have hXKT_AKT :
      Geo.AngleCongruent
        X K T
        A K T :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K T
      X K T
      hAKT_XKT

  have hXKU_BKU :
      Geo.AngleCongruent
        X K U
        B K U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K U
      X K U
      hBKU_XKU

  have hACK_XKT :
      Geo.AngleCongruent
        A C K
        X K T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C K
      A K T
      X K T
      hACK_AKT
      hAKT_XKT

  have hBCK_XKU :
      Geo.AngleCongruent
        B C K
        X K U :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B C K
      B K U
      X K U
      hBCK_BKU
      hBKU_XKU

  have hXKT_ACK :
      Geo.AngleCongruent
        X K T
        A C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A C K
      X K T
      hACK_XKT

  have hXKU_BCK :
      Geo.AngleCongruent
        X K U
        B C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B C K
      X K U
      hBCK_XKU

  --------------------------------------------------------------------
  -- Stage 28: independent order classifications.
  --------------------------------------------------------------------

  rcases
      hilbert_forder_IV12_sameSide_ray_orders
        Geo
        K A B C X
        axis
        hCKX
        hKaxis
        hXaxis
        hAoff
        hBoff
        hSameAB
        hAKB
        hACB
    with
    ⟨hOrderK,
      hOrderC⟩

  --------------------------------------------------------------------
  -- Helper: CA inside BCK gives ACK < BCK.
  --------------------------------------------------------------------

  have hLessC_left :
      HilbertRayMeetsSegment Geo C A B K ->
      HilbertAngleLess Geo A C K B C K := by
    intro hInsideA_BK

    have hInsideA_KB :
        HilbertRayMeetsSegment Geo C A K B :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        C A B K
        hInsideA_BK

    have hRaw :
        HilbertAngleLess Geo
          K C A
          K C B :=
      hilbert_interior_angle_less
        Geo
        C A K B
        hKCB
        hInsideA_KB

    have hKCArefl :
        Geo.AngleCongruent
          K C A
          K C A :=
      Geometry.Geo.angle_congruent_reflexive
        Geo K C A

    have hACK_KCA :
        Geo.AngleCongruent
          A C K
          K C A :=
      (Geo.angle_congruent_reverse_first
        K C A
        K C A).mp
        hKCArefl

    have hStep :
        HilbertAngleLess Geo
          A C K
          K C B :=
      hilbert_angleLess_transport_left
        Geo
        K C A
        A C K
        K C B
        hRaw
        hACK
        hACK_KCA

    have hBCKrefl :
        Geo.AngleCongruent
          B C K
          B C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B C K

    have hKCB_BCK :
        Geo.AngleCongruent
          K C B
          B C K :=
      (Geo.angle_congruent_reverse_first
        B C K
        B C K).mp
        hBCKrefl

    exact
      hilbert_angleLess_transport_right
        Geo
        A C K
        K C B
        B C K
        hStep
        hBCK
        hKCB_BCK

  --------------------------------------------------------------------
  -- Helper: CB inside ACK gives BCK < ACK.
  --------------------------------------------------------------------

  have hLessC_right :
      HilbertRayMeetsSegment Geo C B A K ->
      HilbertAngleLess Geo B C K A C K := by
    intro hInsideB_AK

    have hInsideB_KA :
        HilbertRayMeetsSegment Geo C B K A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        C B A K
        hInsideB_AK

    have hRaw :
        HilbertAngleLess Geo
          K C B
          K C A :=
      hilbert_interior_angle_less
        Geo
        C B K A
        hKCA
        hInsideB_KA

    have hKCBrefl :
        Geo.AngleCongruent
          K C B
          K C B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo K C B

    have hBCK_KCB :
        Geo.AngleCongruent
          B C K
          K C B :=
      (Geo.angle_congruent_reverse_first
        K C B
        K C B).mp
        hKCBrefl

    have hStep :
        HilbertAngleLess Geo
          B C K
          K C A :=
      hilbert_angleLess_transport_left
        Geo
        K C B
        B C K
        K C A
        hRaw
        hBCK
        hBCK_KCB

    have hACKrefl :
        Geo.AngleCongruent
          A C K
          A C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A C K

    have hKCA_ACK :
        Geo.AngleCongruent
          K C A
          A C K :=
      (Geo.angle_congruent_reverse_first
        A C K
        A C K).mp
        hACKrefl

    exact
      hilbert_angleLess_transport_right
        Geo
        B C K
        K C A
        A C K
        hStep
        hACK
        hKCA_ACK

  --------------------------------------------------------------------
  -- Synchronize.
  --------------------------------------------------------------------

  rcases hOrderK with hKA | hKB

  --------------------------------------------------------------------
  -- KA is inside BKX.
  --------------------------------------------------------------------

  · have hInsideA_XB :
        HilbertRayMeetsSegment Geo K A X B :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        K A B X
        hKA

    have hWholeLess :
        HilbertAngleLess Geo
          X K A
          X K B :=
      hilbert_interior_angle_less
        Geo
        K A X B
        hXKB
        hInsideA_XB

    have hHalfLess :
        HilbertAngleLess Geo
          X K T
          X K U :=
      hilbert_angleDecomposition_half_less_of_whole_less
        Geo
        K X A T
        K X B U
        hXKA
        hXKB
        hInsideT_XA
        hInsideU_XB
        hXKT_AKT
        hXKU_BKU
        hWholeLess

    have hACK_XKU :
        HilbertAngleLess Geo
          A C K
          X K U :=
      hilbert_angleLess_transport_left
        Geo
        X K T
        A C K
        X K U
        hHalfLess
        hACK
        hACK_XKT

    have hACK_BCK :
        HilbertAngleLess Geo
          A C K
          B C K :=
      hilbert_angleLess_transport_right
        Geo
        A C K
        X K U
        B C K
        hACK_XKU
        hBCK
        hXKU_BCK

    rcases hOrderC with hCA | hCB

    · exact
        Or.inl
          ⟨hKA,
            hCA⟩

    · have hBCK_ACK :
          HilbertAngleLess Geo
            B C K
            A C K :=
        hLessC_right hCB

      have hCycle :
          HilbertAngleLess Geo
            A C K
            A C K :=
        hilbert_angleLess_trans
          Geo
          A C K
          B C K
          A C K
          hACK_BCK
          hBCK_ACK

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo A C K)
            hCycle)

  --------------------------------------------------------------------
  -- KB is inside AKX.
  --------------------------------------------------------------------

  · have hInsideB_XA :
        HilbertRayMeetsSegment Geo K B X A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        K B A X
        hKB

    have hWholeLess :
        HilbertAngleLess Geo
          X K B
          X K A :=
      hilbert_interior_angle_less
        Geo
        K B X A
        hXKA
        hInsideB_XA

    have hHalfLess :
        HilbertAngleLess Geo
          X K U
          X K T :=
      hilbert_angleDecomposition_half_less_of_whole_less
        Geo
        K X B U
        K X A T
        hXKB
        hXKA
        hInsideU_XB
        hInsideT_XA
        hXKU_BKU
        hXKT_AKT
        hWholeLess

    have hBCK_XKT :
        HilbertAngleLess Geo
          B C K
          X K T :=
      hilbert_angleLess_transport_left
        Geo
        X K U
        B C K
        X K T
        hHalfLess
        hBCK
        hBCK_XKU

    have hBCK_ACK :
        HilbertAngleLess Geo
          B C K
          A C K :=
      hilbert_angleLess_transport_right
        Geo
        B C K
        X K T
        A C K
        hBCK_XKT
        hACK
        hXKT_ACK

    rcases hOrderC with hCA | hCB

    · have hACK_BCK :
          HilbertAngleLess Geo
            A C K
            B C K :=
        hLessC_left hCA

      have hCycle :
          HilbertAngleLess Geo
            B C K
            B C K :=
        hilbert_angleLess_trans
          Geo
          B C K
          A C K
          B C K
          hBCK_ACK
          hACK_BCK

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo B C K)
            hCycle)

    · exact
        Or.inr
          ⟨hKB,
            hCB⟩

private theorem hilbert_forder_IV12_subtraction_case
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C X : Geo.Point)
    (chord axis : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKaxis : H.OnLine K axis)
    (hXaxis : H.OnLine X axis)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKX : Geo.Between C K X)
    (hSameAB : HilbertSameSide Geo A B axis) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  --------------------------------------------------------------------
  -- Axis data.
  --------------------------------------------------------------------

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hCK :
      Ne C K :=
    hCKXdata.1

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  rcases hCKXcol with
    ⟨lineCKX,
      hCline,
      hKline,
      hXline⟩

  have hLineEq :
      lineCKX = axis :=
    HilbertPlaneIncidence.line_unique
      K X hKX
      lineCKX axis
      hKline
      hXline
      hKaxis
      hXaxis

  have hCaxis :
      H.OnLine C axis := by
    rw [← hLineEq]
    exact hCline

  have hAoff :
      Not (H.OnLine A axis) :=
    hSameAB.1

  have hBoff :
      Not (H.OnLine B axis) :=
    hSameAB.2.1

  --------------------------------------------------------------------
  -- Proper radius/axis angles.
  --------------------------------------------------------------------

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    rintro ⟨lineAKC,
      hAline,
      hKline',
      hCline'⟩

    have hEq :
        lineAKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineAKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hBKC :
      Not (PrimCollinear Geo B K C) := by
    rintro ⟨lineBKC,
      hBline,
      hKline',
      hCline'⟩

    have hEq :
        lineBKC = axis :=
      HilbertPlaneIncidence.line_unique
        K C hCK.symm
        lineBKC axis
        hKline'
        hCline'
        hKaxis
        hCaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hAKX :
      Not (PrimCollinear Geo A K X) := by
    rintro ⟨lineAKX,
      hAline,
      hKline',
      hXline'⟩

    have hEq :
        lineAKX = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineAKX axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hAoff
    rw [← hEq]
    exact hAline

  have hBKX :
      Not (PrimCollinear Geo B K X) := by
    rintro ⟨lineBKX,
      hBline,
      hKline',
      hXline'⟩

    have hEq :
        lineBKX = axis :=
      HilbertPlaneIncidence.line_unique
        K X hKX
        lineBKX axis
        hKline'
        hXline'
        hKaxis
        hXaxis

    apply hBoff
    rw [← hEq]
    exact hBline

  have hACK :
      Not (PrimCollinear Geo A C K) := by
    rintro ⟨lineACK,
      hAline,
      hCline',
      hKline'⟩
    exact
      hAKC
        ⟨lineACK,
          hAline,
          hKline',
          hCline'⟩

  have hBCK :
      Not (PrimCollinear Geo B C K) := by
    rintro ⟨lineBCK,
      hBline,
      hCline',
      hKline'⟩
    exact
      hBKC
        ⟨lineBCK,
          hBline,
          hKline',
          hCline'⟩

  --------------------------------------------------------------------
  -- Proper central and inscribed target angles from the chord.
  --------------------------------------------------------------------

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hAKB :
      Not (PrimCollinear Geo A K B) := by
    intro h

    have hABK :
        PrimCollinear Geo A B K :=
      PrimCollinearRotate
        Geo A K B h

    have hKchord :
        H.OnLine K chord :=
      hilbert_collinear_on_line
        Geo
        A B K
        chord
        hAB
        hAchord
        hBchord
        hABK

    exact hKoff hKchord

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  --------------------------------------------------------------------
  -- Synchronize the two possible subtraction orientations.
  --------------------------------------------------------------------

  have hSync :=
    hilbert_forder_IV12_sameSide_orders_synchronized
      Geo
      K R A B C X
      axis
      hCKX
      hKaxis
      hXaxis
      hAcircle
      hBcircle
      hCcircle
      hSameAB
      hAKB
      hACB

  --------------------------------------------------------------------
  -- Stage 19: the two exterior-central half constructions.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_exterior_central_half
        Geo
        K R A C X
        hAcircle
        hCcircle
        hAKC
        hCKX
    with
    ⟨T,
      hInsideT_AX,
      hAKT_XKT,
      hACK_AKT⟩

  rcases
      hilbert_circle_exterior_central_half
        Geo
        K R B C X
        hBcircle
        hCcircle
        hBKC
        hCKX
    with
    ⟨U,
      hInsideU_BX,
      hBKU_XKU,
      hBCK_BKU⟩

  --------------------------------------------------------------------
  -- Choose an ordinary bisector of the target central angle AKB.
  --------------------------------------------------------------------

  rcases
      hilbert_angle_bisector_with_interior
        Geo
        K A B
        hAKB
    with
    ⟨E,
      hInsideE_AB,
      hBisectRaw⟩

  have hBisect :
      Geo.AngleCongruent
        A K E
        B K E :=
    (Geo.angle_congruent_reverse_second
      A K E
      E K B).mp
      hBisectRaw

  have hBisectSymm :
      Geo.AngleCongruent
        B K E
        A K E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K E
      B K E
      hBisect

  --------------------------------------------------------------------
  -- Split according to the synchronized ray order.
  --------------------------------------------------------------------

  rcases hSync with hCaseA | hCaseB

  --------------------------------------------------------------------
  -- Case A:
  --
  --   KA is interior to BKX,
  --   CA is interior to BCK.
  --
  -- Hence
  --
  --   BKX = BKA + AKX,
  --   BCK = BCA + ACK.
  --------------------------------------------------------------------

  · rcases hCaseA with
      ⟨hInsideA_BX,
        hInsideA_BK⟩

    have hInsideE_BA :
        HilbertRayMeetsSegment Geo K E B A :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        K E A B
        hInsideE_AB

    have hXKT_AKT :
        Geo.AngleCongruent
          X K T
          A K T :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A K T
        X K T
        hAKT_XKT

    ------------------------------------------------------------------
    -- Rebuild the bisector of the larger angle BKX from
    --
    --   half(BKA) + half(AKX).
    ------------------------------------------------------------------

    rcases
        hilbert_angleDecomposition_double_sum_bisector
          Geo
          B K X A E T
          hBKX
          hInsideA_BX
          hInsideE_BA
          hInsideT_AX
          hBisectSymm
          hXKT_AKT
      with
      ⟨W,
        hInsideW_BX,
        hInsideE_BW,
        _hInsideT_WX,
        hBisectW,
        hEKW_XKT⟩

    ------------------------------------------------------------------
    -- The rebuilt bisector W and the stage-19 bisector U bisect the
    -- same whole angle BKX.
    ------------------------------------------------------------------

    have hBKW_BKU :
        Geo.AngleCongruent
          B K W
          B K U :=
      hilbert_angleDecomposition_angle_half_unique
        Geo
        K B X W U
        hBKX
        hInsideW_BX
        hInsideU_BX
        hBisectW
        hBKU_XKU

    have hBKU_BKW :
        Geo.AngleCongruent
          B K U
          B K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        B K W
        B K U
        hBKW_BKU

    have hBCK_BKW :
        Geo.AngleCongruent
          B C K
          B K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        B C K
        B K U
        B K W
        hBCK_BKU
        hBKU_BKW

    ------------------------------------------------------------------
    -- Match the smaller right components:
    --
    --   KCA ~= WKE.
    ------------------------------------------------------------------

    have hACKrefl :
        Geo.AngleCongruent
          A C K
          A C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A C K

    have hKCA_ACK :
        Geo.AngleCongruent
          K C A
          A C K :=
      (Geo.angle_congruent_reverse_first
        A C K
        A C K).mp
        hACKrefl

    have hKCA_AKT :
        Geo.AngleCongruent
          K C A
          A K T :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        A C K
        A K T
        hKCA_ACK
        hACK_AKT

    have hKCA_XKT :
        Geo.AngleCongruent
          K C A
          X K T :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        A K T
        X K T
        hKCA_AKT
        hAKT_XKT

    have hXKT_EKW :
        Geo.AngleCongruent
          X K T
          E K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        E K W
        X K T
        hEKW_XKT

    have hKCA_EKW :
        Geo.AngleCongruent
          K C A
          E K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        X K T
        E K W
        hKCA_XKT
        hXKT_EKW

    have hEKWrefl :
        Geo.AngleCongruent
          E K W
          E K W :=
      Geometry.Geo.angle_congruent_reflexive
        Geo E K W

    have hEKW_WKE :
        Geo.AngleCongruent
          E K W
          W K E :=
      (Geo.angle_congruent_reverse_second
        E K W
        E K W).mp
        hEKWrefl

    have hKCA_WKE :
        Geo.AngleCongruent
          K C A
          W K E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C A
        E K W
        W K E
        hKCA_EKW
        hEKW_WKE

    ------------------------------------------------------------------
    -- Subtract the matched smaller components from the matched larger
    -- halves.
    ------------------------------------------------------------------

    have hBKW :
        Not (PrimCollinear Geo B K W) :=
      (hilbert_interior_angle_less
        Geo
        K W B X
        hBKX
        hInsideW_BX).1

    have hBCA_BKE :
        Geo.AngleCongruent
          B C A
          B K E :=
      hilbert_angleDecomposition_angle_subtraction
        Geo
        C B K A
        B K W E
        hBCK
        hBKW
        hInsideA_BK
        hInsideE_BW
        hBCK_BKW
        hKCA_WKE

    have hACB_BKE :
        Geo.AngleCongruent
          A C B
          B K E :=
      (Geo.angle_congruent_reverse_first
        B C A
        B K E).mp
        hBCA_BKE

    have hACB_AKE :
        Geo.AngleCongruent
          A C B
          A K E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        A C B
        B K E
        A K E
        hACB_BKE
        hBisectSymm

    exact
      ⟨E,
        hInsideE_AB,
        hBisect,
        hACB_AKE⟩

  --------------------------------------------------------------------
  -- Case B:
  --
  --   KB is interior to AKX,
  --   CB is interior to ACK.
  --
  -- Hence
  --
  --   AKX = AKB + BKX,
  --   ACK = ACB + BCK.
  --------------------------------------------------------------------

  · rcases hCaseB with
      ⟨hInsideB_AX,
        hInsideB_AK⟩

    have hXKU_BKU :
        Geo.AngleCongruent
          X K U
          B K U :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        B K U
        X K U
        hBKU_XKU

    ------------------------------------------------------------------
    -- Rebuild the bisector of the larger angle AKX from
    --
    --   half(AKB) + half(BKX).
    ------------------------------------------------------------------

    rcases
        hilbert_angleDecomposition_double_sum_bisector
          Geo
          A K X B E U
          hAKX
          hInsideB_AX
          hInsideE_AB
          hInsideU_BX
          hBisect
          hXKU_BKU
      with
      ⟨W,
        hInsideW_AX,
        hInsideE_AW,
        _hInsideU_WX,
        hBisectW,
        hEKW_XKU⟩

    ------------------------------------------------------------------
    -- The rebuilt bisector W and the stage-19 bisector T bisect the
    -- same whole angle AKX.
    ------------------------------------------------------------------

    have hAKW_AKT :
        Geo.AngleCongruent
          A K W
          A K T :=
      hilbert_angleDecomposition_angle_half_unique
        Geo
        K A X W T
        hAKX
        hInsideW_AX
        hInsideT_AX
        hBisectW
        hAKT_XKT

    have hAKT_AKW :
        Geo.AngleCongruent
          A K T
          A K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A K W
        A K T
        hAKW_AKT

    have hACK_AKW :
        Geo.AngleCongruent
          A C K
          A K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        A C K
        A K T
        A K W
        hACK_AKT
        hAKT_AKW

    ------------------------------------------------------------------
    -- Match the smaller right components:
    --
    --   KCB ~= WKE.
    ------------------------------------------------------------------

    have hBCKrefl :
        Geo.AngleCongruent
          B C K
          B C K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B C K

    have hKCB_BCK :
        Geo.AngleCongruent
          K C B
          B C K :=
      (Geo.angle_congruent_reverse_first
        B C K
        B C K).mp
        hBCKrefl

    have hKCB_BKU :
        Geo.AngleCongruent
          K C B
          B K U :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        B C K
        B K U
        hKCB_BCK
        hBCK_BKU

    have hKCB_XKU :
        Geo.AngleCongruent
          K C B
          X K U :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        B K U
        X K U
        hKCB_BKU
        hBKU_XKU

    have hXKU_EKW :
        Geo.AngleCongruent
          X K U
          E K W :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        E K W
        X K U
        hEKW_XKU

    have hKCB_EKW :
        Geo.AngleCongruent
          K C B
          E K W :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        X K U
        E K W
        hKCB_XKU
        hXKU_EKW

    have hEKWrefl :
        Geo.AngleCongruent
          E K W
          E K W :=
      Geometry.Geo.angle_congruent_reflexive
        Geo E K W

    have hEKW_WKE :
        Geo.AngleCongruent
          E K W
          W K E :=
      (Geo.angle_congruent_reverse_second
        E K W
        E K W).mp
        hEKWrefl

    have hKCB_WKE :
        Geo.AngleCongruent
          K C B
          W K E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        K C B
        E K W
        W K E
        hKCB_EKW
        hEKW_WKE

    ------------------------------------------------------------------
    -- Subtract the matched smaller components.
    ------------------------------------------------------------------

    have hAKW :
        Not (PrimCollinear Geo A K W) :=
      (hilbert_interior_angle_less
        Geo
        K W A X
        hAKX
        hInsideW_AX).1

    have hACB_AKE :
        Geo.AngleCongruent
          A C B
          A K E :=
      hilbert_angleDecomposition_angle_subtraction
        Geo
        C A K B
        A K W E
        hACK
        hAKW
        hInsideB_AK
        hInsideE_AW
        hACK_AKW
        hKCB_WKE

    exact
      ⟨E,
        hInsideE_AB,
        hBisect,
        hACB_AKE⟩

private theorem hilbert_forder_IV12_diameter_A
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hAKCcol : PrimCollinear Geo A K C) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  --------------------------------------------------------------------
  -- The inscribed angle ACB is proper.
  --------------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      A B C
      chord
      hAB
      hAchord
      hBchord
      hCoff

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC :
      Ne A C :=
    hilbert_noncollinear_ne_first
      Geo
      A C B
      hACB

  --------------------------------------------------------------------
  -- Put A,C,K on their carrier and use stage 16:
  -- K is the midpoint of the diameter AC.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC
    with
    ⟨lineAC,
      hAlineAC,
      hClineAC⟩

  have hACKcol :
      PrimCollinear Geo A C K :=
    PrimCollinearRotate
      Geo A K C hAKCcol

  have hKlineAC :
      H.OnLine K lineAC :=
    hilbert_collinear_on_line
      Geo
      A C K
      lineAC
      hAC
      hAlineAC
      hClineAC
      hACKcol

  have hMidK :
      HilbertIsMidpoint Geo K A C :=
    hilbert_circle_center_midpoint_of_chord
      Geo
      K R A C
      lineAC
      hAC
      hAlineAC
      hClineAC
      hKlineAC
      hAcircle
      hCcircle

  have hAKC :
      Geo.Between A K C :=
    hMidK.1

  have hAKCdata :=
    HilbertOrder.between_incidence
      A K C hAKC

  have hAK :
      Ne A K :=
    hAKCdata.1

  have hKC :
      Ne K C :=
    hAKCdata.2.1

  have hCK :
      Ne C K :=
    hKC.symm

  have hCKA :
      Geo.Between C K A :=
    hAKCdata.2.2.2.2

  --------------------------------------------------------------------
  -- Triangle BCK is proper.
  --------------------------------------------------------------------

  have hBCK :
      Not (PrimCollinear Geo B C K) := by
    intro h

    have hCKB :
        PrimCollinear Geo C K B :=
      PrimCollinearCycle
        Geo B C K h

    have hACBcol :
        PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo
        A C K B
        hCK
        hACKcol
        hCKB

    exact hACB hACBcol

  --------------------------------------------------------------------
  -- KB ~= KC, so triangle KBC is isosceles.
  --------------------------------------------------------------------

  have hKB_KC :
      Geo.Congruent K B K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      B C
      hBcircle
      hCcircle

  have hKBC :
      Not (PrimCollinear Geo K B C) := by
    intro h
    exact
      hBCK
        (PrimCollinearCycle
          Geo K B C h)

  have hIso :
      Geo.AngleCongruent
        K B C
        K C B :=
    hilbert_isosceles_base_angles
      Geo
      K B C
      hKBC
      hKB_KC

  have hCBK_BCK :
      Geo.AngleCongruent
        C B K
        B C K :=
    (Geo.angle_congruent_reverse_second
      C B K
      K C B).mp
      ((Geo.angle_congruent_reverse_first
        K B C
        K C B).mp
        hIso)

  --------------------------------------------------------------------
  -- I.32 on triangle BCK with CK produced through K to A.
  --
  -- It returns P inside the exterior angle BKA:
  --
  --   CBK ~= BKP,
  --   BCK ~= PKA.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B C K A
        hBCK
        hCKA
    with
    ⟨P,
      hBPA,
      hCBK_BKP,
      hBCK_PKA⟩

  --------------------------------------------------------------------
  -- The two I.32 components are congruent.
  --------------------------------------------------------------------

  have hBKP_CBK :
      Geo.AngleCongruent
        B K P
        C B K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C B K
      B K P
      hCBK_BKP

  have hBKP_BCK :
      Geo.AngleCongruent
        B K P
        B C K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B K P
      C B K
      B C K
      hBKP_CBK
      hCBK_BCK

  have hBKP_PKA :
      Geo.AngleCongruent
        B K P
        P K A :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B K P
      B C K
      P K A
      hBKP_BCK
      hBCK_PKA

  have hBKP_AKP :
      Geo.AngleCongruent
        B K P
        A K P :=
    (Geo.angle_congruent_reverse_second
      B K P
      P K A).mp
      hBKP_PKA

  have hBisect :
      Geo.AngleCongruent
        A K P
        B K P :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K P
      A K P
      hBKP_AKP

  --------------------------------------------------------------------
  -- P lies on chord AB, while K is off the chord.
  --------------------------------------------------------------------

  have hBPAdata :=
    HilbertOrder.between_incidence
      B P A hBPA

  have hBP :
      Ne B P :=
    hBPAdata.1

  have hBPAcol :
      PrimCollinear Geo B P A :=
    hBPAdata.2.2.2.1

  have hBAPcol :
      PrimCollinear Geo B A P :=
    PrimCollinearRotate
      Geo B P A hBPAcol

  have hPchord :
      H.OnLine P chord :=
    hilbert_collinear_on_line
      Geo
      B A P
      chord
      hAB.symm
      hBchord
      hAchord
      hBAPcol

  have hPK :
      Ne P K := by
    intro h
    subst P
    exact hKoff hPchord

  have hInsideP_BA :
      HilbertRayMeetsSegment Geo K P B A :=
    ⟨P,
      hBPA,
      hilbert_sameRay_refl
        Geo K P hPK⟩

  have hInsideP_AB :
      HilbertRayMeetsSegment Geo K P A B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K P B A
      hInsideP_BA

  --------------------------------------------------------------------
  -- From C, the points K and A are on the same ray.
  -- Hence angle ACB is the same angle as KCB.
  --------------------------------------------------------------------

  have hRayCKA :
      HilbertSameRay Geo C K A :=
    hilbert_sameRay_of_between
      Geo C K A hCKA

  have hRayCAK :
      HilbertSameRay Geo C A K :=
    hilbert_sameRay_symm
      Geo C K A hRayCKA

  have hAngleEq :
      Geo.Angle A C B =
      Geo.Angle K C B :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      C A K B
      hRayCAK

  have hKCB_PKA :
      Geo.AngleCongruent
        K C B
        P K A :=
    (Geo.angle_congruent_reverse_first
      B C K
      P K A).mp
      hBCK_PKA

  have hKCB_AKP :
      Geo.AngleCongruent
        K C B
        A K P :=
    (Geo.angle_congruent_reverse_second
      K C B
      P K A).mp
      hKCB_PKA

  have hACB_AKP :
      Geo.AngleCongruent
        A C B
        A K P := by
    unfold Geometry.Geo.AngleCongruent at hKCB_AKP
    unfold Geometry.Geo.AngleCongruent
    rw [hAngleEq]
    exact hKCB_AKP

  exact
    ⟨P,
      hInsideP_AB,
      hBisect,
      hACB_AKP⟩


------------------------------------------------------------------------
-- 2. B,K,C collinear: symmetric wrapper.
------------------------------------------------------------------------

private theorem hilbert_forder_IV12_diameter_B
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hBKCcol : PrimCollinear Geo B K C) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo K E A B /\
      Geo.AngleCongruent A K E B K E /\
      Geo.AngleCongruent A C B A K E := by

  rcases
      hilbert_forder_IV12_diameter_A
        Geo
        K R B A C
        chord
        hAB.symm
        hBchord
        hAchord
        hBcircle
        hAcircle
        hCcircle
        hSameCK
        hBKCcol
    with
    ⟨E,
      hInsideE_BA,
      hBisectBA,
      hBCA_BKE⟩

  have hInsideE_AB :
      HilbertRayMeetsSegment Geo K E A B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K E B A
      hInsideE_BA

  have hBisect :
      Geo.AngleCongruent
        A K E
        B K E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K E
      A K E
      hBisectBA

  have hACB_BKE :
      Geo.AngleCongruent
        A C B
        B K E :=
    (Geo.angle_congruent_reverse_first
      B C A
      B K E).mp
      hBCA_BKE

  have hBisectSymm :
      Geo.AngleCongruent
        B K E
        A K E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K E
      B K E
      hBisect

  have hACB_AKE :
      Geo.AngleCongruent
        A C B
        A K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C B
      B K E
      A K E
      hACB_BKE
      hBisectSymm

  exact
    ⟨E,
      hInsideE_AB,
      hBisect,
      hACB_AKE⟩

theorem hilbert_IV12_central_half
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV12CentralHalf
      (Geo := Geo) := by

  intro K R A B C chord
    hAB
    hAchord
    hBchord
    hAcircle
    hBcircle
    hCcircle
    hSameCK

  --------------------------------------------------------------------
  -- Construct the antipodal extension C-K-X.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_antipode
        Geo
        K R A B C
        hAB
        hAcircle
        hBcircle
        hCcircle
    with
    ⟨X,
      hCKX,
      _hXcircle⟩

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  --------------------------------------------------------------------
  -- Reference axis KX.  Since C,K,X are collinear, C lies on it too.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        K X hKX
    with
    ⟨axis,
      hKaxis,
      hXaxis⟩

  have hKXC :
      PrimCollinear Geo K X C :=
    PrimCollinearCycle
      Geo C K X hCKXcol

  have hCaxis :
      H.OnLine C axis :=
    hilbert_collinear_on_line
      Geo
      K X C
      axis
      hKX
      hKaxis
      hXaxis
      hKXC

  --------------------------------------------------------------------
  -- First exceptional branch: A lies on the axis.
  --------------------------------------------------------------------

  by_cases hAaxis : H.OnLine A axis

  · have hAKCcol :
        PrimCollinear Geo A K C :=
      ⟨axis,
        hAaxis,
        hKaxis,
        hCaxis⟩

    exact
      hilbert_forder_IV12_diameter_A
        Geo
        K R A B C
        chord
        hAB
        hAchord
        hBchord
        hAcircle
        hBcircle
        hCcircle
        hSameCK
        hAKCcol

  --------------------------------------------------------------------
  -- Second exceptional branch: B lies on the axis.
  --------------------------------------------------------------------

  · by_cases hBaxis : H.OnLine B axis

    · have hBKCcol :
          PrimCollinear Geo B K C :=
        ⟨axis,
          hBaxis,
          hKaxis,
          hCaxis⟩

      exact
        hilbert_forder_IV12_diameter_B
          Geo
          K R A B C
          chord
          hAB
          hAchord
          hBchord
          hAcircle
          hBcircle
          hCcircle
          hSameCK
          hBKCcol

    ------------------------------------------------------------------
    -- Generic case: A and B are both off the axis.
    ------------------------------------------------------------------

    · by_cases hSameAB :
          HilbertSameSide Geo A B axis

      ---------------------------------------------------------------
      -- Same side: Forder's subtraction branch.
      ---------------------------------------------------------------

      · exact
          hilbert_forder_IV12_subtraction_case
            Geo
            K R A B C X
            chord axis
            hAB
            hAchord
            hBchord
            hKaxis
            hXaxis
            hAcircle
            hBcircle
            hCcircle
            hSameCK
            hCKX
            hSameAB

      ---------------------------------------------------------------
      -- Not same side: since both points are off the axis, they are
      -- on opposite sides.  This is Forder's addition branch.
      ---------------------------------------------------------------

      · have hOppAB :
            HilbertOppositeSide Geo A B axis :=
          hilbert_oppositeSide_of_not_sameSide
            Geo
            A B
            axis
            hAaxis
            hBaxis
            hSameAB

        exact
          hilbert_forder_IV12_addition_case
            Geo
            K R A B C X
            chord axis
            hAB
            hAchord
            hBchord
            hKaxis
            hXaxis
            hAcircle
            hBcircle
            hCcircle
            hSameCK
            hCKX
            hOppAB

theorem hilbert_IV12_same_segment
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV12_1SameSegment
      (Geo := Geo) := by

  exact
    hilbert_forder_IV12_1_of_IV12_aux
      Geo
      (hilbert_IV12_central_half
        Geo)

end Geometry

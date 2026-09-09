import CGJteamLab.Hilbert3DRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Raw synthetic segment proportion in Hilbert 2D and 3D

This module contains the proposition-independent ratio/proportion layer
used by Euclid XI.17.

The representation is purely synthetic.  A ratio of two concrete
segments is represented by a right triangle whose two legs are
congruent to those segments; equality of ratios is equality, up to
angle congruence, of the corresponding defining acute angles.

The module deliberately does not import `HilbertSegmentArithmetic` and
does not use quotient segment classes, numerical lengths, division,
addition, multiplication, coordinates, or real numbers.

It also provides:

* the raw VI.2 interface in any planar Hilbert geometry;
* transport of a plane-slice proportion from `PlaneGeo` to ambient 3D;
* spatial well-definedness of the ratio angle;
* spatial V.11 (transitivity of raw proportion).

No Euclid XI.17 configuration is mentioned here.
-/

structure HilbertSegmentRatioWitnessRaw
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P Q R S : Geo.Point) where

  O : Geo.Point
  A : Geo.Point
  B : Geo.Point

  hOA : Ne O A
  hOB : Ne O B

  hNoncol :
    Not (PrimCollinear Geo O A B)

  hRight :
    HilbertRightAngle Geo A O B

  hNumerator :
    Geo.Congruent O B P Q

  hDenominator :
    Geo.Congruent O A R S


/--
Purely synthetic equality of two concrete segment ratios:

    PQ : RS = UV : WX.

The relation is expressed only by congruence of the defining acute angles
of two right-triangle witnesses.
-/
def HilbertSegmentProportionRaw
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P Q R S U V W X : Geo.Point) : Prop :=
  exists w1 : HilbertSegmentRatioWitnessRaw Geo P Q R S,
    exists w2 : HilbertSegmentRatioWitnessRaw Geo U V W X,
      Geo.AngleCongruent
        w1.O w1.A w1.B
        w2.O w2.A w2.B


/--
Two witnesses of the same concrete ratio PQ : RS determine congruent
defining acute angles.
-/
theorem hilbertSegmentRatioWitnessRaw_angle_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P Q R S : Geo.Point)
    (w1 w2 : HilbertSegmentRatioWitnessRaw Geo P Q R S) :
    Geo.AngleCongruent
      w1.O w1.A w1.B
      w2.O w2.A w2.B := by

  ----------------------------------------------------------------------
  -- Denominator legs OA are both congruent to RS.
  ----------------------------------------------------------------------

  have hOA :
      Geo.Congruent
        w1.O w1.A
        w2.O w2.A := by
    exact
      hilbert_congruent_transitivity
        Geo
        w1.O w1.A
        R S
        w2.O w2.A
        w1.hDenominator
        (hilbert_congruent_symmetry
          Geo
          w2.O w2.A
          R S
          w2.hDenominator)

  ----------------------------------------------------------------------
  -- Numerator legs OB are both congruent to PQ.
  ----------------------------------------------------------------------

  have hOB :
      Geo.Congruent
        w1.O w1.B
        w2.O w2.B := by
    exact
      hilbert_congruent_transitivity
        Geo
        w1.O w1.B
        P Q
        w2.O w2.B
        w1.hNumerator
        (hilbert_congruent_symmetry
          Geo
          w2.O w2.B
          P Q
          w2.hNumerator)

  ----------------------------------------------------------------------
  -- The included angles at O are right angles.
  ----------------------------------------------------------------------

  have hNonAOB1 :
      Not (PrimCollinear Geo w1.A w1.O w1.B) := by
    intro hCol
    exact
      w1.hNoncol
        (PrimCollinearSwap
          Geo w1.A w1.O w1.B hCol)

  have hNonAOB2 :
      Not (PrimCollinear Geo w2.A w2.O w2.B) := by
    intro hCol
    exact
      w2.hNoncol
        (PrimCollinearSwap
          Geo w2.A w2.O w2.B hCol)

  have hRight :
      Geo.AngleCongruent
        w1.A w1.O w1.B
        w2.A w2.O w2.B :=
    hilbert_all_right_angles_congruent
      Geo
      w1.A w1.O w1.B
      w2.A w2.O w2.B
      hNonAOB1 hNonAOB2
      w1.hRight w2.hRight

  ----------------------------------------------------------------------
  -- SAS identifies the right triangles.  The angle at A is the
  -- defining angle of the ratio.
  ----------------------------------------------------------------------

  have hTriangles :
      TriangleCongruenceResult
        Geo
        w1.O w1.A w1.B
        w2.O w2.A w2.B :=
    SAS
      Geo
      w1.O w1.A w1.B
      w2.O w2.A w2.B
      w1.hNoncol
      w2.hNoncol
      hOA
      hRight
      hOB

  exact hTriangles.angleB


/--
Transitivity of the purely geometric segment-proportion relation.

This is the V.11-type composition needed at the end of Euclid XI.17.
-/
theorem hilbertSegmentProportionRaw_trans
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P Q R S U V W X Y Z T K : Geo.Point)
    (h1 :
      HilbertSegmentProportionRaw
        Geo P Q R S U V W X)
    (h2 :
      HilbertSegmentProportionRaw
        Geo U V W X Y Z T K) :
    HilbertSegmentProportionRaw
      Geo P Q R S Y Z T K := by

  cases h1 with
  | intro wPQRS hRest1 =>
      cases hRest1 with
      | intro wUVWX1 hAngle1 =>

          cases h2 with
          | intro wUVWX2 hRest2 =>
              cases hRest2 with
              | intro wYZTK hAngle2 =>

                  have hMiddle :
                      Geo.AngleCongruent
                        wUVWX1.O wUVWX1.A wUVWX1.B
                        wUVWX2.O wUVWX2.A wUVWX2.B :=
                    hilbertSegmentRatioWitnessRaw_angle_congruent
                      (Geo := Geo)
                      U V W X
                      wUVWX1 wUVWX2

                  have hAngle12 :
                      Geo.AngleCongruent
                        wPQRS.O wPQRS.A wPQRS.B
                        wUVWX2.O wUVWX2.A wUVWX2.B :=
                    Geometry.Geo.angle_congruent_transitivity
                      Geo
                      wPQRS.O wPQRS.A wPQRS.B
                      wUVWX1.O wUVWX1.A wUVWX1.B
                      wUVWX2.O wUVWX2.A wUVWX2.B
                      hAngle1 hMiddle

                  have hFinal :
                      Geo.AngleCongruent
                        wPQRS.O wPQRS.A wPQRS.B
                        wYZTK.O wYZTK.A wYZTK.B :=
                    Geometry.Geo.angle_congruent_transitivity
                      Geo
                      wPQRS.O wPQRS.A wPQRS.B
                      wUVWX2.O wUVWX2.A wUVWX2.B
                      wYZTK.O wYZTK.A wYZTK.B
                      hAngle12 hAngle2

                  exact
                    Exists.intro wPQRS
                      (Exists.intro wYZTK hFinal)



def HilbertVI2Raw
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop :=
  forall X E Y F Z : Geo.Point,
    Geo.Between X E Y ->
    Geo.Between X F Z ->
    Geo.Parallel E F Y Z ->
    HilbertSegmentProportionRaw
        Geo
        X E
        E Y
        X F
        F Z /\
      HilbertSegmentProportionRaw
        Geo
        E Y
        X E
        F Z
        X F


/--
Reversing both endpoints of every concrete segment does not change a
raw synthetic proportion.
-/
theorem hilbertSegmentProportionRaw_reverse_all
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P Q R S U V W X : Geo.Point)
    (h :
      HilbertSegmentProportionRaw
        Geo P Q R S U V W X) :
    HilbertSegmentProportionRaw
      Geo Q P S R V U X W := by

  cases h with
  | intro w1 hRest =>
      cases hRest with
      | intro w2 hAngle =>

          let w1' :
              HilbertSegmentRatioWitnessRaw
                Geo Q P S R :=
            {
              O := w1.O
              A := w1.A
              B := w1.B
              hOA := w1.hOA
              hOB := w1.hOB
              hNoncol := w1.hNoncol
              hRight := w1.hRight
              hNumerator :=
                (Geo.congruent_reverse_second
                  w1.O w1.B P Q).mp
                  w1.hNumerator
              hDenominator :=
                (Geo.congruent_reverse_second
                  w1.O w1.A R S).mp
                  w1.hDenominator
            }

          let w2' :
              HilbertSegmentRatioWitnessRaw
                Geo V U X W :=
            {
              O := w2.O
              A := w2.A
              B := w2.B
              hOA := w2.hOA
              hOB := w2.hOB
              hNoncol := w2.hNoncol
              hRight := w2.hRight
              hNumerator :=
                (Geo.congruent_reverse_second
                  w2.O w2.B U V).mp
                  w2.hNumerator
              hDenominator :=
                (Geo.congruent_reverse_second
                  w2.O w2.A W X).mp
                  w2.hDenominator
            }

          exact
            Exists.intro w1'
              (Exists.intro w2' hAngle)


theorem planeGeo_parallel_of_ambient_disjoint_carriers
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (tau : S.Plane)
    (l m : Geo.Line)
    (A B C D : PlanePoint Geo tau)
    (hAB : Ne A B)
    (hCD : Ne C D)
    (hlTau : HilbertLineInPlane Geo l tau)
    (hmTau : HilbertLineInPlane Geo m tau)
    (hAl : H.OnLine A.1 l)
    (hBl : H.OnLine B.1 l)
    (hCm : H.OnLine C.1 m)
    (hDm : H.OnLine D.1 m)
    (hDisjoint : HilbertLinesDisjoint Geo l m) :
    (PlaneGeo Geo tau).Parallel A B C D := by

  let lp : PlaneLine Geo tau :=
    Subtype.mk l hlTau

  let mp : PlaneLine Geo tau :=
    Subtype.mk m hmTau

  refine And.intro hAB ?_
  refine And.intro hCD ?_

  apply Set.disjoint_left.mpr
  intro X hXAB hXCD

  have hXl :
      (PlaneGeo Geo tau).OnLine X lp :=
    (hilbert_mem_pointLine_iff_onLine
      (PlaneGeo Geo tau)
      A B X
      lp
      hAB
      hAl hBl).mp
      hXAB

  have hXm :
      (PlaneGeo Geo tau).OnLine X mp :=
    (hilbert_mem_pointLine_iff_onLine
      (PlaneGeo Geo tau)
      C D X
      mp
      hCD
      hCm hDm).mp
      hXCD

  exact
    hDisjoint
      (Exists.intro X.1
        (And.intro hXl hXm))


/--
Plane-local VI.2 fed by ambient carrier data.

The ambient points X,E,Y,F,Z lie in tau and satisfy

    X-E-Y,
    X-F-Z,

while EF and YZ are carried by ambiently disjoint lines.

The conclusion is the raw synthetic proportion in PlaneGeo(tau):

    XE : EY = XF : FZ.

No segment arithmetic is used.
-/
theorem hilbertVI2Raw_of_ambient_disjoint_carriers
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (tau : S.Plane)
    (X E Y F Z : Geo.Point)
    (hXtau : S.OnPlane X tau)
    (hEtau : S.OnPlane E tau)
    (hYtau : S.OnPlane Y tau)
    (hFtau : S.OnPlane F tau)
    (hZtau : S.OnPlane Z tau)
    (hXEY : Geo.Between X E Y)
    (hXFZ : Geo.Between X F Z)
    (lEF lYZ : Geo.Line)
    (hlEFTau : HilbertLineInPlane Geo lEF tau)
    (hlYZTau : HilbertLineInPlane Geo lYZ tau)
    (hElEF : H.OnLine E lEF)
    (hFlEF : H.OnLine F lEF)
    (hYlYZ : H.OnLine Y lYZ)
    (hZlYZ : H.OnLine Z lYZ)
    (hEF : Ne E F)
    (hYZ : Ne Y Z)
    (hDisjoint : HilbertLinesDisjoint Geo lEF lYZ)
    (hVI2 : HilbertVI2Raw (PlaneGeo Geo tau)) :
    HilbertSegmentProportionRaw
      (PlaneGeo Geo tau)
      (Subtype.mk X hXtau)
      (Subtype.mk E hEtau)
      (Subtype.mk E hEtau)
      (Subtype.mk Y hYtau)
      (Subtype.mk X hXtau)
      (Subtype.mk F hFtau)
      (Subtype.mk F hFtau)
      (Subtype.mk Z hZtau) := by

  let Xp : PlanePoint Geo tau :=
    Subtype.mk X hXtau

  let Ep : PlanePoint Geo tau :=
    Subtype.mk E hEtau

  let Yp : PlanePoint Geo tau :=
    Subtype.mk Y hYtau

  let Fp : PlanePoint Geo tau :=
    Subtype.mk F hFtau

  let Zp : PlanePoint Geo tau :=
    Subtype.mk Z hZtau

  have hXEYp :
      (PlaneGeo Geo tau).Between Xp Ep Yp := by
    exact hXEY

  have hXFZp :
      (PlaneGeo Geo tau).Between Xp Fp Zp := by
    exact hXFZ

  have hEFp :
      Ne Ep Fp := by
    intro h
    apply hEF
    exact congrArg Subtype.val h

  have hYZp :
      Ne Yp Zp := by
    intro h
    apply hYZ
    exact congrArg Subtype.val h

  have hParallelPlane :
      (PlaneGeo Geo tau).Parallel Ep Fp Yp Zp :=
    planeGeo_parallel_of_ambient_disjoint_carriers
      (Geo := Geo)
      tau
      lEF lYZ
      Ep Fp Yp Zp
      hEFp hYZp
      hlEFTau hlYZTau
      hElEF hFlEF
      hYlYZ hZlYZ
      hDisjoint

  have hProp :=
    (hVI2 Xp Ep Yp Fp Zp
      hXEYp hXFZp hParallelPlane).1

  simpa [Xp, Ep, Yp, Fp, Zp] using hProp



structure HilbertSpaceSegmentRatioWitnessRaw
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P Q R T : Geo.Point) where

  O : Geo.Point
  A : Geo.Point
  B : Geo.Point

  hOA : Ne O A
  hOB : Ne O B

  hNoncol :
    Not (PrimCollinear Geo O A B)

  hRight :
    HilbertRightAngle Geo A O B

  hNumerator :
    Geo.Congruent O B P Q

  hDenominator :
    Geo.Congruent O A R T


/--
Purely synthetic equality of two concrete segment ratios in ambient
three-space.

No global planar `HilbertCongruence Geo`, quotient of segments, numeric
length, division, addition, or multiplication is used.
-/
def HilbertSpaceSegmentProportionRaw
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P Q R T U V W X : Geo.Point) : Prop :=
  exists w1 :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo P Q R T,
    exists w2 :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo U V W X,
      Geo.AngleCongruent
        w1.O w1.A w1.B
        w2.O w2.A w2.B


/--
Forget the PlaneGeo subtype in one raw ratio witness.

All geometric fields are transported through the established
PlaneGeo/ambient bridges.
-/
def hilbertSegmentRatioWitnessRaw_to_space
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (tau : S.Plane)
    (P Q R T : PlanePoint Geo tau)
    (w :
      HilbertSegmentRatioWitnessRaw
        (PlaneGeo Geo tau) P Q R T) :
    HilbertSpaceSegmentRatioWitnessRaw
      Geo P.1 Q.1 R.1 T.1 := by

  have hOA :
      Ne w.O.1 w.A.1 := by
    intro h
    apply w.hOA
    exact Subtype.ext h

  have hOB :
      Ne w.O.1 w.B.1 := by
    intro h
    apply w.hOB
    exact Subtype.ext h

  have hNoncol :
      Not
        (PrimCollinear
          Geo w.O.1 w.A.1 w.B.1) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      tau
      w.O w.A w.B
      w.hNoncol

  have hRight :
      HilbertRightAngle
        Geo w.A.1 w.O.1 w.B.1 :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      tau
      w.A w.O w.B).mp
      w.hRight

  have hNumerator :
      Geo.Congruent
        w.O.1 w.B.1 P.1 Q.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      tau
      w.O w.B P Q).mp
      w.hNumerator

  have hDenominator :
      Geo.Congruent
        w.O.1 w.A.1 R.1 T.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      tau
      w.O w.A R T).mp
      w.hDenominator

  exact
    {
      O := w.O.1
      A := w.A.1
      B := w.B.1
      hOA := hOA
      hOB := hOB
      hNoncol := hNoncol
      hRight := hRight
      hNumerator := hNumerator
      hDenominator := hDenominator
    }


/--
A raw proportion proved inside any fixed PlaneGeo is the same synthetic
proportion in ambient three-space.

This is the bridge needed in XI.17 after each planar VI.2 application.
-/
theorem hilbertSegmentProportionRaw_to_space
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (tau : S.Plane)
    (P Q R T U V W X : PlanePoint Geo tau)
    (h :
      HilbertSegmentProportionRaw
        (PlaneGeo Geo tau)
        P Q R T U V W X) :
    HilbertSpaceSegmentProportionRaw
      Geo
      P.1 Q.1 R.1 T.1
      U.1 V.1 W.1 X.1 := by

  cases h with
  | intro w1 hRest =>
      cases hRest with
      | intro w2 hAnglePlane =>

          have hAngleAmbient :
              Geo.AngleCongruent
                w1.O.1 w1.A.1 w1.B.1
                w2.O.1 w2.A.1 w2.B.1 :=
            (planeGeo_angleCongruent_iff_ambient
              (Geo := Geo)
              tau
              w1.O w1.A w1.B
              w2.O w2.A w2.B).mp
              hAnglePlane

          refine
            Exists.intro
              (hilbertSegmentRatioWitnessRaw_to_space
                (Geo := Geo)
                tau
                P Q R T
                w1) ?_

          refine
            Exists.intro
              (hilbertSegmentRatioWitnessRaw_to_space
                (Geo := Geo)
                tau
                U V W X
                w2) ?_

          change
            Geo.AngleCongruent
              w1.O.1 w1.A.1 w1.B.1
              w2.O.1 w2.A.1 w2.B.1

          exact hAngleAmbient



theorem hilbertSpaceSegmentRatioWitnessRaw_angle_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P Q R T : Geo.Point)
    (w1 w2 :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo P Q R T) :
    Geo.AngleCongruent
      w1.O w1.A w1.B
      w2.O w2.A w2.B := by

  ----------------------------------------------------------------------
  -- Denominator legs OA are congruent through the common segment RT.
  ----------------------------------------------------------------------

  have hRT_w1OA :
      Geo.Congruent
        R T
        w1.O w1.A :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w1.O w1.A
      R T
      w1.hOA
      w1.hDenominator

  have hRT_w2OA :
      Geo.Congruent
        R T
        w2.O w2.A :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w2.O w2.A
      R T
      w2.hOA
      w2.hDenominator

  have hOA :
      Geo.Congruent
        w1.O w1.A
        w2.O w2.A :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      R T
      w1.O w1.A
      w2.O w2.A
      hRT_w1OA
      hRT_w2OA

  ----------------------------------------------------------------------
  -- Numerator legs OB are congruent through the common segment PQ.
  ----------------------------------------------------------------------

  have hPQ_w1OB :
      Geo.Congruent
        P Q
        w1.O w1.B :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w1.O w1.B
      P Q
      w1.hOB
      w1.hNumerator

  have hPQ_w2OB :
      Geo.Congruent
        P Q
        w2.O w2.B :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w2.O w2.B
      P Q
      w2.hOB
      w2.hNumerator

  have hOB :
      Geo.Congruent
        w1.O w1.B
        w2.O w2.B :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P Q
      w1.O w1.B
      w2.O w2.B
      hPQ_w1OB
      hPQ_w2OB

  ----------------------------------------------------------------------
  -- The included angles at O are both right.
  ----------------------------------------------------------------------

  have hAOB1 :
      Not (PrimCollinear Geo w1.A w1.O w1.B) := by
    intro hCol
    exact
      w1.hNoncol
        (PrimCollinearSwap
          Geo w1.A w1.O w1.B hCol)

  have hAOB2 :
      Not (PrimCollinear Geo w2.A w2.O w2.B) := by
    intro hCol
    exact
      w2.hNoncol
        (PrimCollinearSwap
          Geo w2.A w2.O w2.B hCol)

  have hRight :
      Geo.AngleCongruent
        w1.A w1.O w1.B
        w2.A w2.O w2.B :=
    hilbert_space_all_right_angles_congruent
      (Geo := Geo)
      w1.A w1.O w1.B
      w2.A w2.O w2.B
      hAOB1 hAOB2
      w1.hRight w2.hRight

  ----------------------------------------------------------------------
  -- Spatial SAS: OA, OB and the included right angle determine the
  -- defining angle at A.
  ----------------------------------------------------------------------

  exact
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      w1.O w1.A w1.B
      w2.O w2.A w2.B
      w1.hNoncol
      w2.hNoncol
      hOA
      hOB
      hRight


/--
Spatial V.11 for the raw synthetic proportion relation.

If

    PQ : RT = UV : WX

and

    UV : WX = YZ : JK,

then

    PQ : RT = YZ : JK.
-/
theorem hilbertSpaceSegmentProportionRaw_trans
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P Q R T U V W X Y Z J K : Geo.Point)
    (h1 :
      HilbertSpaceSegmentProportionRaw
        Geo
        P Q R T
        U V W X)
    (h2 :
      HilbertSpaceSegmentProportionRaw
        Geo
        U V W X
        Y Z J K) :
    HilbertSpaceSegmentProportionRaw
      Geo
      P Q R T
      Y Z J K := by

  cases h1 with
  | intro wPQRT hRest1 =>
      cases hRest1 with
      | intro wUVWX1 hAngle1 =>

          cases h2 with
          | intro wUVWX2 hRest2 =>
              cases hRest2 with
              | intro wYZJK hAngle2 =>

                  have hMiddle :
                      Geo.AngleCongruent
                        wUVWX1.O wUVWX1.A wUVWX1.B
                        wUVWX2.O wUVWX2.A wUVWX2.B :=
                    hilbertSpaceSegmentRatioWitnessRaw_angle_congruent
                      (Geo := Geo)
                      U V W X
                      wUVWX1 wUVWX2

                  have hAngle12 :
                      Geo.AngleCongruent
                        wPQRT.O wPQRT.A wPQRT.B
                        wUVWX2.O wUVWX2.A wUVWX2.B :=
                    Geometry.Geo.angle_congruent_transitivity
                      Geo
                      wPQRT.O wPQRT.A wPQRT.B
                      wUVWX1.O wUVWX1.A wUVWX1.B
                      wUVWX2.O wUVWX2.A wUVWX2.B
                      hAngle1 hMiddle

                  have hFinal :
                      Geo.AngleCongruent
                        wPQRT.O wPQRT.A wPQRT.B
                        wYZJK.O wYZJK.A wYZJK.B :=
                    Geometry.Geo.angle_congruent_transitivity
                      Geo
                      wPQRT.O wPQRT.A wPQRT.B
                      wUVWX2.O wUVWX2.A wUVWX2.B
                      wYZJK.O wYZJK.A wYZJK.B
                      hAngle12 hAngle2

                  refine Exists.intro wPQRT ?_
                  refine Exists.intro wYZJK ?_
                  exact hFinal


end Geometry

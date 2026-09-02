import CGJteamLab.Hilbert3DInterface
import CGJteamLab.HilbertRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid Book XI, Proposition 4

All declarations in this file are specific to the construction and
proof of Euclid XI.4.  General 3D notions remain in
`Hilbert3DInterface.lean`; axioms remain in `Hilbert3DAxioms.lean`.
-/

/-!
## Euclid XI.4: balanced points on a line

The classical proof of XI.4 begins by cutting off four equal segments
from the common point of the two given lines.

The next lemma isolates the one-line construction needed for that step.
It works entirely inside `PlaneGeo pi`, where the ordinary planar
Hilbert order and congruence interfaces are already available.
-/

/--
On a plane-line through `O`, construct two points on opposite sides of
`O`, each congruent to a prescribed segment `UV`.

The result is stated ambiently so that it can be used directly in the
spatial XI.4 proof.
-/
theorem planeGeo_opposite_points_on_line_congruent_to
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l : PlaneLine Geo pi)
    (O U V : PlanePoint Geo pi)
    (hOl : H.OnLine O.1 l.1) :
    exists C D : PlanePoint Geo pi,
      H.OnLine C.1 l.1 /\
      H.OnLine D.1 l.1 /\
      Geo.Between C.1 O.1 D.1 /\
      Geo.Congruent O.1 C.1 U.1 V.1 /\
      Geo.Congruent O.1 D.1 U.1 V.1 := by

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l.1 O.1 with
    ⟨R, hRO, hRl⟩

  have hRpi :
      S.OnPlane R pi :=
    l.2 R hRl

  let Rp : PlanePoint Geo pi :=
    ⟨R, hRpi⟩

  have hORp :
      Ne O Rp := by
    intro h
    apply hRO
    exact (congrArg Subtype.val h).symm

  rcases
      HilbertCongruence.segment_construction
        (Geo := PlaneGeo Geo pi)
        U V O Rp hORp with
    ⟨C, hRayC, hCongC⟩

  have hClPlane :
      HilbertIncidence.OnLine C l := by
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := PlaneGeo Geo pi)
        hORp
        hOl
        hRl
        hRayC.2.2.1

  have hCl :
      H.OnLine C.1 l.1 :=
    hClPlane

  have hCO :
      Ne C O :=
    hRayC.2.1

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo pi)
        C O hCO with
    ⟨Ropp, hCORopp⟩

  have hCORoppData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O Ropp hCORopp

  have hORopp :
      Ne O Ropp :=
    hCORoppData.2.1

  have hRoppLine :
      HilbertIncidence.OnLine Ropp l := by
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := PlaneGeo Geo pi)
        hCO
        hCl
        hOl
        hCORoppData.2.2.2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := PlaneGeo Geo pi)
        U V O Ropp hORopp with
    ⟨D, hRayD, hCongD⟩

  have hDlPlane :
      HilbertIncidence.OnLine D l := by
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := PlaneGeo Geo pi)
        hORopp
        hOl
        hRoppLine
        hRayD.2.2.1

  have hDl :
      H.OnLine D.1 l.1 :=
    hDlPlane

  have hCOD :
      (PlaneGeo Geo pi).Between C O D := by

    rcases
        hilbert_sameRay_cases
          (PlaneGeo Geo pi)
          O Ropp D hRayD with
      hRoppD | hORoppD | hODRopp

    · subst D
      exact hCORopp

    · exact
        (hilbert_between_outer_trans
          (PlaneGeo Geo pi)
          C O Ropp D
          hCORopp
          hORoppD).2

    · have hRoppOC :
          (PlaneGeo Geo pi).Between
            Ropp O C :=
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          C O Ropp hCORopp).2.2.2.2

      have hRoppDO :
          (PlaneGeo Geo pi).Between
            Ropp D O :=
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          O D Ropp hODRopp).2.2.2.2

      have hDOC :
          (PlaneGeo Geo pi).Between
            D O C :=
        (hilbert_between_inner_trans
          (PlaneGeo Geo pi)
          Ropp D O C
          hRoppDO
          hRoppOC).1

      exact
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          D O C hDOC).2.2.2.2

  have hCongCAmbient :
      Geo.Congruent
        O.1 C.1 U.1 V.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O C U V).mp hCongC

  have hCongDAmbient :
      Geo.Congruent
        O.1 D.1 U.1 V.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O D U V).mp hCongD

  exact
    ⟨C, D,
     hCl,
     hDl,
     hCOD,
     hCongCAmbient,
     hCongDAmbient⟩


/-!
## Euclid XI.4: the balanced cross on the two given lines
-/

/--
Given two plane-lines through `O`, construct points `A,B` on the first
and `C,D` on the second such that:

* `A-O-B` and `C-O-D`;
* all four radial segments are congruent to one common reference
  segment `OR`.

This is the exact synthetic configuration used at the start of
Euclid XI.4.
-/
theorem hilbert_XI4_balanced_cross_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (O : PlanePoint Geo pi)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1) :
    exists R A B C D : PlanePoint Geo pi,
      Ne R O /\
      H.OnLine R.1 m.1 /\
      H.OnLine A.1 m.1 /\
      H.OnLine B.1 m.1 /\
      H.OnLine C.1 n.1 /\
      H.OnLine D.1 n.1 /\
      Geo.Between A.1 O.1 B.1 /\
      Geo.Between C.1 O.1 D.1 /\
      Geo.Congruent O.1 A.1 O.1 R.1 /\
      Geo.Congruent O.1 B.1 O.1 R.1 /\
      Geo.Congruent O.1 C.1 O.1 R.1 /\
      Geo.Congruent O.1 D.1 O.1 R.1 := by

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        m.1 O.1 with
    ⟨R0, hR0O, hR0m⟩

  have hR0pi :
      S.OnPlane R0 pi :=
    m.2 R0 hR0m

  let R : PlanePoint Geo pi :=
    ⟨R0, hR0pi⟩

  have hRO :
      Ne R O := by
    intro h
    exact hR0O (congrArg Subtype.val h)

  rcases
      planeGeo_opposite_points_on_line_congruent_to
        (Geo := Geo)
        pi m O O R hOm with
    ⟨A, B,
     hAm, hBm,
     hAOB,
     hOAref,
     hOBref⟩

  rcases
      planeGeo_opposite_points_on_line_congruent_to
        (Geo := Geo)
        pi n O O R hOn with
    ⟨C, D,
     hCn, hDn,
     hCOD,
     hOCref,
     hODref⟩

  exact
    ⟨R, A, B, C, D,
     hRO,
     hR0m,
     hAm,
     hBm,
     hCn,
     hDn,
     hAOB,
     hCOD,
     hOAref,
     hOBref,
     hOCref,
     hODref⟩

/-!
## Euclid XI.4: first congruent pair of triangles

Euclid now compares the triangles formed by the balanced cross:

  O-A-D   and   O-B-C

The included angles at `O` are vertical.  The two pairs of adjacent
radial sides are equal by construction.  Hilbert SAS therefore gives
the opposite sides `AD` and `BC` equal and also the corresponding
remaining angles.

This is the synthetic Hilbert version of Euclid XI.4's first use of
Book I, Proposition 4.
-/

/--
If two distinct plane-lines through `O` contain `A,B` and `C,D`
respectively, with `A-O-B`, `C-O-D`, then `O,A,D` and `O,B,C` are
noncollinear.
-/
theorem planeGeo_XI4_cross_noncollinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (O A B C D : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB : Geo.Between A.1 O.1 B.1)
    (hCOD : Geo.Between C.1 O.1 D.1) :
    Not (PrimCollinear (PlaneGeo Geo pi) O A D) /\
    Not (PrimCollinear (PlaneGeo Geo pi) O B C) := by

  have hAOBData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB

  have hCODData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O D hCOD

  have hOA : Ne O A :=
    hAOBData.1.symm

  have hOB : Ne O B :=
    hAOBData.2.1

  have hOC : Ne O C :=
    hCODData.1.symm

  have hOD : Ne O D :=
    hCODData.2.1

  have hNonOAD :
      Not (PrimCollinear (PlaneGeo Geo pi) O A D) := by

    intro hCol

    rcases hCol with
      ⟨q, hOq, hAq, hDq⟩

    have hmq :
        m = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O A hOA
        m q
        hOm hAm
        hOq hAq

    have hnq :
        n = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O D hOD
        n q
        hOn hDn
        hOq hDq

    apply hmn

    exact
      Eq.trans hmq (Eq.symm hnq)

  have hNonOBC :
      Not (PrimCollinear (PlaneGeo Geo pi) O B C) := by

    intro hCol

    rcases hCol with
      ⟨q, hOq, hBq, hCq⟩

    have hmq :
        m = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O B hOB
        m q
        hOm hBm
        hOq hBq

    have hnq :
        n = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O C hOC
        n q
        hOn hCn
        hOq hCq

    apply hmn

    exact
      Eq.trans hmq (Eq.symm hnq)

  exact
    ⟨hNonOAD, hNonOBC⟩


/--
First congruence consequence of the balanced cross in Euclid XI.4.

Under the common-radius hypotheses, the triangles `OAD` and `OBC`
have two corresponding equal sides and equal included vertical angles.
Hence:

* `AD` is congruent to `BC`;
* angle `OAD` is congruent to angle `OBC`.

The conclusions are returned in the ambient geometry.
-/
theorem hilbert_XI4_balanced_cross_first_SAS
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (O R A B C D : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB : Geo.Between A.1 O.1 B.1)
    (hCOD : Geo.Between C.1 O.1 D.1)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1) :
    Geo.Congruent A.1 D.1 B.1 C.1 /\
    Geo.AngleCongruent
      O.1 A.1 D.1
      O.1 B.1 C.1 := by

  have hNon :=
    planeGeo_XI4_cross_noncollinear
      (Geo := Geo)
      pi m n
      O A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD

  have hNonOAD :
      Not (PrimCollinear (PlaneGeo Geo pi) O A D) :=
    hNon.1

  have hNonOBC :
      Not (PrimCollinear (PlaneGeo Geo pi) O B C) :=
    hNon.2

  have hAOBData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB

  have hCODData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O D hCOD

  have hDOC :
      (PlaneGeo Geo pi).Between D O C :=
    hCODData.2.2.2.2

  have hNonAOD :
      Not (PrimCollinear (PlaneGeo Geo pi) A O D) := by
    intro h
    exact
      hNonOAD
        (PrimCollinearSwap
          (PlaneGeo Geo pi)
          A O D h)

  have hVertical :
      (PlaneGeo Geo pi).AngleCongruent
        A O D
        B O C :=
    hilbert_vertical_angles
      (PlaneGeo Geo pi)
      A O D B C
      hAOB
      hDOC
      hNonAOD

  have hOArefP :
      (PlaneGeo Geo pi).Congruent
        O A O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O A O R).mpr hOAref

  have hOBrefP :
      (PlaneGeo Geo pi).Congruent
        O B O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O B O R).mpr hOBref

  have hOCrefP :
      (PlaneGeo Geo pi).Congruent
        O C O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O C O R).mpr hOCref

  have hODrefP :
      (PlaneGeo Geo pi).Congruent
        O D O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O D O R).mpr hODref

  have hROA :
      (PlaneGeo Geo pi).Congruent
        O R O A :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O A O R
      hOArefP

  have hROB :
      (PlaneGeo Geo pi).Congruent
        O R O B :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O B O R
      hOBrefP

  have hROC :
      (PlaneGeo Geo pi).Congruent
        O R O C :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O C O R
      hOCrefP

  have hROD :
      (PlaneGeo Geo pi).Congruent
        O R O D :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O D O R
      hODrefP

  have hOAOB :
      (PlaneGeo Geo pi).Congruent
        O A O B :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O A O B
      hROA hROB

  have hODOC :
      (PlaneGeo Geo pi).Congruent
        O D O C :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O D O C
      hROD hROC

  have hThird :=
    hilbert_sas_third_side_and_angle
      (PlaneGeo Geo pi)
      O A D
      O B C
      hNonOAD
      hNonOBC
      hOAOB
      hODOC
      hVertical

  have hAngles :=
    hilbert_sas_remaining_angles
      (PlaneGeo Geo pi)
      O A D
      O B C
      hNonOAD
      hNonOBC
      hOAOB
      hODOC
      hVertical

  have hADBCPlane :
      (PlaneGeo Geo pi).Congruent
        A D B C :=
    hThird.1

  have hAnglePlane :
      (PlaneGeo Geo pi).AngleCongruent
        O A D
        O B C :=
    hAngles.1

  have hADBCAmbient :
      Geo.Congruent
        A.1 D.1 B.1 C.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi A D B C).mp
      hADBCPlane

  have hAngleAmbient :
      Geo.AngleCongruent
        O.1 A.1 D.1
        O.1 B.1 C.1 :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      pi O A D O B C).mp
      hAnglePlane

  exact
    ⟨hADBCAmbient,
     hAngleAmbient⟩

/-!
## Euclid XI.4: the I.26 / ASA step on an arbitrary transversal

Suppose a line through `O` meets the two opposite connector segments
`AD` and `BC` at `G` and `H`.

From the first SAS step we already know

  angle OAD = angle OBC.

Because `G` lies on `AD` and `H` lies on `BC`, this becomes

  angle OAG = angle OBH.

The angles `AOG` and `BOH` are vertical.  Together with `OA = OB`,
Hilbert's ASA theorem gives

  OG = OH
  AG = BH.

This is the exact counterpart of Euclid XI.4's use of I.26.
-/

/--
Noncollinearity of the two ASA triangles obtained by cutting the
connector segments `AD` and `BC`.
-/
theorem planeGeo_XI4_transversal_noncollinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A B C D G J : PlanePoint Geo pi)
    (hNonOAD :
      Not (PrimCollinear (PlaneGeo Geo pi) O A D))
    (hNonOBC :
      Not (PrimCollinear (PlaneGeo Geo pi) O B C))
    (hAGD :
      (PlaneGeo Geo pi).Between A G D)
    (hBJC :
      (PlaneGeo Geo pi).Between B J C) :
    Not (PrimCollinear (PlaneGeo Geo pi) A O G) /\
    Not (PrimCollinear (PlaneGeo Geo pi) B O J) := by

  have hAGDData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A G D hAGD

  have hBJCData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      B J C hBJC

  have hAG :
      Ne A G :=
    hAGDData.1

  have hBJ :
      Ne B J :=
    hBJCData.1

  have hAGDcol :
      PrimCollinear
        (PlaneGeo Geo pi) A G D :=
    hAGDData.2.2.2.1

  have hBJCcol :
      PrimCollinear
        (PlaneGeo Geo pi) B J C :=
    hBJCData.2.2.2.1

  have hNonAOG :
      Not (PrimCollinear
        (PlaneGeo Geo pi) A O G) := by

    intro hAOG

    have hOAG :
        PrimCollinear
          (PlaneGeo Geo pi) O A G :=
      PrimCollinearSwap
        (PlaneGeo Geo pi)
        A O G hAOG

    have hOAD :
        PrimCollinear
          (PlaneGeo Geo pi) O A D :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        O A G D
        hAG
        hOAG
        hAGDcol

    exact hNonOAD hOAD

  have hNonBOJ :
      Not (PrimCollinear
        (PlaneGeo Geo pi) B O J) := by

    intro hBOJ

    have hOBJ :
        PrimCollinear
          (PlaneGeo Geo pi) O B J :=
      PrimCollinearSwap
        (PlaneGeo Geo pi)
        B O J hBOJ

    have hOBC :
        PrimCollinear
          (PlaneGeo Geo pi) O B C :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        O B J C
        hBJ
        hOBJ
        hBJCcol

    exact hNonOBC hOBC

  exact
    ⟨hNonAOG, hNonBOJ⟩


/--
Euclid XI.4, second planar congruence step.

Assume `G` lies between `A,D`, `J` lies between `B,C`, and `G-O-J`.
From the balanced-cross data one obtains

  OG congruent OJ
  AG congruent BJ.

The proof is Hilbert ASA, corresponding to Euclid I.26.
-/
theorem hilbert_XI4_transversal_ASA
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (O R A B C D G J : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB : Geo.Between A.1 O.1 B.1)
    (hCOD : Geo.Between C.1 O.1 D.1)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1)
    (hAGD : Geo.Between A.1 G.1 D.1)
    (hBJC : Geo.Between B.1 J.1 C.1)
    (hGOJ : Geo.Between G.1 O.1 J.1) :
    Geo.Congruent O.1 G.1 O.1 J.1 /\
    Geo.Congruent A.1 G.1 B.1 J.1 := by

  have hNon :=
    planeGeo_XI4_cross_noncollinear
      (Geo := Geo)
      pi m n
      O A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD

  have hNonOAD :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O A D) :=
    hNon.1

  have hNonOBC :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O B C) :=
    hNon.2

  have hTransNon :=
    planeGeo_XI4_transversal_noncollinear
      (Geo := Geo)
      pi
      O A B C D G J
      hNonOAD
      hNonOBC
      hAGD
      hBJC

  have hNonAOG :
      Not (PrimCollinear
        (PlaneGeo Geo pi) A O G) :=
    hTransNon.1

  have hNonBOJ :
      Not (PrimCollinear
        (PlaneGeo Geo pi) B O J) :=
    hTransNon.2

  have hFirst :=
    hilbert_XI4_balanced_cross_first_SAS
      (Geo := Geo)
      pi m n
      O R A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD
      hOAref hOBref
      hOCref hODref

  have hAngleOAD_OBC :
      Geo.AngleCongruent
        O.1 A.1 D.1
        O.1 B.1 C.1 :=
    hFirst.2

  have hAngleOAD_OBC_P :
      (PlaneGeo Geo pi).AngleCongruent
        O A D
        O B C :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      pi O A D O B C).mpr
      hAngleOAD_OBC

  have hRayAGD :
      HilbertSameRay
        (PlaneGeo Geo pi) A G D :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo pi)
      A G D hAGD

  have hRayADG :
      HilbertSameRay
        (PlaneGeo Geo pi) A D G :=
    hilbert_sameRay_symm
      (PlaneGeo Geo pi)
      A G D hRayAGD

  have hRayBJC :
      HilbertSameRay
        (PlaneGeo Geo pi) B J C :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo pi)
      B J C hBJC

  have hRayBCJ :
      HilbertSameRay
        (PlaneGeo Geo pi) B C J :=
    hilbert_sameRay_symm
      (PlaneGeo Geo pi)
      B J C hRayBJC

  have hAngleAtA :
      (PlaneGeo Geo pi).AngleCongruent
        O A G
        O B J := by

    have hLeft :
        (PlaneGeo Geo pi).Angle O A D =
        (PlaneGeo Geo pi).Angle O A G :=
      hilbert_angle_eq_of_sameRay_second
        (PlaneGeo Geo pi)
        A O D G hRayADG

    have hRight :
        (PlaneGeo Geo pi).Angle O B C =
        (PlaneGeo Geo pi).Angle O B J :=
      hilbert_angle_eq_of_sameRay_second
        (PlaneGeo Geo pi)
        B O C J hRayBCJ

    simpa only [
      Geometry.Geo.AngleCongruent,
      hLeft,
      hRight
    ] using hAngleOAD_OBC_P

  have hAngleAtO :
      (PlaneGeo Geo pi).AngleCongruent
        A O G
        B O J := by
    exact
      hilbert_vertical_angles
        (PlaneGeo Geo pi)
        A O G B J
        hAOB
        hGOJ
        hNonAOG

  have hOArefP :
      (PlaneGeo Geo pi).Congruent
        O A O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O A O R).mpr hOAref

  have hOBrefP :
      (PlaneGeo Geo pi).Congruent
        O B O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O B O R).mpr hOBref

  have hROA :
      (PlaneGeo Geo pi).Congruent
        O R O A :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O A O R
      hOArefP

  have hROB :
      (PlaneGeo Geo pi).Congruent
        O R O B :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O B O R
      hOBrefP

  have hOAOB :
      (PlaneGeo Geo pi).Congruent
        O A O B :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O A O B
      hROA hROB

  have hAO_OB :
      (PlaneGeo Geo pi).Congruent
        A O O B :=
    (Geometry.Geo.congruent_reverse_first
      (PlaneGeo Geo pi)
      O A O B).mp
      hOAOB

  have hAOBO :
      (PlaneGeo Geo pi).Congruent
        A O B O :=
    (Geometry.Geo.congruent_reverse_second
      (PlaneGeo Geo pi)
      A O O B).mp
      hAO_OB

  have hASA :
      (PlaneGeo Geo pi).Congruent A G B J /\
      (PlaneGeo Geo pi).Congruent O G O J :=
    hilbert_asa_sides
      (PlaneGeo Geo pi)
      A O G
      B O J
      hNonAOG
      hNonBOJ
      hAOBO
      hAngleAtA
      hAngleAtO

  have hAGBJPlane :
      (PlaneGeo Geo pi).Congruent
        A G B J :=
    hASA.1

  have hOGOJPlane :
      (PlaneGeo Geo pi).Congruent
        O G O J :=
    hASA.2

  have hOGOJAmbient :
      Geo.Congruent
        O.1 G.1 O.1 J.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O G O J).mp
      hOGOJPlane

  have hAGBJAmbient :
      Geo.Congruent
        A.1 G.1 B.1 J.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi A G B J).mp
      hAGBJPlane

  exact
    ⟨hOGOJAmbient,
     hAGBJAmbient⟩


/-!
## Euclid XI.4: spatial perpendicular-bisector block

The next part of XI.4 uses a point F on the candidate perpendicular
through O.  The point-based definition of line-line perpendicularity
contains arbitrary witness points on the two carriers, so we first
normalize those witnesses to any prescribed nonvertex points on the
same two lines.

The carrier-normalization lemmas below are kept local to XI.4 for now.
Their content is general, but their permanent neutral-module location is
left open until the XI.4 proof is closed and the dependency boundary is
settled.
-/

/--
Swapping the two arms of a nondegenerate right angle preserves
rightness.
-/
theorem hilbert_XI4_right_angle_swap
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
      Geo.AngleCongruent A O B A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hAngle :
      Geo.AngleCongruent A O B B O A :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      A O B).mp hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      B O A
      hAOB
      hBOA
      hRight
      hAngle


/--
Moving the first arm of a right angle along the same ray preserves
rightness.
-/
theorem hilbert_XI4_right_angle_sameRay_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B)
    (hRay : HilbertSameRay Geo O A A') :
    HilbertRightAngle Geo A' O B := by

  have hOA' : Not (O = A') := by
    intro h
    apply hRay.2.1
    exact h.symm

  have hA'OB :
      Not (PrimCollinear Geo A' O B) := by
    intro hA'OBcol

    have hAOA' :
        PrimCollinear Geo A O A' :=
      PrimCollinearSwap
        Geo O A A' hRay.2.2.1

    have hOA'B :
        PrimCollinear Geo O A' B :=
      PrimCollinearSwap
        Geo A' O B hA'OBcol

    have hAOBcol :
        PrimCollinear Geo A O B :=
      hilbert_primCollinear_trans
        Geo
        A O A' B
        hOA'
        hAOA'
        hOA'B

    exact hAOB hAOBcol

  have hAngleEq :
      Geo.Angle A O B = Geo.Angle A' O B :=
    hilbert_angle_eq_of_sameRay_first
      Geo O A A' B hRay

  have hRefl :
      Geo.AngleCongruent A O B A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hAngle :
      Geo.AngleCongruent A O B A' O B := by
    unfold Geometry.Geo.AngleCongruent at hRefl
    unfold Geometry.Geo.AngleCongruent
    rw [Eq.symm hAngleEq]
    exact hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      A' O B
      hAOB
      hA'OB
      hRight
      hAngle


/--
Reversing the first arm of a right angle through the vertex preserves
rightness.
-/
theorem hilbert_XI4_right_angle_opposite_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' O B : Geo.Point)
    (hAOA' : Geo.Between A O A')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A' O B := by

  have hRightEq :
      Geo.AngleCongruent A O B B O A' :=
    hilbert_right_angle_opposite_extension
      Geo
      A O B A'
      hAOB
      hRight
      hAOA'

  have hAOB_A'OB :
      Geo.AngleCongruent A O B A' O B :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      B O A').mp hRightEq

  have hA'OB_AOB :
      Geo.AngleCongruent A' O B A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      A' O B
      hAOB_A'OB

  have hA'OB_BOA :
      Geo.AngleCongruent A' O B B O A :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A' O B
      A O B).mp hA'OB_AOB

  have hA'OA :
      Geo.Between A' O A :=
    (HilbertOrder.between_incidence
      A O A' hAOA').2.2.2.2

  exact
    Exists.intro A
      (And.intro hA'OA hA'OB_BOA)


/--
A right angle does not depend on which nonvertex point is chosen on the
carrier of its first arm.
-/
theorem hilbert_XI4_right_angle_collinear_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' O B : Geo.Point)
    (hOA : Not (O = A))
    (hOA' : Not (O = A'))
    (hCol : PrimCollinear Geo O A A')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A' O B := by

  by_cases hAA' : A = A'

  · subst A'
    exact hRight

  · rcases
      hilbert_between_trichotomy
        Geo
        O A A'
        hOA
        hAA'
        hOA'
        hCol
    with
    hOAA' | hAOA' | hOA'A

    · have hRay :
          HilbertSameRay Geo O A A' :=
        hilbert_sameRay_of_between
          Geo O A A' hOAA'

      exact
        hilbert_XI4_right_angle_sameRay_first
          Geo
          A A' O B
          hAOB
          hRight
          hRay

    · exact
        hilbert_XI4_right_angle_opposite_first
          Geo
          A A' O B
          hAOA'
          hAOB
          hRight

    · have hRayA'A :
          HilbertSameRay Geo O A' A :=
        hilbert_sameRay_of_between
          Geo O A' A hOA'A

      have hRayAA' :
          HilbertSameRay Geo O A A' :=
        hilbert_sameRay_symm
          Geo O A' A hRayA'A

      exact
        hilbert_XI4_right_angle_sameRay_first
          Geo
          A A' O B
          hAOB
          hRight
          hRayAA'


/--
A right angle does not depend on which nonvertex point is chosen on the
carrier of its second arm.
-/
theorem hilbert_XI4_right_angle_collinear_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B B' : Geo.Point)
    (hOB : Not (O = B))
    (hOB' : Not (O = B'))
    (hCol : PrimCollinear Geo O B B')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A O B' := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hRightBOA :
      HilbertRightAngle Geo B O A :=
    hilbert_XI4_right_angle_swap
      Geo
      A O B
      hAOB
      hRight

  have hRightB'OA :
      HilbertRightAngle Geo B' O A :=
    hilbert_XI4_right_angle_collinear_first
      Geo
      B B' O A
      hOB
      hOB'
      hCol
      hBOA
      hRightBOA

  have hB'OA :
      Not (PrimCollinear Geo B' O A) := by
    intro h

    have hOB'A :
        PrimCollinear Geo O B' A :=
      PrimCollinearSwap
        Geo B' O A h

    have hBOB' :
        PrimCollinear Geo B O B' :=
      PrimCollinearSwap
        Geo O B B' hCol

    have hBOAcol :
        PrimCollinear Geo B O A :=
      hilbert_primCollinear_trans
        Geo
        B O B' A
        hOB'
        hBOB'
        hOB'A

    exact hBOA hBOAcol

  exact
    hilbert_XI4_right_angle_swap
      Geo
      B' O A
      hB'OA
      hRightB'OA


/--
Normalize the witness-based line-line perpendicularity predicate to any
chosen nonvertex points on the two carriers.

This theorem is planar: it will be applied in the induced plane through
the candidate spatial line and one of the two base lines.
-/
theorem hilbert_XI4_linesPerpendicularAt_right_angle_of_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (l m : Geo.Line)
    (O A B : Geo.Point)
    (hlm : Ne l m)
    (hPerp : HilbertLinesPerpendicularAt Geo l m O)
    (hAO : Ne A O)
    (hBO : Ne B O)
    (hAl : HilbertIncidence.OnLine A l)
    (hBm : HilbertIncidence.OnLine B m) :
    Not (PrimCollinear Geo A O B) /\
    HilbertRightAngle Geo A O B := by

  rcases hPerp with
    ⟨hOl, hOm,
     X, Y,
     hXO, hYO,
     hXl, hYm,
     hNonXY,
     hRightXY⟩

  have hOXA :
      PrimCollinear Geo O X A :=
    ⟨l, hOl, hXl, hAl⟩

  have hRightAY :
      HilbertRightAngle Geo A O Y :=
    hilbert_XI4_right_angle_collinear_first
      Geo
      X A O Y
      hXO.symm
      hAO.symm
      hOXA
      hNonXY
      hRightXY

  have hNonAY :
      Not (PrimCollinear Geo A O Y) := by
    intro hAOY

    have hYOA :
        PrimCollinear Geo Y O A :=
      PrimCollinearSymm
        Geo A O Y hAOY

    have hAm :
        HilbertIncidence.OnLine A m :=
      hilbert_collinear_on_line
        Geo
        Y O A
        m
        hYO
        hYm
        hOm
        hYOA

    have hEq : l = m :=
      HilbertPlaneIncidence.line_unique
        A O hAO
        l m
        hAl hOl
        hAm hOm

    exact hlm hEq

  have hOYB :
      PrimCollinear Geo O Y B :=
    ⟨m, hOm, hYm, hBm⟩

  have hRightAB :
      HilbertRightAngle Geo A O B :=
    hilbert_XI4_right_angle_collinear_second
      Geo
      A O Y B
      hYO.symm
      hBO.symm
      hOYB
      hNonAY
      hRightAY

  have hNonAB :
      Not (PrimCollinear Geo A O B) := by
    intro hAOB

    have hBOA :
        PrimCollinear Geo B O A :=
      PrimCollinearSymm
        Geo A O B hAOB

    have hAm :
        HilbertIncidence.OnLine A m :=
      hilbert_collinear_on_line
        Geo
        B O A
        m
        hBO
        hBm
        hOm
        hBOA

    have hEq : l = m :=
      HilbertPlaneIncidence.line_unique
        A O hAO
        l m
        hAl hOl
        hAm hOm

    exact hlm hEq

  exact ⟨hNonAB, hRightAB⟩


/--
Spatial perpendicular-bisector lemma used twice in XI.4.

If l is perpendicular at O to m, A-O-B on m with OA congruent OB, and F
is a nonvertex point of l, then AF is congruent BF.

The proof constructs the unique plane containing the two intersecting
lines l and m and performs the SAS argument inside its PlaneGeo slice.
-/
theorem hilbert_XI4_spatial_perpendicular_bisector_equidistant
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m : Geo.Line)
    (O A B F : Geo.Point)
    (hlm : Ne l m)
    (hOl : H.OnLine O l)
    (hOm : H.OnLine O m)
    (hFl : H.OnLine F l)
    (hAm : H.OnLine A m)
    (hBm : H.OnLine B m)
    (hFO : Ne F O)
    (hAOB : Geo.Between A O B)
    (hOAOB : Geo.Congruent O A O B)
    (hPerp : HilbertLinesPerpendicularAt Geo l m O) :
    Geo.Congruent A F B F := by

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm
        O hOl hOm with
    ⟨rho, hlrho, hmrho, _hUnique⟩

  let lp : PlaneLine Geo rho :=
    ⟨l, hlrho⟩

  let mp : PlaneLine Geo rho :=
    ⟨m, hmrho⟩

  let Op : PlanePoint Geo rho :=
    ⟨O, hlrho O hOl⟩

  let Fp : PlanePoint Geo rho :=
    ⟨F, hlrho F hFl⟩

  let Ap : PlanePoint Geo rho :=
    ⟨A, hmrho A hAm⟩

  let Bp : PlanePoint Geo rho :=
    ⟨B, hmrho B hBm⟩

  have hlpmp : Ne lp mp := by
    intro h
    apply hlm
    exact congrArg Subtype.val h

  have hFOplane : Ne Fp Op := by
    intro h
    apply hFO
    exact congrArg Subtype.val h

  have hAO : Ne A O :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O B hAOB).1

  have hBO : Ne B O :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O B hAOB).2.1.symm

  have hAOplane : Ne Ap Op := by
    intro h
    apply hAO
    exact congrArg Subtype.val h

  have hBOplane : Ne Bp Op := by
    intro h
    apply hBO
    exact congrArg Subtype.val h

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho) lp mp Op :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      rho lp mp Op).mpr
      hPerp

  have hFOA :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      lp mp
      Op Fp Ap
      hlpmp
      hPerpPlane
      hFOplane
      hAOplane
      hFl
      hAm

  have hFOB :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      lp mp
      Op Fp Bp
      hlpmp
      hPerpPlane
      hFOplane
      hBOplane
      hFl
      hBm

  have hNonFOA :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Fp Op Ap) :=
    hFOA.1

  have hRightFOA :
      HilbertRightAngle
        (PlaneGeo Geo rho) Fp Op Ap :=
    hFOA.2

  have hNonAOF :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Ap Op Fp) := by
    intro h
    exact
      hNonFOA
        (PrimCollinearSymm
          (PlaneGeo Geo rho)
          Ap Op Fp h)

  have hRightAOF :
      HilbertRightAngle
        (PlaneGeo Geo rho) Ap Op Fp :=
    hilbert_XI4_right_angle_swap
      (PlaneGeo Geo rho)
      Fp Op Ap
      hNonFOA
      hRightFOA

  have hAngleAOF_FOB :
      (PlaneGeo Geo rho).AngleCongruent
        Ap Op Fp
        Fp Op Bp :=
    hilbert_right_angle_opposite_extension
      (PlaneGeo Geo rho)
      Ap Op Fp Bp
      hNonAOF
      hRightAOF
      hAOB

  have hAngleAOF_BOF :
      (PlaneGeo Geo rho).AngleCongruent
        Ap Op Fp
        Bp Op Fp :=
    (Geometry.Geo.angle_congruent_reverse_second
      (PlaneGeo Geo rho)
      Ap Op Fp
      Fp Op Bp).mp
      hAngleAOF_FOB

  have hNonFOB :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Fp Op Bp) :=
    hFOB.1

  have hNonBOF :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Bp Op Fp) := by
    intro h
    exact
      hNonFOB
        (PrimCollinearSymm
          (PlaneGeo Geo rho)
          Bp Op Fp h)

  have hOAOBPlane :
      (PlaneGeo Geo rho).Congruent
        Op Ap Op Bp :=
    (planeGeo_congruent
      (Geo := Geo)
      rho Op Ap Op Bp).mpr
      hOAOB

  have hOFOF :
      (PlaneGeo Geo rho).Congruent
        Op Fp Op Fp :=
    hilbert_congruent_reflexive
      (PlaneGeo Geo rho)
      Op Fp

  have hNonOAF :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Op Ap Fp) := by
    intro h
    exact
      hNonAOF
        (PrimCollinearSwap
          (PlaneGeo Geo rho)
          Op Ap Fp h)

  have hNonOBF :
      Not (PrimCollinear
        (PlaneGeo Geo rho) Op Bp Fp) := by
    intro h
    exact
      hNonBOF
        (PrimCollinearSwap
          (PlaneGeo Geo rho)
          Op Bp Fp h)

  have hSAS :=
    hilbert_sas_third_side_and_angle
      (PlaneGeo Geo rho)
      Op Ap Fp
      Op Bp Fp
      hNonOAF
      hNonOBF
      hOAOBPlane
      hOFOF
      hAngleAOF_BOF

  exact
    (planeGeo_congruent
      (Geo := Geo)
      rho Ap Fp Bp Fp).mp
      hSAS.1


/--
The first spatial metric consequence of the balanced XI.4 cross.

For a point F on the candidate line l through O, perpendicular to both
base carriers m and n, the opposite balanced points are equidistant from
F:

  FA congruent FB,
  FC congruent FD.
-/
theorem hilbert_XI4_spatial_opposite_pairs_equidistant
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (l : Geo.Line)
    (O R A B C D : PlanePoint Geo pi)
    (F : Geo.Point)
    (hlm : Ne l m.1)
    (hln : Ne l n.1)
    (hOl : H.OnLine O.1 l)
    (hFl : H.OnLine F l)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hFO : Ne F O.1)
    (hAOB : Geo.Between A.1 O.1 B.1)
    (hCOD : Geo.Between C.1 O.1 D.1)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1)
    (hPerpM : HilbertLinesPerpendicularAt Geo l m.1 O.1)
    (hPerpN : HilbertLinesPerpendicularAt Geo l n.1 O.1) :
    Geo.Congruent A.1 F B.1 F /\
    Geo.Congruent C.1 F D.1 F := by

  have hOArefP :
      (PlaneGeo Geo pi).Congruent
        O A O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O A O R).mpr hOAref

  have hOBrefP :
      (PlaneGeo Geo pi).Congruent
        O B O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O B O R).mpr hOBref

  have hOCrefP :
      (PlaneGeo Geo pi).Congruent
        O C O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O C O R).mpr hOCref

  have hODrefP :
      (PlaneGeo Geo pi).Congruent
        O D O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O D O R).mpr hODref

  have hROA :
      (PlaneGeo Geo pi).Congruent
        O R O A :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O A O R
      hOArefP

  have hROB :
      (PlaneGeo Geo pi).Congruent
        O R O B :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O B O R
      hOBrefP

  have hROC :
      (PlaneGeo Geo pi).Congruent
        O R O C :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O C O R
      hOCrefP

  have hROD :
      (PlaneGeo Geo pi).Congruent
        O R O D :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O D O R
      hODrefP

  have hOAOBPlane :
      (PlaneGeo Geo pi).Congruent
        O A O B :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O A O B
      hROA hROB

  have hOCODPlane :
      (PlaneGeo Geo pi).Congruent
        O C O D :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O C O D
      hROC hROD

  have hOAOB :
      Geo.Congruent O.1 A.1 O.1 B.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O A O B).mp
      hOAOBPlane

  have hOCOD :
      Geo.Congruent O.1 C.1 O.1 D.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O C O D).mp
      hOCODPlane

  have hFAFB :
      Geo.Congruent A.1 F B.1 F :=
    hilbert_XI4_spatial_perpendicular_bisector_equidistant
      (Geo := Geo)
      l m.1
      O.1 A.1 B.1 F
      hlm
      hOl hOm
      hFl hAm hBm
      hFO
      hAOB
      hOAOB
      hPerpM

  have hFCFD :
      Geo.Congruent C.1 F D.1 F :=
    hilbert_XI4_spatial_perpendicular_bisector_equidistant
      (Geo := Geo)
      l n.1
      O.1 C.1 D.1 F
      hln
      hOl hOn
      hFl hCn hDn
      hFO
      hCOD
      hOCOD
      hPerpN

  exact ⟨hFAFB, hFCFD⟩


/-!
## Euclid XI.4: spatial SSS and transversal metric step
-/

/--
XI.4 spatial SSS step.

From the three side congruences

  AD ~= BC,
  AF ~= BF,
  CF ~= DF,

and noncollinearity of the two spatial triangles, obtain the angle
corresponding to Euclid's SSS comparison:

  angle DAF ~= angle CBF.
-/
theorem hilbert_XI4_spatial_SSS_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D : PlanePoint Geo pi)
    (F : Geo.Point)
    (hADF :
      Not (PrimCollinear Geo A.1 D.1 F))
    (hBCF :
      Not (PrimCollinear Geo B.1 C.1 F))
    (hADBC :
      Geo.Congruent A.1 D.1 B.1 C.1)
    (hAFBF :
      Geo.Congruent A.1 F B.1 F)
    (hCFDF :
      Geo.Congruent C.1 F D.1 F) :
    Geo.AngleCongruent D.1 A.1 F C.1 B.1 F := by

  -- The target triangle BCF has its own carrier plane in space.
  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        B.1 C.1 F hBCF with
    ⟨sigma, hBsigma, hCsigma, hFsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B.1, hBsigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨C.1, hCsigma⟩

  let Fp : PlanePoint Geo sigma :=
    ⟨F, hFsigma⟩

  have hBCFPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Bp Cp Fp) := by
    intro hPlane
    apply hBCF
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Bp Cp Fp hPlane
    simpa [Bp, Cp, Fp] using hAmbient

  -- We need DF ~= CF in the orientation expected by spatial SSS.
  -- Derive C != F directly from noncollinearity, using incidence only.
  have hCF : Ne C.1 F := by
    intro hEq
    subst F

    by_cases hBCeq : B.1 = C.1

    · rcases hilbert_line_through_point Geo C.1 with
        ⟨q, hCq⟩

      have hBq : H.OnLine B.1 q := by
        exact hBCeq.symm ▸ hCq

      exact hBCF ⟨q, hBq, hCq, hCq⟩

    · rcases
        HilbertPlaneIncidence.line_through
          B.1 C.1 hBCeq with
        ⟨q, hBq, hCq⟩

      exact hBCF ⟨q, hBq, hCq, hCq⟩

  have hDFCF :
      Geo.Congruent D.1 F C.1 F :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      C.1 F D.1 F
      hCF
      hCFDF

  exact
    hilbert_space_sss_angleA_in_plane
      (Geo := Geo)
      sigma
      A.1 D.1 F
      Bp Cp Fp
      hADF
      hBCFPlane
      hADBC
      hDFCF
      hAFBF

/--
Ambient spatial angle transport along the first ray.

If `A'` lies on the same ray from `O` as `A`, then the nondegenerate
ambient angles `AOB` and `A'OB` are congruent.  The proof creates the
plane of `A,O,B`, pulls `A'` into that plane by collinearity, performs
the ordinary planar same-ray normalization there, and bridges the
result back to ambient space.
-/
theorem hilbert_XI4_space_angle_sameRay_first_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A A' O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRay : HilbertSameRay Geo O A A') :
    Geo.AngleCongruent A O B A' O B := by

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A O B hAOB with
    ⟨sigma, hAsigma, hOsigma, hBsigma⟩

  have hOA : Ne O A :=
    hRay.1.symm

  have hA'sigma :
      S.OnPlane A' sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      O A A'
      hOA
      hOsigma hAsigma
      hRay.2.2.1

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let A'p : PlanePoint Geo sigma :=
    ⟨A', hA'sigma⟩

  let Op : PlanePoint Geo sigma :=
    ⟨O, hOsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Op Ap A'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma Op Ap A'p).mpr
    simpa [Op, Ap, A'p] using hRay

  have hAOBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Ap Op Bp) := by
    intro hPlane
    apply hAOB
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Ap Op Bp hPlane
    simpa [Ap, Op, Bp] using hAmbient

  have hAngleEq :
      (PlaneGeo Geo sigma).Angle Ap Op Bp =
      (PlaneGeo Geo sigma).Angle A'p Op Bp :=
    hilbert_angle_eq_of_sameRay_first
      (PlaneGeo Geo sigma)
      Op Ap A'p Bp hRayPlane

  have hRefl :
      (PlaneGeo Geo sigma).AngleCongruent
        Ap Op Bp Ap Op Bp :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo sigma)
      Ap Op Bp hAOBPlane

  have hPlaneAngle :
      (PlaneGeo Geo sigma).AngleCongruent
        Ap Op Bp A'p Op Bp := by
    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [Eq.symm hAngleEq]
    exact hRefl

  have hAmbient :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      sigma
      Ap Op Bp A'p Op Bp).mp
      hPlaneAngle

  simpa [Ap, A'p, Op, Bp] using hAmbient

/--
XI.4 angle normalization after the spatial SSS comparison.

The SSS step gives

  angle DAF ~= angle CBF.

With `A-G-D` and `B-J-C`, the rays `AD,AG` and `BC,BJ` coincide, hence

  angle GAF ~= angle JBF,

which is the exact included-angle orientation needed by the following
spatial SAS step on triangles `AGF` and `BJF`.
-/
theorem hilbert_XI4_spatial_SSS_angle_normalized
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D G J : PlanePoint Geo pi)
    (F : Geo.Point)
    (hADF :
      Not (PrimCollinear Geo A.1 D.1 F))
    (hCBF :
      Not (PrimCollinear Geo C.1 B.1 F))
    (hAGD :
      (PlaneGeo Geo pi).Between A G D)
    (hBJC :
      (PlaneGeo Geo pi).Between B J C)
    (hAngle :
      Geo.AngleCongruent D.1 A.1 F C.1 B.1 F) :
    Geo.AngleCongruent G.1 A.1 F J.1 B.1 F := by

  have hRayAGD :
      HilbertSameRay
        (PlaneGeo Geo pi) A G D :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo pi)
      A G D hAGD

  have hRayADG :
      HilbertSameRay
        (PlaneGeo Geo pi) A D G :=
    hilbert_sameRay_symm
      (PlaneGeo Geo pi)
      A G D hRayAGD

  have hRayADGAmbient :
      HilbertSameRay Geo A.1 D.1 G.1 :=
    (planeGeo_sameRay_iff_ambient
      (Geo := Geo)
      pi A D G).mp
      hRayADG

  have hRayBJC :
      HilbertSameRay
        (PlaneGeo Geo pi) B J C :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo pi)
      B J C hBJC

  have hRayBCJ :
      HilbertSameRay
        (PlaneGeo Geo pi) B C J :=
    hilbert_sameRay_symm
      (PlaneGeo Geo pi)
      B J C hRayBJC

  have hRayBCJAmbient :
      HilbertSameRay Geo B.1 C.1 J.1 :=
    (planeGeo_sameRay_iff_ambient
      (Geo := Geo)
      pi B C J).mp
      hRayBCJ

  have hDAF :
      Not (PrimCollinear Geo D.1 A.1 F) := by
    intro h
    exact
      hADF
        (PrimCollinearSwap
          Geo D.1 A.1 F h)

  have hDAF_GAF :
      Geo.AngleCongruent
        D.1 A.1 F
        G.1 A.1 F :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      D.1 G.1 A.1 F
      hDAF
      hRayADGAmbient

  have hCBF_JBF :
      Geo.AngleCongruent
        C.1 B.1 F
        J.1 B.1 F :=
    hilbert_XI4_space_angle_sameRay_first_congruent
      (Geo := Geo)
      C.1 J.1 B.1 F
      hCBF
      hRayBCJAmbient

  have hGAF_DAF :
      Geo.AngleCongruent
        G.1 A.1 F
        D.1 A.1 F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D.1 A.1 F
      G.1 A.1 F
      hDAF_GAF

  have hGAF_CBF :
      Geo.AngleCongruent
        G.1 A.1 F
        C.1 B.1 F :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G.1 A.1 F
      D.1 A.1 F
      C.1 B.1 F
      hGAF_DAF
      hAngle

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G.1 A.1 F
      C.1 B.1 F
      J.1 B.1 F
      hGAF_CBF
      hCBF_JBF

/--
XI.4 spatial SAS side step.

For the two spatial triangles AGF and BJF, equal adjacent sides and the
included angle imply the remaining-side congruence

  GF ~= JF.

The target triangle is carried in its own plane and compared with the
ambient source triangle through the general spatial SAS interface.
-/
theorem hilbert_XI4_spatial_SAS_transversal_side
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B G J : PlanePoint Geo pi)
    (F : Geo.Point)
    (hAGF :
      Not (PrimCollinear Geo A.1 G.1 F))
    (hBJF :
      Not (PrimCollinear Geo B.1 J.1 F))
    (hAGBJ :
      Geo.Congruent A.1 G.1 B.1 J.1)
    (hAFBF :
      Geo.Congruent A.1 F B.1 F)
    (hAngle :
      Geo.AngleCongruent G.1 A.1 F J.1 B.1 F) :
    Geo.Congruent G.1 F J.1 F := by

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        B.1 J.1 F hBJF with
    ⟨sigma, hBsigma, hJsigma, hFsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B.1, hBsigma⟩

  let Jp : PlanePoint Geo sigma :=
    ⟨J.1, hJsigma⟩

  let Fp : PlanePoint Geo sigma :=
    ⟨F, hFsigma⟩

  have hBJFPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Bp Jp Fp) := by
    intro hPlane
    apply hBJF
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Bp Jp Fp hPlane
    simpa [Bp, Jp, Fp] using hAmbient

  have hSAS :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      A.1 G.1 F
      Bp Jp Fp
      hAGF
      hBJFPlane
      hAGBJ
      hAFBF
      hAngle

  exact hSAS.1

/--
XI.4 combined spatial step.

This packages the complete chain

  AD ~= BC, AF ~= BF, CF ~= DF
       -> angle DAF ~= angle CBF           (spatial SSS)
  A-G-D, B-J-C
       -> angle GAF ~= angle JBF           (ray normalization)
  AG ~= BJ, AF ~= BF
       -> GF ~= JF                         (spatial SAS).

The noncollinearity hypotheses are kept explicit in this theorem; they
are configuration facts, not part of SSS/SAS transport itself.
-/
theorem hilbert_XI4_spatial_transversal_F_equidistant
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D G J : PlanePoint Geo pi)
    (F : Geo.Point)
    (hADF :
      Not (PrimCollinear Geo A.1 D.1 F))
    (hBCF :
      Not (PrimCollinear Geo B.1 C.1 F))
    (hAGF :
      Not (PrimCollinear Geo A.1 G.1 F))
    (hBJF :
      Not (PrimCollinear Geo B.1 J.1 F))
    (hADBC :
      Geo.Congruent A.1 D.1 B.1 C.1)
    (hAFBF :
      Geo.Congruent A.1 F B.1 F)
    (hCFDF :
      Geo.Congruent C.1 F D.1 F)
    (hAGBJ :
      Geo.Congruent A.1 G.1 B.1 J.1)
    (hAGD :
      (PlaneGeo Geo pi).Between A G D)
    (hBJC :
      (PlaneGeo Geo pi).Between B J C) :
    Geo.Congruent G.1 F J.1 F := by

  have hAngleDAF_CBF :
      Geo.AngleCongruent
        D.1 A.1 F
        C.1 B.1 F :=
    hilbert_XI4_spatial_SSS_angle
      (Geo := Geo)
      pi A B C D F
      hADF hBCF
      hADBC hAFBF hCFDF

  have hCBF :
      Not (PrimCollinear Geo C.1 B.1 F) := by
    intro h
    exact
      hBCF
        (PrimCollinearSwap
          Geo C.1 B.1 F h)

  have hAngleGAF_JBF :
      Geo.AngleCongruent
        G.1 A.1 F
        J.1 B.1 F :=
    hilbert_XI4_spatial_SSS_angle_normalized
      (Geo := Geo)
      pi A B C D G J F
      hADF hCBF
      hAGD hBJC
      hAngleDAF_CBF

  exact
    hilbert_XI4_spatial_SAS_transversal_side
      (Geo := Geo)
      pi A B G J F
      hAGF hBJF
      hAGBJ hAFBF
      hAngleGAF_JBF


/-!
## Euclid XI.4: second spatial SSS and the right angle at O
-/

/--
Second spatial SSS step in Euclid XI.4.

For the two spatial triangles GOF and JOF, the side data

  OG ~= OJ,
  GF ~= JF,
  OF ~= OF

imply

  angle GOF ~= angle JOF.

The target triangle JOF is carried in its own plane and compared to the
ambient source triangle through the general spatial SSS interface.
-/
theorem hilbert_XI4_second_spatial_SSS_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (G O J : Geo.Point)
    (F : Geo.Point)
    (hGOF :
      Not (PrimCollinear Geo G O F))
    (hJOF :
      Not (PrimCollinear Geo J O F))
    (hOF : Ne O F)
    (hOGOJ :
      Geo.Congruent O G O J)
    (hGFJF :
      Geo.Congruent G F J F) :
    Geo.AngleCongruent G O F J O F := by

  have hOJF :
      Not (PrimCollinear Geo O J F) := by
    intro h
    exact
      hJOF
        (PrimCollinearSwap
          Geo O J F h)

  have hOGF :
      Not (PrimCollinear Geo O G F) := by
    intro h
    exact
      hGOF
        (PrimCollinearSwap
          Geo O G F h)

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        O J F hOJF with
    ⟨sigma, hOsigma, hJsigma, hFsigma⟩

  let Op : PlanePoint Geo sigma :=
    ⟨O, hOsigma⟩

  let Jp : PlanePoint Geo sigma :=
    ⟨J, hJsigma⟩

  let Fp : PlanePoint Geo sigma :=
    ⟨F, hFsigma⟩

  have hOJFPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Op Jp Fp) := by
    intro hPlane
    apply hOJF
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma Op Jp Fp hPlane
    simpa [Op, Jp, Fp] using hAmbient

  have hOFOF :
      Geo.Congruent O F O F :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      O F hOF

  exact
    hilbert_space_sss_angleA_in_plane
      (Geo := Geo)
      sigma
      O G F
      Op Jp Fp
      hOGF
      hOJFPlane
      hOGOJ
      hGFJF
      hOFOF

/--
If G-O-J and the adjacent angles GOF and JOF are congruent, then GOF is
a right angle.

This is exactly Euclid's definition of a right angle: the first arm GO
is extended through O to J, and the two adjacent angles are equal.
-/
theorem hilbert_XI4_right_angle_of_adjacent_equal
    (G O J F : Geo.Point)
    (hGOJ : Geo.Between G O J)
    (hAngle :
      Geo.AngleCongruent G O F J O F) :
    HilbertRightAngle Geo G O F := by

  have hAngleRight :
      Geo.AngleCongruent G O F F O J :=
    (Geo.angle_congruent_reverse_second
      G O F
      J O F).mp hAngle

  exact
    ⟨J,
     hGOJ,
     hAngleRight⟩

/-!
## Euclid XI.4: arbitrary transversal and final theorem

The following block closes the universal-transversal part of the proof.
All auxiliary points are constructed internally; the public theorem at the
end exposes only the classical XI.4 hypotheses.
-/


/--
First Pasch exit for an arbitrary plane transversal through O in the
balanced-cross configuration of Euclid XI.4.

If q is distinct from both base carriers m and n, then q enters the
triangle A-B-D through the interior point O of AB.  Pasch therefore
forces q to leave through AD or BD.

This is the geometric branch that will later select one of the two
opposite connector families AD/BC or BD/AC.
-/
theorem hilbert_XI4_transversal_pasch_first_exit
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n q : PlaneLine Geo pi)
    (O A B C D : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hqm : Ne q m)
    (hqn : Ne q n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hOq : H.OnLine O.1 q.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (_hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB :
      (PlaneGeo Geo pi).Between A O B)
    (hCOD :
      (PlaneGeo Geo pi).Between C O D) :
    (exists G : PlanePoint Geo pi,
      (PlaneGeo Geo pi).Between A G D /\
      H.OnLine G.1 q.1) \/
    (exists G : PlanePoint Geo pi,
      (PlaneGeo Geo pi).Between B G D /\
      H.OnLine G.1 q.1) := by

  have hAOBData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB

  have hCODData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O D hCOD

  have hAO : Ne A O :=
    hAOBData.1

  have hOA : Ne O A :=
    hAO.symm

  have hOB : Ne O B :=
    hAOBData.2.1

  have hAB : Ne A B :=
    hAOBData.2.2.1

  have hOD : Ne O D :=
    hCODData.2.1

  ----------------------------------------------------------------------
  -- Triangle A-B-D is noncollinear.
  ----------------------------------------------------------------------

  have hABD :
      Not (PrimCollinear
        (PlaneGeo Geo pi) A B D) := by

    intro hCol

    rcases hCol with
      ⟨r, hAr, hBr, hDr⟩

    have hrm :
        r = m :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        A B hAB
        r m
        hAr hBr
        hAm hBm

    have hDm :
        PlaneOnLine Geo D m := by
      exact hrm ▸ hDr

    have hmnEq :
        m = n :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O D hOD
        m n
        hOm hDm
        hOn hDn

    exact hmn hmnEq

  ----------------------------------------------------------------------
  -- Since q is not m or n, none of A,B,D lies on q.
  ----------------------------------------------------------------------

  have hAq :
      Not (PlaneOnLine Geo A q) := by

    intro hAq

    have hmq :
        m = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O A hOA
        m q
        hOm hAm
        hOq hAq

    exact hqm hmq.symm

  have hBq :
      Not (PlaneOnLine Geo B q) := by

    intro hBq

    have hmq :
        m = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O B hOB
        m q
        hOm hBm
        hOq hBq

    exact hqm hmq.symm

  have hDq :
      Not (PlaneOnLine Geo D q) := by

    intro hDq

    have hnq :
        n = q :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O D hOD
        n q
        hOn hDn
        hOq hDq

    exact hqn hnq.symm

  ----------------------------------------------------------------------
  -- q enters triangle A-B-D through the open side AB at O.
  ----------------------------------------------------------------------

  have hMeetsAB :
      HilbertSegmentMeetsLine
        (PlaneGeo Geo pi) A B q :=
    ⟨O, hAOB, hOq⟩

  ----------------------------------------------------------------------
  -- Pasch: q leaves through AD or BD.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.pasch
        (Geo := PlaneGeo Geo pi)
        A B D
        hABD
        q
        hAq hBq hDq
        hMeetsAB with
    hMeetsAD | hMeetsBD

  · rcases hMeetsAD with
      ⟨G, hAGD, hGq⟩

    exact
      Or.inl
        ⟨G, hAGD, hGq⟩

  · rcases hMeetsBD with
      ⟨G, hBGD, hGq⟩

    exact
      Or.inr
        ⟨G, hBGD, hGq⟩


/--
On a plane-line q through O, every nonvertex point G has an opposite
point J on q such that G-O-J and OG ~= OJ.

This is the neutral synthetic half-turn construction needed for the
arbitrary-transversal part of Euclid XI.4.
-/
theorem hilbert_XI4_opposite_point_on_transversal
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (q : PlaneLine Geo pi)
    (O G : PlanePoint Geo pi)
    (hOq : H.OnLine O.1 q.1)
    (hGq : H.OnLine G.1 q.1)
    (hGO : Ne G O) :
    exists J : PlanePoint Geo pi,
      H.OnLine J.1 q.1 /\
      (PlaneGeo Geo pi).Between G O J /\
      Geo.Congruent O.1 G.1 O.1 J.1 := by

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo pi)
        G O hGO with
    ⟨R, hGOR⟩

  have hGORData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      G O R hGOR

  have hOR :
      Ne O R :=
    hGORData.2.1

  have hGORcol :
      PrimCollinear
        (PlaneGeo Geo pi) G O R :=
    hGORData.2.2.2.1

  have hRq :
      PlaneOnLine Geo R q := by
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := PlaneGeo Geo pi)
        hGO
        hGq
        hOq
        hGORcol

  rcases
      HilbertCongruence.segment_construction
        (Geo := PlaneGeo Geo pi)
        O G O R hOR with
    ⟨J, hRayJ, hCongJ⟩

  have hJq :
      PlaneOnLine Geo J q := by
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := PlaneGeo Geo pi)
        hOR
        hOq
        hRq
        hRayJ.2.2.1

  have hGOJ :
      (PlaneGeo Geo pi).Between G O J := by

    rcases
        hilbert_sameRay_cases
          (PlaneGeo Geo pi)
          O R J hRayJ with
      hRJ | hORJ | hOJR

    · subst J
      exact hGOR

    · exact
        (hilbert_between_outer_trans
          (PlaneGeo Geo pi)
          G O R J
          hGOR
          hORJ).2

    · have hROG :
          (PlaneGeo Geo pi).Between R O G :=
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          G O R hGOR).2.2.2.2

      have hRJO :
          (PlaneGeo Geo pi).Between R J O :=
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          O J R hOJR).2.2.2.2

      have hJOG :
          (PlaneGeo Geo pi).Between J O G :=
        (hilbert_between_inner_trans
          (PlaneGeo Geo pi)
          R J O G
          hRJO
          hROG).1

      exact
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          J O G hJOG).2.2.2.2

  have hCongAmbient :
      Geo.Congruent O.1 J.1 O.1 G.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O J O G).mp hCongJ

  have hOJ :
      Ne O.1 J.1 := by
    intro h
    apply hRayJ.2.1
    exact Subtype.ext h.symm

  have hCongDesired :
      Geo.Congruent O.1 G.1 O.1 J.1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      O.1 J.1 O.1 G.1
      hOJ
      hCongAmbient

  exact
    ⟨J,
     hJq,
     hGOJ,
     hCongDesired⟩


/--
First connector-family landing lemma for the arbitrary-transversal part
of Euclid XI.4.

In the balanced cross, suppose G lies between A and D and J is the point
opposite G across O, with OG congruent OJ. Then J lies between B and C.

The proof is neutral. Two SAS applications around O give

  AG ~= BJ
  GD ~= JC

while the balanced-cross SAS already gives

  AD ~= BC.

Hilbert Theorem 27 then transports the order A-G-D to B-J-C.
-/
theorem hilbert_XI4_first_exit_opposite_lands_on_BC
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (O R A B C D G J : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB : Geo.Between A.1 O.1 B.1)
    (hCOD : Geo.Between C.1 O.1 D.1)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1)
    (hAGD : Geo.Between A.1 G.1 D.1)
    (hGOJ : Geo.Between G.1 O.1 J.1)
    (hOGOJ : Geo.Congruent O.1 G.1 O.1 J.1) :
    Geo.Between B.1 J.1 C.1 := by

  have hNon :=
    planeGeo_XI4_cross_noncollinear
      (Geo := Geo)
      pi m n
      O A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD

  have hNonOAD :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O A D) :=
    hNon.1

  have hNonOBC :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O B C) :=
    hNon.2

  have hAOBData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB

  have hCODData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O D hCOD

  have hAGDData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A G D hAGD

  have hGOJData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      G O J hGOJ

  have hAG : Ne A G :=
    hAGDData.1

  have hGD : Ne G D :=
    hAGDData.2.1

  have hOB : Ne O B :=
    hAOBData.2.1

  have hOJ : Ne O J :=
    hGOJData.2.1

  have hAGDcol :
      PrimCollinear
        (PlaneGeo Geo pi) A G D :=
    hAGDData.2.2.2.1

  have hAOBcol :
      PrimCollinear
        (PlaneGeo Geo pi) A O B :=
    hAOBData.2.2.2.1

  have hGOJcol :
      PrimCollinear
        (PlaneGeo Geo pi) G O J :=
    hGOJData.2.2.2.1

  ----------------------------------------------------------------------
  -- Noncollinearity for the two SAS applications.
  ----------------------------------------------------------------------

  have hNonAOG :
      Not (PrimCollinear
        (PlaneGeo Geo pi) A O G) := by
    intro hAOG

    have hOAG :
        PrimCollinear
          (PlaneGeo Geo pi) O A G :=
      PrimCollinearSwap
        (PlaneGeo Geo pi)
        A O G hAOG

    have hOAD :
        PrimCollinear
          (PlaneGeo Geo pi) O A D :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        O A G D
        hAG
        hOAG
        hAGDcol

    exact hNonOAD hOAD

  have hNonOAG :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O A G) := by
    intro h
    exact hNonAOG
      (PrimCollinearSwap
        (PlaneGeo Geo pi)
        O A G h)

  have hNonBOJ :
      Not (PrimCollinear
        (PlaneGeo Geo pi) B O J) := by
    intro hBOJ

    have hOBJ :
        PrimCollinear
          (PlaneGeo Geo pi) O B J :=
      PrimCollinearSwap
        (PlaneGeo Geo pi)
        B O J hBOJ

    have hAOJ :
        PrimCollinear
          (PlaneGeo Geo pi) A O J :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        A O B J
        hOB
        hAOBcol
        hOBJ

    have hOJG :
        PrimCollinear
          (PlaneGeo Geo pi) O J G :=
      PrimCollinearCycle
        (PlaneGeo Geo pi)
        G O J hGOJcol

    have hAOG :
        PrimCollinear
          (PlaneGeo Geo pi) A O G :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        A O J G
        hOJ
        hAOJ
        hOJG

    exact hNonAOG hAOG

  have hNonOBJ :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O B J) := by
    intro h
    exact hNonBOJ
      (PrimCollinearSwap
        (PlaneGeo Geo pi)
        O B J h)

  have hNonDOG :
      Not (PrimCollinear
        (PlaneGeo Geo pi) D O G) := by
    intro hDOG

    have hDGO :
        PrimCollinear
          (PlaneGeo Geo pi) D G O :=
      PrimCollinearRotate
        (PlaneGeo Geo pi)
        D O G hDOG

    have hGDO :
        PrimCollinear
          (PlaneGeo Geo pi) G D O :=
      PrimCollinearSwap
        (PlaneGeo Geo pi)
        D G O hDGO

    have hAGO :
        PrimCollinear
          (PlaneGeo Geo pi) A G O :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        A G D O
        hGD
        hAGDcol
        hGDO

    exact hNonAOG
      (PrimCollinearRotate
        (PlaneGeo Geo pi)
        A G O hAGO)

  have hNonODG :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O D G) := by
    intro h
    exact hNonDOG
      (PrimCollinearSwap
        (PlaneGeo Geo pi)
        O D G h)

  have hDOC :
      (PlaneGeo Geo pi).Between D O C :=
    hCODData.2.2.2.2

  have hDOCData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      D O C hDOC

  have hDOCcol :
      PrimCollinear
        (PlaneGeo Geo pi) D O C :=
    hDOCData.2.2.2.1

  have hOC : Ne O C :=
    hDOCData.2.1

  have hNonCOJ :
      Not (PrimCollinear
        (PlaneGeo Geo pi) C O J) := by
    intro hCOJ

    have hOCJ :
        PrimCollinear
          (PlaneGeo Geo pi) O C J :=
      PrimCollinearSwap
        (PlaneGeo Geo pi)
        C O J hCOJ

    have hDOJ :
        PrimCollinear
          (PlaneGeo Geo pi) D O J :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        D O C J
        hOC
        hDOCcol
        hOCJ

    have hOJG :
        PrimCollinear
          (PlaneGeo Geo pi) O J G :=
      PrimCollinearCycle
        (PlaneGeo Geo pi)
        G O J hGOJcol

    have hDOG :
        PrimCollinear
          (PlaneGeo Geo pi) D O G :=
      hilbert_primCollinear_trans
        (PlaneGeo Geo pi)
        D O J G
        hOJ
        hDOJ
        hOJG

    exact hNonDOG hDOG

  have hNonOCJ :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O C J) := by
    intro h
    exact hNonCOJ
      (PrimCollinearSwap
        (PlaneGeo Geo pi)
        O C J h)

  ----------------------------------------------------------------------
  -- Equal radial segments in PlaneGeo.
  ----------------------------------------------------------------------

  have hOArefP :
      (PlaneGeo Geo pi).Congruent O A O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O A O R).mpr hOAref

  have hOBrefP :
      (PlaneGeo Geo pi).Congruent O B O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O B O R).mpr hOBref

  have hOCrefP :
      (PlaneGeo Geo pi).Congruent O C O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O C O R).mpr hOCref

  have hODrefP :
      (PlaneGeo Geo pi).Congruent O D O R :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O D O R).mpr hODref

  have hROA :
      (PlaneGeo Geo pi).Congruent O R O A :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O A O R hOArefP

  have hROB :
      (PlaneGeo Geo pi).Congruent O R O B :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O B O R hOBrefP

  have hROC :
      (PlaneGeo Geo pi).Congruent O R O C :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O C O R hOCrefP

  have hROD :
      (PlaneGeo Geo pi).Congruent O R O D :=
    hilbert_congruent_symmetry
      (PlaneGeo Geo pi)
      O D O R hODrefP

  have hOAOB :
      (PlaneGeo Geo pi).Congruent O A O B :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O A O B
      hROA hROB

  have hODOC :
      (PlaneGeo Geo pi).Congruent O D O C :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      O R O D O C
      hROD hROC

  have hOGOJP :
      (PlaneGeo Geo pi).Congruent O G O J :=
    (planeGeo_congruent
      (Geo := Geo)
      pi O G O J).mpr hOGOJ

  ----------------------------------------------------------------------
  -- SAS around O: AG ~= BJ.
  ----------------------------------------------------------------------

  have hVerticalAOG :
      (PlaneGeo Geo pi).AngleCongruent
        A O G
        B O J :=
    hilbert_vertical_angles
      (PlaneGeo Geo pi)
      A O G B J
      hAOB
      hGOJ
      hNonAOG

  have hAGBJ :
      (PlaneGeo Geo pi).Congruent A G B J :=
    (hilbert_sas_third_side_and_angle
      (PlaneGeo Geo pi)
      O A G
      O B J
      hNonOAG
      hNonOBJ
      hOAOB
      hOGOJP
      hVerticalAOG).1

  ----------------------------------------------------------------------
  -- SAS around O: DG ~= CJ.
  ----------------------------------------------------------------------

  have hVerticalDOG :
      (PlaneGeo Geo pi).AngleCongruent
        D O G
        C O J :=
    hilbert_vertical_angles
      (PlaneGeo Geo pi)
      D O G C J
      hDOC
      hGOJ
      hNonDOG

  have hGDJC :
      (PlaneGeo Geo pi).Congruent G D J C := by

    have hDGCJ :
        (PlaneGeo Geo pi).Congruent D G C J :=
      (hilbert_sas_third_side_and_angle
        (PlaneGeo Geo pi)
        O D G
        O C J
        hNonODG
        hNonOCJ
        hODOC
        hOGOJP
        hVerticalDOG).1

    exact
      CongruentReverseBoth
        (PlaneGeo Geo pi)
        D G C J hDGCJ

  ----------------------------------------------------------------------
  -- The whole connector sides: AD ~= BC.
  ----------------------------------------------------------------------

  have hFirst :=
    hilbert_XI4_balanced_cross_first_SAS
      (Geo := Geo)
      pi m n
      O R A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD
      hOAref hOBref
      hOCref hODref

  have hADBC :
      (PlaneGeo Geo pi).Congruent A D B C :=
    (planeGeo_congruent
      (Geo := Geo)
      pi A D B C).mpr hFirst.1

  ----------------------------------------------------------------------
  -- Target nondegeneracy for Hilbert Theorem 27.
  ----------------------------------------------------------------------

  have hNonBJO :
      Not (PrimCollinear
        (PlaneGeo Geo pi) B J O) := by
    intro h
    exact hNonBOJ
      (PrimCollinearRotate
        (PlaneGeo Geo pi)
        B J O h)

  have hBJ : Ne B J :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo pi)
      B J O hNonBJO

  have hNonJCO :
      Not (PrimCollinear
        (PlaneGeo Geo pi) J C O) := by
    intro h
    exact hNonCOJ
      (PrimCollinearCycle
        (PlaneGeo Geo pi)
        J C O h)

  have hJC : Ne J C :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo pi)
      J C O hNonJCO

  have hNonBCO :
      Not (PrimCollinear
        (PlaneGeo Geo pi) B C O) := by
    intro h

    have hCOB :
        PrimCollinear
          (PlaneGeo Geo pi) C O B :=
      PrimCollinearCycle
        (PlaneGeo Geo pi)
        B C O h

    have hOBC :
        PrimCollinear
          (PlaneGeo Geo pi) O B C :=
      PrimCollinearCycle
        (PlaneGeo Geo pi)
        C O B hCOB

    exact hNonOBC hOBC

  have hBC : Ne B C :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo pi)
      B C O hNonBCO

  ----------------------------------------------------------------------
  -- Hilbert Theorem 27 transports A-G-D to B-J-C.
  ----------------------------------------------------------------------

  exact
    hilbert_theorem27_three_points
      (PlaneGeo Geo pi)
      A G D
      B J C
      hAGD
      hBJ hJC hBC
      hAGBJ
      hADBC
      hGDJC


/--
Second connector-family landing lemma for the arbitrary-transversal part
of Euclid XI.4.

If the Pasch exit lies on BD, so B-G-D, and J is opposite G across O,
then J lies between A and C.

This is the first landing lemma with A and B exchanged.
-/
theorem hilbert_XI4_second_exit_opposite_lands_on_AC
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (O R A B C D G J : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB : Geo.Between A.1 O.1 B.1)
    (hCOD : Geo.Between C.1 O.1 D.1)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1)
    (hBGD : Geo.Between B.1 G.1 D.1)
    (hGOJ : Geo.Between G.1 O.1 J.1)
    (hOGOJ : Geo.Congruent O.1 G.1 O.1 J.1) :
    Geo.Between A.1 J.1 C.1 := by

  have hBOA :
      (PlaneGeo Geo pi).Between B O A :=
    (HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB).2.2.2.2

  exact
    hilbert_XI4_first_exit_opposite_lands_on_BC
      (Geo := Geo)
      pi m n
      O R
      B A C D
      G J
      hmn
      hOm hOn
      hBm hAm
      hCn hDn
      hBOA hCOD
      hOBref hOAref
      hOCref hODref
      hBGD
      hGOJ
      hOGOJ


/--
Arbitrary-transversal connector package for Euclid XI.4.

Let q be any plane line through O distinct from the two balanced-cross
carriers m and n. Then there exist opposite points G,J on q such that
G-O-J and OG ~= OJ, and exactly the connector family selected by Pasch
contains them in the required order:

  A-G-D and B-J-C,

or

  B-G-D and A-J-C.

No parallel axiom is used. The proof combines:
  * Pasch in triangle A-B-D,
  * opposite-point construction on q,
  * the two neutral landing lemmas.
-/
theorem hilbert_XI4_arbitrary_transversal_connector_package
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n q : PlaneLine Geo pi)
    (O R A B C D : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hqm : Ne q m)
    (hqn : Ne q n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hOq : H.OnLine O.1 q.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB :
      (PlaneGeo Geo pi).Between A O B)
    (hCOD :
      (PlaneGeo Geo pi).Between C O D)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1) :
    exists G J : PlanePoint Geo pi,
      H.OnLine G.1 q.1 /\
      H.OnLine J.1 q.1 /\
      (PlaneGeo Geo pi).Between G O J /\
      Geo.Congruent O.1 G.1 O.1 J.1 /\
      (((PlaneGeo Geo pi).Between A G D /\
        (PlaneGeo Geo pi).Between B J C) \/
       ((PlaneGeo Geo pi).Between B G D /\
        (PlaneGeo Geo pi).Between A J C)) := by

  have hNon :=
    planeGeo_XI4_cross_noncollinear
      (Geo := Geo)
      pi m n
      O A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD

  have hNonOAD :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O A D) :=
    hNon.1

  have hAOBData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB

  have hCODData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O D hCOD

  have hOB : Ne O B :=
    hAOBData.2.1

  have hOD : Ne O D :=
    hCODData.2.1

  have hNonOBD :
      Not (PrimCollinear
        (PlaneGeo Geo pi) O B D) := by

    intro hCol

    rcases hCol with
      ⟨r, hOr, hBr, hDr⟩

    have hmr :
        m = r :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O B hOB
        m r
        hOm hBm
        hOr hBr

    have hnr :
        n = r :=
      HilbertPlaneIncidence.line_unique
        (Geo := PlaneGeo Geo pi)
        O D hOD
        n r
        hOn hDn
        hOr hDr

    apply hmn
    exact Eq.trans hmr (Eq.symm hnr)

  rcases
      hilbert_XI4_transversal_pasch_first_exit
        (Geo := Geo)
        pi m n q
        O A B C D
        hmn hqm hqn
        hOm hOn hOq
        hAm hBm
        hCn hDn
        hAOB hCOD with
    hAD | hBD

  ----------------------------------------------------------------------
  -- Pasch exits through AD.
  ----------------------------------------------------------------------

  · rcases hAD with
      ⟨G, hAGD, hGq⟩

    have hGO : Ne G O := by
      intro hEq
      subst G

      have hAOD :
          PrimCollinear
            (PlaneGeo Geo pi) A O D :=
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          A O D hAGD).2.2.2.1

      exact
        hNonOAD
          (PrimCollinearSwap
            (PlaneGeo Geo pi)
            A O D hAOD)

    rcases
        hilbert_XI4_opposite_point_on_transversal
          (Geo := Geo)
          pi q
          O G
          hOq hGq hGO with
      ⟨J, hJq, hGOJ, hOGOJ⟩

    have hBJC :
        (PlaneGeo Geo pi).Between B J C :=
      hilbert_XI4_first_exit_opposite_lands_on_BC
        (Geo := Geo)
        pi m n
        O R A B C D G J
        hmn
        hOm hOn
        hAm hBm
        hCn hDn
        hAOB hCOD
        hOAref hOBref
        hOCref hODref
        hAGD
        hGOJ
        hOGOJ

    exact
      ⟨G, J,
       hGq, hJq,
       hGOJ,
       hOGOJ,
       Or.inl ⟨hAGD, hBJC⟩⟩

  ----------------------------------------------------------------------
  -- Pasch exits through BD.
  ----------------------------------------------------------------------

  · rcases hBD with
      ⟨G, hBGD, hGq⟩

    have hGO : Ne G O := by
      intro hEq
      subst G

      have hBOD :
          PrimCollinear
            (PlaneGeo Geo pi) B O D :=
        (HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo pi)
          B O D hBGD).2.2.2.1

      exact
        hNonOBD
          (PrimCollinearSwap
            (PlaneGeo Geo pi)
            B O D hBOD)

    rcases
        hilbert_XI4_opposite_point_on_transversal
          (Geo := Geo)
          pi q
          O G
          hOq hGq hGO with
      ⟨J, hJq, hGOJ, hOGOJ⟩

    have hAJC :
        (PlaneGeo Geo pi).Between A J C :=
      hilbert_XI4_second_exit_opposite_lands_on_AC
        (Geo := Geo)
        pi m n
        O R A B C D G J
        hmn
        hOm hOn
        hAm hBm
        hCn hDn
        hAOB hCOD
        hOAref hOBref
        hOCref hODref
        hBGD
        hGOJ
        hOGOJ

    exact
      ⟨G, J,
       hGq, hJq,
       hGOJ,
       hOGOJ,
       Or.inr ⟨hBGD, hAJC⟩⟩


/--
For every plane transversal q through O distinct from the two balanced-cross
carriers m,n, the point F off the plane determines a right angle with q,
provided the already established spatial equidistance data

  AF ~= BF
  CF ~= DF

hold.

This is the arbitrary-transversal right-angle core of Euclid XI.4.
-/
theorem hilbert_XI4_arbitrary_transversal_right_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n q : PlaneLine Geo pi)
    (O R A B C D : PlanePoint Geo pi)
    (F : Geo.Point)
    (hmn : Ne m n)
    (hqm : Ne q m)
    (hqn : Ne q n)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hOq : H.OnLine O.1 q.1)
    (hAm : H.OnLine A.1 m.1)
    (hBm : H.OnLine B.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hDn : H.OnLine D.1 n.1)
    (hAOB :
      (PlaneGeo Geo pi).Between A O B)
    (hCOD :
      (PlaneGeo Geo pi).Between C O D)
    (hOAref : Geo.Congruent O.1 A.1 O.1 R.1)
    (hOBref : Geo.Congruent O.1 B.1 O.1 R.1)
    (hOCref : Geo.Congruent O.1 C.1 O.1 R.1)
    (hODref : Geo.Congruent O.1 D.1 O.1 R.1)
    (hFoff : Not (S.OnPlane F pi))
    (hAFBF : Geo.Congruent A.1 F B.1 F)
    (hCFDF : Geo.Congruent C.1 F D.1 F) :
    exists G : PlanePoint Geo pi,
      H.OnLine G.1 q.1 /\
      Ne G.1 O.1 /\
      HilbertRightAngle Geo G.1 O.1 F := by

  ----------------------------------------------------------------------
  -- Any line through two distinct plane points cannot also contain F,
  -- because F is outside pi.
  ----------------------------------------------------------------------

  have noncol_plane_pair_F :
      forall P Q : PlanePoint Geo pi,
        Ne P.1 Q.1 ->
        Not (PrimCollinear Geo P.1 Q.1 F) := by
    intro P Q hPQ hCol
    apply hFoff
    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi P.1 Q.1 F
        hPQ
        P.2 Q.2
        hCol

  have hOF : Ne O.1 F := by
    intro h
    apply hFoff
    rw [← h]
    exact O.2

  ----------------------------------------------------------------------
  -- Fixed balanced-cross side congruence AD ~= BC.
  ----------------------------------------------------------------------

  have hFirst :=
    hilbert_XI4_balanced_cross_first_SAS
      (Geo := Geo)
      pi m n
      O R A B C D
      hmn
      hOm hOn
      hAm hBm
      hCn hDn
      hAOB hCOD
      hOAref hOBref
      hOCref hODref

  have hADBC :
      Geo.Congruent A.1 D.1 B.1 C.1 :=
    hFirst.1

  ----------------------------------------------------------------------
  -- The swapped balanced-cross side congruence BD ~= AC.
  ----------------------------------------------------------------------

  have hBOA :
      (PlaneGeo Geo pi).Between B O A :=
    (HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB).2.2.2.2

  have hSecondCross :=
    hilbert_XI4_balanced_cross_first_SAS
      (Geo := Geo)
      pi m n
      O R B A C D
      hmn
      hOm hOn
      hBm hAm
      hCn hDn
      hBOA hCOD
      hOBref hOAref
      hOCref hODref

  have hBDAC :
      Geo.Congruent B.1 D.1 A.1 C.1 :=
    hSecondCross.1

  have hAF : Ne A.1 F := by
    intro h
    apply hFoff
    rw [← h]
    exact A.2

  have hBFAF :
      Geo.Congruent B.1 F A.1 F :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A.1 F B.1 F
      hAF
      hAFBF

  ----------------------------------------------------------------------
  -- Obtain the Pasch/opposite-point connector package.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI4_arbitrary_transversal_connector_package
        (Geo := Geo)
        pi m n q
        O R A B C D
        hmn hqm hqn
        hOm hOn hOq
        hAm hBm
        hCn hDn
        hAOB hCOD
        hOAref hOBref
        hOCref hODref with
    ⟨G, J, hGq, hJq, hGOJ, hOGOJ, hBranch⟩

  have hGOJData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      G O J hGOJ

  have hGO : Ne G.1 O.1 := by
    intro hEq
    apply hGOJData.1
    exact Subtype.ext hEq

  have hOJ : Ne O.1 J.1 := by
    intro hEq
    apply hGOJData.2.1
    exact Subtype.ext hEq

  have hJO : Ne J.1 O.1 :=
    hOJ.symm

  have hGOF :
      Not (PrimCollinear Geo G.1 O.1 F) :=
    noncol_plane_pair_F G O hGO

  have hJOF :
      Not (PrimCollinear Geo J.1 O.1 F) :=
    noncol_plane_pair_F J O hJO

  rcases hBranch with hADbranch | hBDbranch

  ----------------------------------------------------------------------
  -- First connector family: A-G-D and B-J-C.
  ----------------------------------------------------------------------

  · rcases hADbranch with ⟨hAGD, hBJC⟩

    have hAGDData :=
      HilbertOrder.between_incidence
        (Geo := PlaneGeo Geo pi)
        A G D hAGD

    have hBJCData :=
      HilbertOrder.between_incidence
        (Geo := PlaneGeo Geo pi)
        B J C hBJC

    have hAD : Ne A.1 D.1 := by
      intro hEq
      apply hAGDData.2.2.1
      exact Subtype.ext hEq

    have hBC : Ne B.1 C.1 := by
      intro hEq
      apply hBJCData.2.2.1
      exact Subtype.ext hEq

    have hAG : Ne A.1 G.1 := by
      intro hEq
      apply hAGDData.1
      exact Subtype.ext hEq

    have hBJ : Ne B.1 J.1 := by
      intro hEq
      apply hBJCData.1
      exact Subtype.ext hEq

    have hADF :
        Not (PrimCollinear Geo A.1 D.1 F) :=
      noncol_plane_pair_F A D hAD

    have hBCF :
        Not (PrimCollinear Geo B.1 C.1 F) :=
      noncol_plane_pair_F B C hBC

    have hAGF :
        Not (PrimCollinear Geo A.1 G.1 F) :=
      noncol_plane_pair_F A G hAG

    have hBJF :
        Not (PrimCollinear Geo B.1 J.1 F) :=
      noncol_plane_pair_F B J hBJ

    have hASA :=
      hilbert_XI4_transversal_ASA
        (Geo := Geo)
        pi m n
        O R A B C D G J
        hmn
        hOm hOn
        hAm hBm
        hCn hDn
        hAOB hCOD
        hOAref hOBref
        hOCref hODref
        hAGD hBJC hGOJ

    have hAGBJ :
        Geo.Congruent A.1 G.1 B.1 J.1 :=
      hASA.2

    have hGFJF :
        Geo.Congruent G.1 F J.1 F :=
      hilbert_XI4_spatial_transversal_F_equidistant
        (Geo := Geo)
        pi A B C D G J F
        hADF hBCF
        hAGF hBJF
        hADBC
        hAFBF
        hCFDF
        hAGBJ
        hAGD hBJC

    have hAngle :
        Geo.AngleCongruent G.1 O.1 F J.1 O.1 F :=
      hilbert_XI4_second_spatial_SSS_angle
        (Geo := Geo)
        G.1 O.1 J.1 F
        hGOF hJOF
        hOF
        hOGOJ
        hGFJF

    have hRight :
        HilbertRightAngle Geo G.1 O.1 F :=
      hilbert_XI4_right_angle_of_adjacent_equal
        (Geo := Geo)
        G.1 O.1 J.1 F
        hGOJ
        hAngle

    exact ⟨G, hGq, hGO, hRight⟩

  ----------------------------------------------------------------------
  -- Second connector family: B-G-D and A-J-C.
  -- This is the same spatial chain after swapping A and B.
  ----------------------------------------------------------------------

  · rcases hBDbranch with ⟨hBGD, hAJC⟩

    have hBGDData :=
      HilbertOrder.between_incidence
        (Geo := PlaneGeo Geo pi)
        B G D hBGD

    have hAJCData :=
      HilbertOrder.between_incidence
        (Geo := PlaneGeo Geo pi)
        A J C hAJC

    have hBD : Ne B.1 D.1 := by
      intro hEq
      apply hBGDData.2.2.1
      exact Subtype.ext hEq

    have hAC : Ne A.1 C.1 := by
      intro hEq
      apply hAJCData.2.2.1
      exact Subtype.ext hEq

    have hBG : Ne B.1 G.1 := by
      intro hEq
      apply hBGDData.1
      exact Subtype.ext hEq

    have hAJ : Ne A.1 J.1 := by
      intro hEq
      apply hAJCData.1
      exact Subtype.ext hEq

    have hBDF :
        Not (PrimCollinear Geo B.1 D.1 F) :=
      noncol_plane_pair_F B D hBD

    have hACF :
        Not (PrimCollinear Geo A.1 C.1 F) :=
      noncol_plane_pair_F A C hAC

    have hBGF :
        Not (PrimCollinear Geo B.1 G.1 F) :=
      noncol_plane_pair_F B G hBG

    have hAJF :
        Not (PrimCollinear Geo A.1 J.1 F) :=
      noncol_plane_pair_F A J hAJ

    have hASA :=
      hilbert_XI4_transversal_ASA
        (Geo := Geo)
        pi m n
        O R B A C D G J
        hmn
        hOm hOn
        hBm hAm
        hCn hDn
        hBOA hCOD
        hOBref hOAref
        hOCref hODref
        hBGD hAJC hGOJ

    have hBGAJ :
        Geo.Congruent B.1 G.1 A.1 J.1 :=
      hASA.2

    have hGFJF :
        Geo.Congruent G.1 F J.1 F :=
      hilbert_XI4_spatial_transversal_F_equidistant
        (Geo := Geo)
        pi B A C D G J F
        hBDF hACF
        hBGF hAJF
        hBDAC
        hBFAF
        hCFDF
        hBGAJ
        hBGD hAJC

    have hAngle :
        Geo.AngleCongruent G.1 O.1 F J.1 O.1 F :=
      hilbert_XI4_second_spatial_SSS_angle
        (Geo := Geo)
        G.1 O.1 J.1 F
        hGOF hJOF
        hOF
        hOGOJ
        hGFJF

    have hRight :
        HilbertRightAngle Geo G.1 O.1 F :=
      hilbert_XI4_right_angle_of_adjacent_equal
        (Geo := Geo)
        G.1 O.1 J.1 F
        hGOJ
        hAngle

    exact ⟨G, hGq, hGO, hRight⟩


/--
Neutral uniqueness of the perpendicular direction at a fixed foot.

If F-O-M and F-O-N are both nondegenerate right angles, then M,O,N
are collinear.  The proof uses Hilbert III.4 on each half-plane.
-/
theorem hilbert_XI4_two_right_angles_same_first_arm_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (F O M N : Geo.Point)
    (base : Geo.Line)
    (hFO : Ne F O)
    (hFbase : HilbertIncidence.OnLine F base)
    (hObase : HilbertIncidence.OnLine O base)
    (hFOM : Not (PrimCollinear Geo F O M))
    (hFON : Not (PrimCollinear Geo F O N))
    (hRightM : HilbertRightAngle Geo F O M)
    (hRightN : HilbertRightAngle Geo F O N) :
    PrimCollinear Geo M O N := by

  have hMoff :
      Not (HilbertIncidence.OnLine M base) := by
    intro hMbase
    exact hFOM
      ⟨base, hFbase, hObase, hMbase⟩

  have hNoff :
      Not (HilbertIncidence.OnLine N base) := by
    intro hNbase
    exact hFON
      ⟨base, hFbase, hObase, hNbase⟩

  by_cases hSameMN :
      HilbertSameSide Geo M N base

  ----------------------------------------------------------------------
  -- Same half-plane: Hilbert III.4 gives the same perpendicular ray.
  ----------------------------------------------------------------------

  · have hAngles :
        Geo.AngleCongruent F O M F O N :=
      hilbert_all_right_angles_congruent
        Geo
        F O M
        F O N
        hFOM hFON
        hRightM hRightN

    rcases
        hilbert_angle_unique_common_ray
          Geo
          F O M N
          base
          hFO
          hFbase hObase
          hMoff
          hSameMN
          hAngles with
      ⟨X, hRayXM, hRayXN⟩

    have hOX :
        Ne O X :=
      hRayXM.1.symm

    have hOXM :
        PrimCollinear Geo O X M :=
      hRayXM.2.2.1

    have hMOX :
        PrimCollinear Geo M O X :=
      PrimCollinearCycle
        Geo X M O
        (PrimCollinearCycle
          Geo O X M hOXM)

    have hOXN :
        PrimCollinear Geo O X N :=
      hRayXN.2.2.1

    exact
      hilbert_primCollinear_trans
        Geo
        M O X N
        hOX
        hMOX
        hOXN

  ----------------------------------------------------------------------
  -- Opposite half-planes: reverse M through O.  The opposite point M'
  -- lies in N's half-plane and still determines a right angle.
  ----------------------------------------------------------------------

  · have hOppMN :
        HilbertOppositeSide Geo M N base :=
      hilbert_oppositeSide_of_not_sameSide
        Geo
        M N base
        hMoff hNoff
        hSameMN

    have hMO : Ne M O := by
      intro hEq
      subst M
      exact hFOM
        ⟨base, hFbase, hObase, hObase⟩

    rcases
        HilbertOrder.between_extension
          (Geo := Geo)
          M O hMO with
      ⟨M', hMOM'⟩

    by_contra hMON

    have hSameNM' :
        HilbertSameSide Geo N M' base :=
      hilbert_sameSide_after_opposite_extension
        Geo
        M O N M'
        base
        hObase
        hMON
        hMOM'
        hOppMN

    have hM'off :
        Not (HilbertIncidence.OnLine M' base) :=
      hSameNM'.2.1

    have hFOM' :
        Not (PrimCollinear Geo F O M') :=
      hilbert_not_collinear_of_off_line
        Geo
        F O M'
        base
        hFO
        hFbase hObase
        hM'off

    have hMOF :
        Not (PrimCollinear Geo M O F) := by
      intro h
      exact hFOM
        (PrimCollinearSymm
          Geo M O F h)

    have hRightMOF :
        HilbertRightAngle Geo M O F :=
      hilbert_XI4_right_angle_swap
        Geo
        F O M
        hFOM
        hRightM

    have hAngleMOF_FOM' :
        Geo.AngleCongruent M O F F O M' :=
      hilbert_right_angle_opposite_extension
        Geo
        M O F M'
        hMOF
        hRightMOF
        hMOM'

    have hRightM' :
        HilbertRightAngle Geo F O M' :=
      hilbert_right_angle_transport
        Geo
        M O F
        F O M'
        hMOF
        hFOM'
        hRightMOF
        hAngleMOF_FOM'

    have hSameM'N :
        HilbertSameSide Geo M' N base :=
      hilbert_sameSide_symm
        Geo N M' base hSameNM'

    have hAngles' :
        Geo.AngleCongruent F O M' F O N :=
      hilbert_all_right_angles_congruent
        Geo
        F O M'
        F O N
        hFOM' hFON
        hRightM' hRightN

    rcases
        hilbert_angle_unique_common_ray
          Geo
          F O M' N
          base
          hFO
          hFbase hObase
          hM'off
          hSameM'N
          hAngles' with
      ⟨X, hRayXM', hRayXN⟩

    have hOX :
        Ne O X :=
      hRayXM'.1.symm

    have hOXM' :
        PrimCollinear Geo O X M' :=
      hRayXM'.2.2.1

    have hM'OX :
        PrimCollinear Geo M' O X :=
      PrimCollinearCycle
        Geo X M' O
        (PrimCollinearCycle
          Geo O X M' hOXM')

    have hOXN :
        PrimCollinear Geo O X N :=
      hRayXN.2.2.1

    have hM'ON :
        PrimCollinear Geo M' O N :=
      hilbert_primCollinear_trans
        Geo
        M' O X N
        hOX
        hM'OX
        hOXN

    have hOM'N :
        PrimCollinear Geo O M' N :=
      PrimCollinearSwap
        Geo M' O N hM'ON

    have hMOM'Data :=
      HilbertOrder.between_incidence
        (Geo := Geo)
        M O M' hMOM'

    have hOM' : Ne O M' :=
      hMOM'Data.2.1

    have hMOM'col :
        PrimCollinear Geo M O M' :=
      hMOM'Data.2.2.2.1

    exact hMON
      (hilbert_primCollinear_trans
        Geo
        M O M' N
        hOM'
        hMOM'col
        hOM'N)


/--
XI.4 off-plane bridge.

Let m,n be distinct lines of pi through O.  If the ambient line l through O
is perpendicular to both, then every nonvertex point F of l is outside pi.

Otherwise l would itself be a line of pi.  The two perpendicular directions
OA and OC would then be unique in PlaneGeo pi, forcing m=n.
-/
theorem hilbert_XI4_perpendicular_point_off_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (l : Geo.Line)
    (O A C : PlanePoint Geo pi)
    (F : Geo.Point)
    (hmn : Ne m n)
    (hlm : Ne l m.1)
    (hln : Ne l n.1)
    (hOl : H.OnLine O.1 l)
    (hFl : H.OnLine F l)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hAm : H.OnLine A.1 m.1)
    (hCn : H.OnLine C.1 n.1)
    (hFO : Ne F O.1)
    (hAO : Ne A O)
    (hCO : Ne C O)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m.1 O.1)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n.1 O.1) :
    Not (S.OnPlane F pi) := by

  intro hFpi

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      O.1 F hFO.symm
      l hOl hFl
      pi O.2 hFpi

  let lp : PlaneLine Geo pi :=
    ⟨l, hlpi⟩

  let Fp : PlanePoint Geo pi :=
    ⟨F, hFpi⟩

  have hFOplane : Ne Fp O := by
    intro hEq
    apply hFO
    exact congrArg Subtype.val hEq

  have hlpm : Ne lp m := by
    intro hEq
    apply hlm
    exact congrArg Subtype.val hEq

  have hlpn : Ne lp n := by
    intro hEq
    apply hln
    exact congrArg Subtype.val hEq

  have hPerpMPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) lp m O :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      pi lp m O).mpr
      hPerpM

  have hPerpNPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) lp n O :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      pi lp n O).mpr
      hPerpN

  have hFOA :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo pi)
      lp m
      O Fp A
      hlpm
      hPerpMPlane
      hFOplane
      hAO
      hFl
      hAm

  have hFOC :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo pi)
      lp n
      O Fp C
      hlpn
      hPerpNPlane
      hFOplane
      hCO
      hFl
      hCn

  have hAOC :
      PrimCollinear
        (PlaneGeo Geo pi) A O C :=
    hilbert_XI4_two_right_angles_same_first_arm_collinear
      (PlaneGeo Geo pi)
      Fp O A C
      lp
      hFOplane
      hFl hOl
      hFOA.1 hFOC.1
      hFOA.2 hFOC.2

  have hCOnM :
      HilbertIncidence.OnLine C m :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := PlaneGeo Geo pi)
      hAO
      hAm hOm
      hAOC

  have hEq :
      m = n :=
    HilbertPlaneIncidence.line_unique
      (Geo := PlaneGeo Geo pi)
      O C hCO.symm
      m n
      hOm hCOnM
      hOn hCn

  exact hmn hEq


/--
Core form of Euclid XI.4.

Let m,n be two distinct lines of the plane pi through O.  Let l be an
ambient line through O, distinct from both m and n, and perpendicular at O
to both of them.  Then l is perpendicular to the whole plane pi at O.

The proof is fully synthetic.  The balanced cross, the auxiliary point F on
l, and the arbitrary transversal construction are all internal.
-/
theorem hilbert_XI4_line_perpendicular_plane_core
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (l : Geo.Line)
    (O : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hlm : Ne l m.1)
    (hln : Ne l n.1)
    (hOl : H.OnLine O.1 l)
    (hOm : H.OnLine O.1 m.1)
    (hOn : H.OnLine O.1 n.1)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m.1 O.1)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n.1 O.1) :
    HilbertLinePerpendicularPlaneAt Geo l pi O.1 := by

  ----------------------------------------------------------------------
  -- Choose a nonvertex point F on l.
  ----------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l O.1 with
    ⟨F, hFO, hFl⟩

  ----------------------------------------------------------------------
  -- Construct the balanced cross in pi.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI4_balanced_cross_exists
        (Geo := Geo)
        pi m n O
        hOm hOn with
    ⟨R, A, B, C, D,
     hRO,
     hRm,
     hAm, hBm,
     hCn, hDn,
     hAOB, hCOD,
     hOAref, hOBref,
     hOCref, hODref⟩

  have hAOBData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      A O B hAOB

  have hCODData :=
    HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo pi)
      C O D hCOD

  have hAO :
      Ne A O :=
    hAOBData.1

  have hCO :
      Ne C O :=
    hCODData.1

  ----------------------------------------------------------------------
  -- F cannot lie in pi.
  ----------------------------------------------------------------------

  have hFoff :
      Not (S.OnPlane F pi) :=
    hilbert_XI4_perpendicular_point_off_plane
      (Geo := Geo)
      pi m n l
      O A C F
      hmn
      hlm hln
      hOl hFl
      hOm hOn
      hAm hCn
      hFO
      hAO hCO
      hPerpM hPerpN

  ----------------------------------------------------------------------
  -- The two opposite balanced pairs are equidistant from F.
  ----------------------------------------------------------------------

  have hOppPairs :=
    hilbert_XI4_spatial_opposite_pairs_equidistant
      (Geo := Geo)
      pi m n l
      O R A B C D
      F
      hlm hln
      hOl hFl
      hOm hOn
      hAm hBm
      hCn hDn
      hFO
      hAOB hCOD
      hOAref hOBref
      hOCref hODref
      hPerpM hPerpN

  have hAFBF :
      Geo.Congruent A.1 F B.1 F :=
    hOppPairs.1

  have hCFDF :
      Geo.Congruent C.1 F D.1 F :=
    hOppPairs.2

  ----------------------------------------------------------------------
  -- Prove perpendicularity to every line q of pi through O.
  ----------------------------------------------------------------------

  refine
    ⟨hOl, O.2, ?_⟩

  intro q hqPi hOq

  by_cases hqm : q = m.1

  ----------------------------------------------------------------------
  -- q = m.
  ----------------------------------------------------------------------

  · simpa [hqm] using hPerpM

  by_cases hqn : q = n.1

  ----------------------------------------------------------------------
  -- q = n.
  ----------------------------------------------------------------------

  · simpa [hqn] using hPerpN

  ----------------------------------------------------------------------
  -- q is distinct from both m and n.
  ----------------------------------------------------------------------

  · let qp : PlaneLine Geo pi :=
      ⟨q, hqPi⟩

    have hqpm :
        Ne qp m := by
      intro hEq
      apply hqm
      exact congrArg Subtype.val hEq

    have hqpn :
        Ne qp n := by
      intro hEq
      apply hqn
      exact congrArg Subtype.val hEq

    rcases
        hilbert_XI4_arbitrary_transversal_right_angle
          (Geo := Geo)
          pi m n qp
          O R A B C D
          F
          hmn
          hqpm hqpn
          hOm hOn
          hOq
          hAm hBm
          hCn hDn
          hAOB hCOD
          hOAref hOBref
          hOCref hODref
          hFoff
          hAFBF hCFDF with
      ⟨G, hGq, hGO, hRightGOF⟩

    have hGOF :
        Not (PrimCollinear Geo G.1 O.1 F) := by
      intro hCol

      apply hFoff

      exact
        hilbert_onPlane_of_primCollinear_with_two_on_plane
          (Geo := Geo)
          pi
          G.1 O.1 F
          hGO
          G.2 O.2
          hCol

    have hFOG :
        Not (PrimCollinear Geo F O.1 G.1) := by
      intro hCol
      exact
        hGOF
          (PrimCollinearSymm
            Geo F O.1 G.1 hCol)

    ------------------------------------------------------------------
    -- Swap the right angle inside the explicit plane through l and q.
    --
    -- We deliberately do not install an ambient HilbertCongruence
    -- instance.  The two intersecting lines l and q determine a plane
    -- rho, and PlaneGeo rho carries the ordinary planar congruence API.
    ------------------------------------------------------------------

    have hlq : Ne l q := by
      intro hEq
      apply hFoff
      apply hqPi F
      rw [← hEq]
      exact hFl

    rcases
        hilbert_plane_through_two_intersecting_lines
          (Geo := Geo)
          l q hlq
          O.1 hOl hOq with
      ⟨rho, hlrho, hqrho, _hUniqueRho⟩

    let Op : PlanePoint Geo rho :=
      ⟨O.1, hlrho O.1 hOl⟩

    let Fp : PlanePoint Geo rho :=
      ⟨F, hlrho F hFl⟩

    let Gp : PlanePoint Geo rho :=
      ⟨G.1, hqrho G.1 hGq⟩

    have hGOFPlane :
        Not (PrimCollinear
          (PlaneGeo Geo rho) Gp Op Fp) := by
      intro hCol
      apply hGOF
      exact
        planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          rho Gp Op Fp hCol

    have hRightGOFPlane :
        HilbertRightAngle
          (PlaneGeo Geo rho) Gp Op Fp := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          rho Gp Op Fp).mpr
      simpa [Gp, Op, Fp] using hRightGOF

    have hRightFOGPlane :
        HilbertRightAngle
          (PlaneGeo Geo rho) Fp Op Gp :=
      hilbert_XI4_right_angle_swap
        (PlaneGeo Geo rho)
        Gp Op Fp
        hGOFPlane
        hRightGOFPlane

    have hRightFOG :
        HilbertRightAngle Geo F O.1 G.1 := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          rho Fp Op Gp).mp
      exact hRightFOGPlane

    exact
      ⟨hOl,
       hOq,
       F, G.1,
       hFO,
       hGO,
       hFl,
       hGq,
       hFOG,
       hRightFOG⟩


/--
Euclid XI.4.

If an ambient line l is perpendicular at O to two distinct lines m,n
of the plane pi through O, then l is perpendicular to the plane pi at O.

The distinctness of l from m and n is no longer a separate hypothesis:
it follows from the nondegenerate line-line perpendicularity predicate.
-/
theorem euclid_proposition_11_4
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (l : Geo.Line)
    (O : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m.1 O.1)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n.1 O.1) :
    HilbertLinePerpendicularPlaneAt Geo l pi O.1 := by

  have hlm :
      Ne l m.1 :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l m.1 O.1 hPerpM

  have hln :
      Ne l n.1 :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l n.1 O.1 hPerpN

  have hOl :
      H.OnLine O.1 l :=
    hPerpM.1

  have hOm :
      H.OnLine O.1 m.1 :=
    hPerpM.2.1

  have hOn :
      H.OnLine O.1 n.1 :=
    hPerpN.2.1

  exact
    hilbert_XI4_line_perpendicular_plane_core
      (Geo := Geo)
      pi m n l O
      hmn
      hlm hln
      hOl hOm hOn
      hPerpM hPerpN


end Geometry

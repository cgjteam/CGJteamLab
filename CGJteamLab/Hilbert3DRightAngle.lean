import CGJteamLab.Hilbert3DInterface
import CGJteamLab.HilbertRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Neutral 3D right-angle congruence layer

This module contains proposition-independent consequences of spatial
Hilbert Groups II and III needed whenever right angles carried by
different ambient planes must be compared.

The material is extracted from the previously verified Coxeter 3D
development.  No Coxeter objects or reflection machinery are used.

Main result:

    hilbert_space_all_right_angles_congruent

No global planar `HilbertCongruence Geo` instance is installed.
-/

theorem hilbert_space_sas_third_side
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C A' B' C' : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear Geo A' B' C'))
    (hAB :
      Geo.Congruent A B A' B')
    (hAC :
      Geo.Congruent A C A' C')
    (hAngle :
      Geo.AngleCongruent B A C B' A' C') :
    Geo.Congruent B C B' C' := by

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A' B' C'
        hA'B'C' with
    ⟨sigma, hA'sigma, hB'sigma, hC'sigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨A', hA'sigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B', hB'sigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨C', hC'sigma⟩

  have hPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Cp) := by
    intro hCol
    have hAmbient :
        PrimCollinear Geo A' B' C' :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma
        Ap Bp Cp
        hCol
    exact hA'B'C' hAmbient

  have hResult :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      A B C
      Ap Bp Cp
      hABC
      hPlane
      hAB
      hAC
      hAngle

  simpa [Ap, Bp, Cp] using hResult.1

theorem hilbert_space_coplanar_right_angles_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A O B A' O' B' : PlanePoint Geo pi)
    (hAOB :
      Not (PrimCollinear Geo A.1 O.1 B.1))
    (hA'OB' :
      Not (PrimCollinear Geo A'.1 O'.1 B'.1))
    (hRight :
      HilbertRightAngle Geo A.1 O.1 B.1)
    (hRight' :
      HilbertRightAngle Geo A'.1 O'.1 B'.1) :
    Geo.AngleCongruent
      A.1 O.1 B.1
      A'.1 O'.1 B'.1 := by

  have hAOBPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi) A O B) := by
    intro hCol
    exact hAOB
      (planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi A O B hCol)

  have hA'OB'Plane :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi) A' O' B') := by
    intro hCol
    exact hA'OB'
      (planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi A' O' B' hCol)

  have hRightPlane :
      HilbertRightAngle
        (PlaneGeo Geo pi) A O B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      pi A O B).mpr hRight

  have hRightPlane' :
      HilbertRightAngle
        (PlaneGeo Geo pi) A' O' B' :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      pi A' O' B').mpr hRight'

  have hAnglePlane :
      (PlaneGeo Geo pi).AngleCongruent
        A O B A' O' B' :=
    hilbert_all_right_angles_congruent
      (PlaneGeo Geo pi)
      A O B
      A' O' B'
      hAOBPlane
      hA'OB'Plane
      hRightPlane
      hRightPlane'

  exact
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      pi
      A O B
      A' O' B').mp
      hAnglePlane


/--
Coplanar right-triangle hypotenuse comparison.

If two nondegenerate right triangles lie in the same ambient plane,
their corresponding legs are congruent, and the right angles are at
the first vertices, then their hypotenuses are congruent.

-/
theorem hilbert_space_sameRay_of_between
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O P Q : Geo.Point)
    (hOPQ : Geo.Between O P Q) :
    HilbertSameRay Geo O P Q := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      O P Q hOPQ

  exact
    ⟨hData.1.symm,
     hData.2.2.1.symm,
     hData.2.2.2.1,
     (HilbertSpaceOrder.between_unique
       (Geo := Geo)
       O P Q
       hData.2.2.2.1
       hOPQ).1⟩


/--
Ambient rays determined by two representatives of the same Hilbert ray
are extensionally equal.

The proof puts their common carrier line into one explicit ambient
plane and invokes the already established planar theorem in `PlaneGeo`.

-/
theorem hilbert_space_sameRay_ray_eq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O P Q : Geo.Point)
    (hRay : HilbertSameRay Geo O P Q) :
    Geo.ray O P = Geo.ray O Q := by

  rcases hRay.2.2.1 with
    ⟨l, hOl, hPl, hQl⟩

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨R, hRl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l R hRl with
    ⟨pi, hlpi, _hRpi, _hUniquePi⟩

  let Op : PlanePoint Geo pi :=
    ⟨O, hlpi O hOl⟩

  let Pp : PlanePoint Geo pi :=
    ⟨P, hlpi P hPl⟩

  let Qp : PlanePoint Geo pi :=
    ⟨Q, hlpi Q hQl⟩

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Pp Qp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Pp Qp).mpr
    simpa [Op, Pp, Qp] using hRay

  have hEqPlane :
      (PlaneGeo Geo pi).ray Op Pp =
      (PlaneGeo Geo pi).ray Op Qp :=
    hilbert_sameRay_ray_eq
      (PlaneGeo Geo pi)
      Op Pp Qp
      hRayPlane

  have hEqMapped :
      planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Pp) =
      planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Qp) :=
    congrArg
      (fun X : Set (PlanePoint Geo pi) =>
        planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          X)
      hEqPlane

  calc
    Geo.ray O P =
        planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Pp) := by
      symm
      simpa [Op, Pp] using
        (planeGeo_ray_to_ambient
          (Geo := Geo)
          pi Op Pp)
    _ =
        planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Qp) :=
      hEqMapped
    _ = Geo.ray O Q := by
      simpa [Op, Qp] using
        (planeGeo_ray_to_ambient
          (Geo := Geo)
          pi Op Qp)


/--
Changing the first arm of an ambient angle to another representative of
the same Hilbert ray does not change the angle object.

-/
theorem hilbert_space_angle_eq_of_sameRay_first
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O A A' B : Geo.Point)
    (hAA' : HilbertSameRay Geo O A A') :
    Geo.Angle A O B =
    Geo.Angle A' O B := by

  unfold Geometry.Geo.Angle
  rw [
    hilbert_space_sameRay_ray_eq
      (Geo := Geo)
      O A A' hAA'
  ]


/--
Changing the second arm of an ambient angle to another representative
of the same Hilbert ray does not change the angle object.

-/
theorem hilbert_space_angle_eq_of_sameRay_second
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O A B B' : Geo.Point)
    (hBB' : HilbertSameRay Geo O B B') :
    Geo.Angle A O B =
    Geo.Angle A O B' := by

  unfold Geometry.Geo.Angle
  rw [
    hilbert_space_sameRay_ray_eq
      (Geo := Geo)
      O B B' hBB'
  ]


/--
Ambient noncollinearity is preserved when both arms of an angle are
replaced by representatives of the same rays.

This is purely incidence-theoretic once the same-ray data are given.

-/
theorem hilbert_space_noncollinear_of_sameRays
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A O B X Y : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hAX : HilbertSameRay Geo O A X)
    (hBY : HilbertSameRay Geo O B Y) :
    Not (PrimCollinear Geo X O Y) := by

  intro hXOY

  have hAOX :
      PrimCollinear Geo A O X :=
    PrimCollinearRotate Geo A X O
      (PrimCollinearCycle
        Geo O A X hAX.2.2.1)

  have hOXY :
      PrimCollinear Geo O X Y :=
    PrimCollinearSwap
      Geo X O Y hXOY

  have hAOY :
      PrimCollinear Geo A O Y :=
    hilbert_primCollinear_trans
      Geo A O X Y
      hAX.2.1.symm
      hAOX hOXY

  have hOYB :
      PrimCollinear Geo O Y B :=
    PrimCollinearRotate
      Geo O B Y hBY.2.2.1

  exact
    hAOB
      (hilbert_primCollinear_trans
        Geo A O Y B
        hBY.2.1.symm
        hAOY hOYB)


/--
Ambient transport of strict betweenness along two Hilbert rays.

All five points lie on one ambient line.  That line is placed in an
explicit plane, the planar theorem is applied in `PlaneGeo`, and the
result is read back in the ambient geometry.

-/
theorem hilbert_space_between_transport_sameRays
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (A O C A' C' : Geo.Point)
    (hAOC : Geo.Between A O C)
    (hAA' : HilbertSameRay Geo O A A')
    (hCC' : HilbertSameRay Geo O C C') :
    Geo.Between A' O C' := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O C hAOC

  rcases hData.2.2.2.1 with
    ⟨l, hAl, hOl, hCl⟩

  have hA'l :
      H.OnLine A' l := by
    have hAOA' :
        PrimCollinear Geo A O A' :=
      PrimCollinearSwap
        Geo O A A'
        hAA'.2.2.1

    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hData.1
        hAl hOl
        hAOA'

  have hC'l :
      H.OnLine C' l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hData.2.1
      hOl hCl
      hCC'.2.2.1

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨R, hRl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l R hRl with
    ⟨pi, hlpi, _hRpi, _hUniquePi⟩

  let Ap : PlanePoint Geo pi :=
    ⟨A, hlpi A hAl⟩

  let Op : PlanePoint Geo pi :=
    ⟨O, hlpi O hOl⟩

  let Cp : PlanePoint Geo pi :=
    ⟨C, hlpi C hCl⟩

  let A'p : PlanePoint Geo pi :=
    ⟨A', hlpi A' hA'l⟩

  let C'p : PlanePoint Geo pi :=
    ⟨C', hlpi C' hC'l⟩

  have hAOCPlane :
      (PlaneGeo Geo pi).Between
        Ap Op Cp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        pi Ap Op Cp).mpr
    simpa [Ap, Op, Cp] using hAOC

  have hAA'Plane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Ap A'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Ap A'p).mpr
    simpa [Op, Ap, A'p] using hAA'

  have hCC'Plane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Cp C'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Cp C'p).mpr
    simpa [Op, Cp, C'p] using hCC'

  have hResult :
      (PlaneGeo Geo pi).Between
        A'p Op C'p :=
    hilbert_between_transport_sameRays
      (PlaneGeo Geo pi)
      Ap Op Cp A'p C'p
      hAOCPlane
      hAA'Plane
      hCC'Plane

  have hResultAmbient :
      Geo.Between A' O C' :=
    (planeGeo_between
      (Geo := Geo)
      pi A'p Op C'p).mp
      hResult

  simpa [A'p, Op, C'p] using hResultAmbient



theorem hilbert_space_adjacent_angles_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A O B C A' O' B' C' : Geo.Point)
    (hAOC : Geo.Between A O C)
    (hA'O'C' : Geo.Between A' O' C')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'O'B' : Not (PrimCollinear Geo A' O' B'))
    (hAngle :
      Geo.AngleCongruent A O B A' O' B') :
    Geo.AngleCongruent B O C B' O' C' := by

  have hAOCData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O C hAOC

  have hA'O'C'Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A' O' C' hA'O'C'

  have hOA : O ≠ A :=
    hAOCData.1.symm

  have hOC : O ≠ C :=
    hAOCData.2.1

  have hOB : O ≠ B := by
    have hBOA :
        Not (PrimCollinear Geo B O A) := by
      intro h
      exact
        hAOB
          (PrimCollinearRotate
            Geo A B O
            (PrimCollinearCycle
              Geo O A B
              (PrimCollinearCycle
                Geo B O A h)))
    exact
      (hilbert_noncollinear_ne_first
        Geo B O A hBOA).symm

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' A'
        O A
        hOA with
    ⟨X, hAX, hOX⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' B'
        O B
        hOB with
    ⟨Y, hBY, hOY⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' C'
        O C
        hOC with
    ⟨Z, hCZ, hOZ⟩

  have hXOY :
      Not (PrimCollinear Geo X O Y) :=
    hilbert_space_noncollinear_of_sameRays
      (Geo := Geo)
      A O B X Y
      hAOB hAX hBY

  have hAngleLeft :
      Geo.Angle A O B =
      Geo.Angle X O Y := by
    calc
      Geo.Angle A O B =
          Geo.Angle X O B :=
        hilbert_space_angle_eq_of_sameRay_first
          (Geo := Geo)
          O A X B hAX
      _ =
          Geo.Angle X O Y :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          O X B Y hBY

  have hAngleXOY :
      Geo.AngleCongruent
        X O Y
        A' O' B' := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢
    rw [← hAngleLeft]
    exact hAngle

  have hFirstAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      O X Y
      O' A' B'
      (by
        intro h
        exact hXOY
          (PrimCollinearSwap
            Geo O X Y h))
      (by
        intro h
        exact hA'O'B'
          (PrimCollinearSwap
            Geo O' A' B' h))
      hOX
      hOY
      hAngleXOY

  have hFirstSide :
      Geo.Congruent X Y A' B' :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      O X Y
      O' A' B'
      (by
        intro h
        exact hXOY
          (PrimCollinearSwap
            Geo O X Y h))
      (by
        intro h
        exact hA'O'B'
          (PrimCollinearSwap
            Geo O' A' B' h))
      hOX
      hOY
      hAngleXOY

  have hXOZ :
      Geo.Between X O Z :=
    hilbert_space_between_transport_sameRays
      (Geo := Geo)
      A O C
      X Z
      hAOC
      hAX
      hCZ

  have hXO :
      Geo.Congruent X O A' O' :=
    (Geo.congruent_reverse_second
      X O O' A').mp
      ((Geo.congruent_reverse_first
        O X O' A').mp hOX)

  have hXZ :
      Geo.Congruent X Z A' C' :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      X O Z
      A' O' C'
      hXOZ
      hA'O'C'
      hXO
      hOZ

  have hRayXOZ :
      HilbertSameRay Geo X O Z :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      X O Z hXOZ

  have hRayA'O'C' :
      HilbertSameRay Geo A' O' C' :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      A' O' C' hA'O'C'

  have hAtXLeft :
      Geo.Angle O X Y =
      Geo.Angle Y X Z := by
    calc
      Geo.Angle O X Y =
          Geo.Angle Y X O :=
        Geo.angle_swap O X Y
      _ =
          Geo.Angle Y X Z :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          X Y O Z hRayXOZ

  have hAtXRight :
      Geo.Angle O' A' B' =
      Geo.Angle B' A' C' := by
    calc
      Geo.Angle O' A' B' =
          Geo.Angle B' A' O' :=
        Geo.angle_swap O' A' B'
      _ =
          Geo.Angle B' A' C' :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          A' B' O' C' hRayA'O'C'

  have hAngleXYZ :
      Geo.AngleCongruent
        Y X Z
        B' A' C' := by
    unfold Geometry.Geo.AngleCongruent
      at hFirstAngles ⊢
    rw [← hAtXLeft, ← hAtXRight]
    exact hFirstAngles.1

  have hXYZ :
      Not (PrimCollinear Geo X Y Z) := by
    intro h

    have hOXZ :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ).2.2.2.1

    have hXZY :
        PrimCollinear Geo X Z Y :=
      PrimCollinearRotate
        Geo X Y Z h

    have hOXY :
        PrimCollinear Geo O X Y :=
      hilbert_primCollinear_trans
        Geo O X Z Y
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          X O Z hXOZ).2.2.1
        (PrimCollinearSwap
          Geo X O Z hOXZ)
        hXZY

    exact
      hXOY
        (PrimCollinearSwap
          Geo O X Y hOXY)

  have hA'B'C' :
      Not (PrimCollinear Geo A' B' C') := by
    intro h

    have hO'A'C' :
        PrimCollinear Geo O' A' C' :=
      PrimCollinearSwap
        Geo A' O' C'
        hA'O'C'Data.2.2.2.1

    have hA'C'B' :
        PrimCollinear Geo A' C' B' :=
      PrimCollinearRotate
        Geo A' B' C' h

    have hO'A'B' :
        PrimCollinear Geo O' A' B' :=
      hilbert_primCollinear_trans
        Geo O' A' C' B'
        hA'O'C'Data.2.2.1
        hO'A'C'
        hA'C'B'

    exact
      hA'O'B'
        (PrimCollinearSwap
          Geo O' A' B' hO'A'B')

  have hSecondSide :
      Geo.Congruent Y Z B' C' :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      X Y Z
      A' B' C'
      hXYZ
      hA'B'C'
      hFirstSide
      hXZ
      hAngleXYZ

  have hSecondAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      X Y Z
      A' B' C'
      hXYZ
      hA'B'C'
      hFirstSide
      hXZ
      hAngleXYZ

  have hZOX :
      Geo.Between Z O X :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X O Z hXOZ).2.2.2.2

  have hRayZOX :
      HilbertSameRay Geo Z O X :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      Z O X hZOX

  have hC'O'A' :
      Geo.Between C' O' A' :=
    hA'O'C'Data.2.2.2.2

  have hRayC'O'A' :
      HilbertSameRay Geo C' O' A' :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      C' O' A' hC'O'A'

  have hAngleZOY :
      Geo.AngleCongruent
        O Z Y
        O' C' B' := by

    have hLeft :
        Geo.Angle O Z Y =
        Geo.Angle X Z Y :=
      hilbert_space_angle_eq_of_sameRay_first
        (Geo := Geo)
        Z O X Y hRayZOX

    have hRight :
        Geo.Angle O' C' B' =
        Geo.Angle A' C' B' :=
      hilbert_space_angle_eq_of_sameRay_first
        (Geo := Geo)
        C' O' A' B' hRayC'O'A'

    unfold Geometry.Geo.AngleCongruent
      at hSecondAngles ⊢

    rw [hLeft, hRight]
    exact hSecondAngles.2

  have hZO :
      Geo.Congruent Z O C' O' :=
    (Geo.congruent_reverse_second
      Z O O' C').mp
      ((Geo.congruent_reverse_first
        O Z O' C').mp hOZ)

  have hZY :
      Geo.Congruent Z Y C' B' :=
    (Geo.congruent_reverse_second
      Z Y B' C').mp
      ((Geo.congruent_reverse_first
        Y Z B' C').mp hSecondSide)

  have hZOY :
      Not (PrimCollinear Geo Z O Y) := by
    intro h

    have hXOZCol :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ).2.2.2.1

    exact
      hXOY
        (hilbert_primCollinear_trans
          Geo X O Z Y
          (HilbertSpaceOrder.between_incidence
            (Geo := Geo)
            X O Z hXOZ).2.1
          hXOZCol
          (PrimCollinearSwap
            Geo Z O Y h))

  have hC'O'B' :
      Not (PrimCollinear Geo C' O' B') := by
    intro h

    have hO'C'B' :
        PrimCollinear Geo O' C' B' :=
      PrimCollinearSwap
        Geo C' O' B' h

    exact
      hA'O'B'
        (hilbert_primCollinear_trans
          Geo A' O' C' B'
          hA'O'C'Data.2.1
          hA'O'C'Data.2.2.2.1
          hO'C'B')

  have hFinal :
      Geo.AngleCongruent
        Z O Y
        C' O' B' :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      Z O Y
      C' O' B'
      hZOY
      hC'O'B'
      hZO
      hZY
      hAngleZOY

  have hTargetLeft :
      Geo.Angle B O C =
      Geo.Angle Z O Y := by
    calc
      Geo.Angle B O C =
          Geo.Angle C O B :=
        Geo.angle_swap B O C
      _ =
          Geo.Angle Z O B :=
        hilbert_space_angle_eq_of_sameRay_first
          (Geo := Geo)
          O C Z B hCZ
      _ =
          Geo.Angle Z O Y :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          O Z B Y hBY

  have hTargetRight :
      Geo.Angle B' O' C' =
      Geo.Angle C' O' B' :=
    Geo.angle_swap B' O' C'

  unfold Geometry.Geo.AngleCongruent
    at hFinal ⊢

  rw [hTargetLeft, hTargetRight]
  exact hFinal


/-!
# Spatial Hilbert Theorem 21 and right triangles

Spatial Hilbert Theorem 21: all ambient right angles are congruent.

-/
theorem hilbert_space_all_right_angles_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A O B A' O' B' : Geo.Point)
    (hAOB :
      Not (PrimCollinear Geo A O B))
    (hA'OB' :
      Not (PrimCollinear Geo A' O' B'))
    (hRight :
      HilbertRightAngle Geo A O B)
    (hRight' :
      HilbertRightAngle Geo A' O' B') :
    Geo.AngleCongruent
      A O B
      A' O' B' := by

  --------------------------------------------------------------------
  -- The target right angle determines an explicit ambient plane.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A' O' B'
        hA'OB' with
    ⟨pi, hA'pi, hO'pi, hB'pi⟩

  have hA'O' :
      Ne A' O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hA'OB'

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A' O' hA'O' with
    ⟨base, hA'base, hO'base⟩

  have hBasePi :
      HilbertLineInPlane Geo base pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A' O' hA'O'
      base
      hA'base hO'base
      pi
      hA'pi hO'pi

  have hB'off :
      Not (H.OnLine B' base) := by
    intro hB'base
    exact
      hA'OB'
        ⟨base,
         hA'base,
         hO'base,
         hB'base⟩

  --------------------------------------------------------------------
  -- Copy the first ambient angle into the plane of the second one.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        A O B
        A' O' B'
        hAOB
        hA'O'
        pi
        base
        hBasePi
        hA'base
        hO'base
        hB'pi
        hB'off with
    ⟨K, hKSame, hCopy, _hUnique⟩

  have hKpi :
      S.OnPlane K pi :=
    hKSame.1

  have hKoff :
      Not (H.OnLine K base) :=
    hKSame.2.2.1

  have hA'OK :
      Not (PrimCollinear Geo A' O' K) :=
    hilbert_not_collinear_of_off_line
      Geo
      A' O' K
      base
      hA'O'
      hA'base
      hO'base
      hKoff

  --------------------------------------------------------------------
  -- Expose the supplementary points witnessing both right angles.
  --------------------------------------------------------------------

  rcases hRight with
    ⟨C, hAOC, hRightEq⟩

  rcases hRight' with
    ⟨D', hA'O'D', hRightEqTarget⟩

  --------------------------------------------------------------------
  -- Hilbert 14 transports the source supplementary congruence.
  --
  -- From
  --
  --   AOB ~= A'O'K
  --
  -- and the linear pairs A-O-C, A'-O'-D',
  --
  --   BOC ~= KO'D'.
  --
  -- Since AOB ~= BOC, the copied angle A'O'K is right.
  --------------------------------------------------------------------

  have hSupp :
      Geo.AngleCongruent
        B O C
        K O' D' :=
    hilbert_space_adjacent_angles_congruent
      (Geo := Geo)
      A O B C
      A' O' K D'
      hAOC
      hA'O'D'
      hAOB
      hA'OK
      hCopy

  have hCopySymm :
      Geo.AngleCongruent
        A' O' K
        A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      A' O' K
      hCopy

  have hCopiedToSourceSupplement :
      Geo.AngleCongruent
        A' O' K
        B O C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A' O' K
      A O B
      B O C
      hCopySymm
      hRightEq

  have hCopiedRightEq :
      Geo.AngleCongruent
        A' O' K
        K O' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A' O' K
      B O C
      K O' D'
      hCopiedToSourceSupplement
      hSupp

  have hRightK :
      HilbertRightAngle Geo A' O' K :=
    ⟨D',
     hA'O'D',
     hCopiedRightEq⟩

  --------------------------------------------------------------------
  -- Both A'O'K and A'O'B' now lie in pi.
  -- Apply the coplanar Hilbert 21 established above.
  --------------------------------------------------------------------

  let A'p : PlanePoint Geo pi :=
    ⟨A', hA'pi⟩

  let O'p : PlanePoint Geo pi :=
    ⟨O', hO'pi⟩

  let Kp : PlanePoint Geo pi :=
    ⟨K, hKpi⟩

  let B'p : PlanePoint Geo pi :=
    ⟨B', hB'pi⟩

  have hLocal :
      Geo.AngleCongruent
        A' O' K
        A' O' B' :=
    hilbert_space_coplanar_right_angles_congruent
      (Geo := Geo)
      pi
      A'p O'p Kp
      A'p O'p B'p
      (by
        simpa [A'p, O'p, Kp] using hA'OK)
      (by
        simpa [A'p, O'p, B'p] using hA'OB')
      hRightK
      ⟨D', hA'O'D', hRightEqTarget⟩

  --------------------------------------------------------------------
  -- Compose the copied angle with the local comparison.
  --------------------------------------------------------------------

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O B
      A' O' K
      A' O' B'
      hCopy
      hLocal

end Geometry

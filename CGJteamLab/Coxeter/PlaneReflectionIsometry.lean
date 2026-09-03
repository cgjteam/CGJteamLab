import CGJteamLab.Coxeter.PlaneReflection
import CGJteamLab.Coxeter.ReflectionIsometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Canonical off-plane data for plane reflection.
-/
theorem planeReflect_off_plane_data
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point)
    (hPoff : Not (S.OnPlane P pi)) :
    exists F : Geo.Point,
      PerpendicularToPlaneThrough Geo pi F P /\
      HilbertIsMidpoint
        Geo F P (planeReflect Geo pi P) := by

  rcases
      planeReflect_spec
        (Geo := Geo) pi P with
    hFixed | hOff

  · exact False.elim (hPoff hFixed.1)

  · rcases hOff with
      ⟨_hPoff, F, hPerp, hMid⟩

    exact ⟨F, hPerp, hMid⟩


/--
If l is the normal line used for P, then the reflected image of P
lies on the same normal line.
-/
theorem planeReflect_on_normal_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P F : Geo.Point)
    (l : Geo.Line)
    (hPl : H.OnLine P l)
    (hLperp :
      HilbertLinePerpendicularPlaneAt Geo l pi F)
    (hMid :
      HilbertIsMidpoint
        Geo F P (planeReflect Geo pi P)) :
    H.OnLine (planeReflect Geo pi P) l := by

  have hFl : H.OnLine F l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp).1

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      P F (planeReflect Geo pi P)
      hMid.1

  have hPF : Ne P F :=
    hData.1

  have hCol :
      PrimCollinear
        Geo P F (planeReflect Geo pi P) :=
    hData.2.2.2.1

  exact
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hPF
      hPl hFl
      hCol


/--
The perpendicular foot of P is also the perpendicular foot of its
reflected image.
-/
theorem planeReflect_reflected_perpendicular
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P F : Geo.Point)
    (hPerp :
      PerpendicularToPlaneThrough Geo pi F P)
    (hMid :
      HilbertIsMidpoint
        Geo F P (planeReflect Geo pi P)) :
    PerpendicularToPlaneThrough
      Geo pi F (planeReflect Geo pi P) := by

  rcases hPerp with
    ⟨l, hPl, hLperp⟩

  have hP'l :
      H.OnLine (planeReflect Geo pi P) l :=
    planeReflect_on_normal_line
      (Geo := Geo)
      pi P F l
      hPl hLperp hMid

  exact
    ⟨l, hP'l, hLperp⟩


/--
Every point of the mirror plane is equidistant from a point and its
plane-reflected image.

The nontrivial case is reduced to ordinary planar line reflection in
a plane sigma containing the normal line PF and the chosen mirror point Q.
-/
theorem planeReflect_plane_point_equidistant
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q : Geo.Point)
    (hQpi : S.OnPlane Q pi) :
    Geo.Congruent
      Q P
      Q (planeReflect Geo pi P) := by

  by_cases hPpi : S.OnPlane P pi

  ----------------------------------------------------------------------
  -- P lies in the mirror plane, hence is fixed.
  ----------------------------------------------------------------------

  · have hFix :
        planeReflect Geo pi P = P :=
      planeReflect_of_on_plane
        (Geo := Geo) pi P hPpi

    rw [hFix]

    by_cases hQP : Q = P

    · subst Q

      exact
        bookZero_nullSegment2 Geo P P

    · exact
        hilbert_space_congruent_reflexive
          (Geo := Geo)
          Q P hQP

  ----------------------------------------------------------------------
  -- P lies outside the mirror plane.
  ----------------------------------------------------------------------

  · rcases
        planeReflect_off_plane_data
          (Geo := Geo)
          pi P hPpi with
      ⟨F, hPerp, hMid⟩

    rcases hPerp with
      ⟨l, hPl, hLperp⟩

    have hInc :=
      HilbertLinePerpendicularPlaneAt.incidence
        (Geo := Geo) hLperp

    have hFl : H.OnLine F l :=
      hInc.1

    have hFpi : S.OnPlane F pi :=
      hInc.2

    --------------------------------------------------------------------
    -- If Q is the foot F, midpoint congruence is exactly the claim.
    --------------------------------------------------------------------

    by_cases hQF : Q = F

    · subst Q

      exact
        (Geometry.Geo.congruent_reverse_first
          Geo
          P F
          F (planeReflect Geo pi P)).mp
          hMid.2

    --------------------------------------------------------------------
    -- Otherwise m = FQ is a genuine line of the mirror plane.
    --------------------------------------------------------------------

    · have hFQ : Ne F Q :=
        Ne.symm hQF

      rcases
          HilbertPlaneIncidence.line_through
            (Geo := Geo)
            F Q hFQ with
        ⟨m, hFm, hQm⟩

      have hmpi :
          HilbertLineInPlane Geo m pi :=
        HilbertSpaceIncidence.line_in_plane
          (Geo := Geo)
          F Q hFQ
          m hFm hQm
          pi hFpi hQpi

      have hLmPerp :
          HilbertLinesPerpendicularAt
            Geo l m F :=
        HilbertLinePerpendicularPlaneAt.perpendicular_to_line
          (Geo := Geo)
          hLperp
          hmpi
          hFm

      ------------------------------------------------------------------
      -- Q cannot lie on the normal l: l meets pi only at F.
      ------------------------------------------------------------------

      have hQl : Not (H.OnLine Q l) := by
        intro hQl

        have hQF' : Q = F :=
          hilbert_XI12_perpendicular_foot_unique
            (Geo := Geo)
            pi l F Q
            hLperp
            hQl
            hQpi

        exact hQF hQF'

      ------------------------------------------------------------------
      -- sigma is the plane generated by l and Q.
      ------------------------------------------------------------------

      rcases
          hilbert_plane_through_line_and_external_point
            (Geo := Geo)
            l Q hQl with
        ⟨sigma, hlsigma, hQsigma, _hSigmaUnique⟩

      have hFsigma : S.OnPlane F sigma :=
        hlsigma F hFl

      have hPsigma : S.OnPlane P sigma :=
        hlsigma P hPl

      have hP'l :
          H.OnLine (planeReflect Geo pi P) l :=
        planeReflect_on_normal_line
          (Geo := Geo)
          pi P F l
          hPl hLperp hMid

      have hP'sigma :
          S.OnPlane (planeReflect Geo pi P) sigma :=
        hlsigma (planeReflect Geo pi P) hP'l

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        HilbertSpaceIncidence.line_in_plane
          (Geo := Geo)
          F Q hFQ
          m hFm hQm
          sigma hFsigma hQsigma

      ------------------------------------------------------------------
      -- Move the configuration into PlaneGeo sigma.
      ------------------------------------------------------------------

      let Pp : PlanePoint Geo sigma :=
        ⟨P, hPsigma⟩

      let Fp : PlanePoint Geo sigma :=
        ⟨F, hFsigma⟩

      let Qp : PlanePoint Geo sigma :=
        ⟨Q, hQsigma⟩

      let Pp' : PlanePoint Geo sigma :=
        ⟨planeReflect Geo pi P, hP'sigma⟩

      let lp : PlaneLine Geo sigma :=
        ⟨l, hlsigma⟩

      let mp : PlaneLine Geo sigma :=
        ⟨m, hmsigma⟩

      have hPF :
          Ne P F :=
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          P F (planeReflect Geo pi P)
          hMid.1).1

      have hPFp : Ne Pp Fp := by
        intro h
        exact hPF (congrArg Subtype.val h)

      have hQFp : Ne Qp Fp := by
        intro h
        apply hQF
        exact congrArg Subtype.val h

      have hFQp : Ne Fp Qp :=
        hQFp.symm

      have hPerpPlane :
          HilbertLinesPerpendicularAt
            (PlaneGeo Geo sigma) lp mp Fp :=
        (planeGeo_linesPerpendicularAt_iff_ambient
          (Geo := Geo)
          sigma lp mp Fp).mpr
          hLmPerp

      ------------------------------------------------------------------
      -- Normalize perpendicularity to the actual points P and Q.
      ------------------------------------------------------------------

      have hNorm :=
        hilbert_XI4_linesPerpendicularAt_right_angle_of_points
          (PlaneGeo Geo sigma)
          lp mp
          Fp Pp Qp
          (hilbert_linesPerpendicularAt_ne
            (PlaneGeo Geo sigma)
            lp mp Fp
            hPerpPlane)
          hPerpPlane
          hPFp
          hQFp
          hPl
          hQm

      have hPFQnon :
          Not
            (PrimCollinear
              (PlaneGeo Geo sigma)
              Pp Fp Qp) :=
        hNorm.1

      have hRightPFQ :
          HilbertRightAngle
            (PlaneGeo Geo sigma)
            Pp Fp Qp :=
        hNorm.2

      have hRightQFP :
          HilbertRightAngle
            (PlaneGeo Geo sigma)
            Qp Fp Pp :=
        coxeter_right_angle_swap
          (PlaneGeo Geo sigma)
          Pp Fp Qp
          hPFQnon
          hRightPFQ

      ------------------------------------------------------------------
      -- m = FQ is the reflection axis inside sigma.
      ------------------------------------------------------------------

      let axis : ReflectionAxis (PlaneGeo Geo sigma) :=
        { carrier := mp
          A := Fp
          B := Qp
          hAB := hFQp
          hA := hFm
          hB := hQm }

      have hPoffAxis :
          Not
            (HilbertIncidence.OnLine
              Pp axis.carrier) := by
        intro hPm

        have hPpi' : S.OnPlane P pi :=
          hmpi P hPm

        exact hPpi hPpi'

      have hPerpAxis :
          PerpendicularToAxis
            (PlaneGeo Geo sigma)
            axis Fp Pp := by

        exact
          ⟨hFm,
           hPoffAxis,
           ⟨Qp,
            hQm,
            hQFp,
            hRightQFP⟩⟩

      have hMidPlane :
          HilbertIsMidpoint
            (PlaneGeo Geo sigma)
            Fp Pp Pp' := by

        constructor

        · exact
            (planeGeo_between
              (Geo := Geo)
              sigma Pp Fp Pp').mpr
              hMid.1

        · exact
            (planeGeo_congruent
              (Geo := Geo)
              sigma Pp Fp Fp Pp').mpr
              hMid.2

      have hLineRef :
          IsLineReflection
            (PlaneGeo Geo sigma)
            axis Pp Pp' :=
        Or.inr
          ⟨hPoffAxis,
           ⟨Fp,
            hPerpAxis,
            hMidPlane⟩⟩

      have hQaxis :
          HilbertIncidence.OnLine
            Qp axis.carrier :=
        hQm

      have hPlaneCong :
          (PlaneGeo Geo sigma).Congruent
            Qp Pp Qp Pp' :=
        line_reflection_axis_point_equidistant
          (PlaneGeo Geo sigma)
          axis
          Pp Pp'
          Qp
          hQaxis
          hLineRef

      exact
        (planeGeo_congruent
          (Geo := Geo)
          sigma Qp Pp Qp Pp').mp
          hPlaneCong


/--
If the first endpoint lies in the mirror plane, plane reflection
preserves the segment.
-/
theorem planeReflect_preserves_congruence_left_on_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q : Geo.Point)
    (hPpi : S.OnPlane P pi) :
    Geo.Congruent
      P Q
      (planeReflect Geo pi P)
      (planeReflect Geo pi Q) := by

  have hFixP :
      planeReflect Geo pi P = P :=
    planeReflect_of_on_plane
      (Geo := Geo) pi P hPpi

  rw [hFixP]

  exact
    planeReflect_plane_point_equidistant
      (Geo := Geo)
      pi Q P hPpi


/--
If the second endpoint lies in the mirror plane, plane reflection
preserves the segment.
-/
theorem planeReflect_preserves_congruence_right_on_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q : Geo.Point)
    (hQpi : S.OnPlane Q pi) :
    Geo.Congruent
      P Q
      (planeReflect Geo pi P)
      (planeReflect Geo pi Q) := by

  have hFixQ :
      planeReflect Geo pi Q = Q :=
    planeReflect_of_on_plane
      (Geo := Geo) pi Q hQpi

  rw [hFixQ]

  have hQP :
      Geo.Congruent
        Q P
        Q (planeReflect Geo pi P) :=
    planeReflect_plane_point_equidistant
      (Geo := Geo)
      pi P Q hQpi

  have hPQ_QP' :
      Geo.Congruent
        P Q
        Q (planeReflect Geo pi P) :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      Q P
      Q (planeReflect Geo pi P)).mp
      hQP

  exact
    (Geometry.Geo.congruent_reverse_second
      Geo
      P Q
      Q (planeReflect Geo pi P)).mp
      hPQ_QP'


/--
Inside a plane slice sigma, if the carrier of a planar reflection axis
lies in the ambient mirror plane pi and P is reflected across pi through
a normal meeting that axis at F, then the ambient reflected point is
exactly the ordinary line reflection of P in the slice.
-/
theorem planeReflect_eq_lineReflect_in_slice
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi sigma : S.Plane)
    (axis : ReflectionAxis (PlaneGeo Geo sigma))
    (Pp Fp Rp Pp' : PlanePoint Geo sigma)
    (n : Geo.Line)
    (hPoff : Not (S.OnPlane Pp.1 pi))
    (hAxisPi :
      HilbertLineInPlane Geo axis.carrier.1 pi)
    (hFaxis :
      HilbertIncidence.OnLine Fp axis.carrier)
    (hRaxis :
      HilbertIncidence.OnLine Rp axis.carrier)
    (hRF : Ne Rp Fp)
    (hPn : H.OnLine Pp.1 n)
    (hNperp :
      HilbertLinePerpendicularPlaneAt
        Geo n pi Fp.1)
    (hMid :
      HilbertIsMidpoint Geo Fp.1 Pp.1 Pp'.1) :
    lineReflect (PlaneGeo Geo sigma) axis Pp = Pp' := by

  ----------------------------------------------------------------------
  -- P is off the slice reflection axis because the axis lies in pi.
  ----------------------------------------------------------------------

  have hPoffAxis :
      Not
        (HilbertIncidence.OnLine
          Pp axis.carrier) := by
    intro hPaxis

    have hPpi :
        S.OnPlane Pp.1 pi :=
      hAxisPi Pp.1 hPaxis

    exact hPoff hPpi

  ----------------------------------------------------------------------
  -- The normal n is perpendicular to the slice axis at F.
  ----------------------------------------------------------------------

  have hNperpAxis :
      HilbertLinesPerpendicularAt
        Geo n axis.carrier.1 Fp.1 :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hNperp
      hAxisPi
      hFaxis

  have hAxisPerpN :
      HilbertLinesPerpendicularAt
        Geo axis.carrier.1 n Fp.1 :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      n axis.carrier.1 Fp.1
      hNperpAxis

  ----------------------------------------------------------------------
  -- Normalize that perpendicularity to the selected axis point R
  -- and to the actual point P.
  ----------------------------------------------------------------------

  have hRFval :
      Ne Rp.1 Fp.1 := by
    intro h
    apply hRF
    exact Subtype.ext h

  have hPF :
      Ne Pp.1 Fp.1 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      Pp.1 Fp.1 Pp'.1
      hMid.1).1

  have hNorm :=
    hilbert_XI6_space_linesPerpendicularAt_right_angle_of_points
      (Geo := Geo)
      axis.carrier.1 n
      Fp.1 Rp.1 Pp.1
      hAxisPerpN
      hRFval
      hPF
      hRaxis
      hPn

  have hRightAmbient :
      HilbertRightAngle
        Geo Rp.1 Fp.1 Pp.1 :=
    hNorm.2

  have hRightPlane :
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        Rp Fp Pp :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma Rp Fp Pp).mpr
      hRightAmbient

  ----------------------------------------------------------------------
  -- Package P-F-P' as a line reflection in PlaneGeo(sigma).
  ----------------------------------------------------------------------

  have hPerpAxis :
      PerpendicularToAxis
        (PlaneGeo Geo sigma)
        axis Fp Pp :=
    ⟨hFaxis,
     hPoffAxis,
     ⟨Rp,
      hRaxis,
      hRF,
      hRightPlane⟩⟩

  have hMidPlane :
      HilbertIsMidpoint
        (PlaneGeo Geo sigma)
        Fp Pp Pp' := by
    constructor

    · exact
        (planeGeo_between
          (Geo := Geo)
          sigma Pp Fp Pp').mpr
          hMid.1

    · exact
        (planeGeo_congruent
          (Geo := Geo)
          sigma Pp Fp Fp Pp').mpr
          hMid.2

  have hRef :
      IsLineReflection
        (PlaneGeo Geo sigma)
        axis Pp Pp' :=
    Or.inr
      ⟨hPoffAxis,
       ⟨Fp,
        hPerpAxis,
        hMidPlane⟩⟩

  have hCanonical :
      IsLineReflection
        (PlaneGeo Geo sigma)
        axis
        Pp
        (lineReflect
          (PlaneGeo Geo sigma)
          axis Pp) :=
    lineReflect_spec
      (PlaneGeo Geo sigma)
      axis Pp

  have hUnique :
      Pp' =
        lineReflect
          (PlaneGeo Geo sigma)
          axis Pp :=
    line_reflection_unique
      (PlaneGeo Geo sigma)
      axis
      Pp
      Pp'
      (lineReflect
        (PlaneGeo Geo sigma)
        axis Pp)
      hRef
      hCanonical

  exact hUnique.symm


/--
If two off-plane points have distinct perpendicular feet F and G,
the two normal lines are coplanar by Euclid XI.6.  In that common plane
the restriction of the plane reflection is ordinary line reflection
in the line FG; therefore the segment PQ is preserved.
-/
theorem planeReflect_preserves_congruence_distinct_feet
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q F G : Geo.Point)
    (hPoff : Not (S.OnPlane P pi))
    (hQoff : Not (S.OnPlane Q pi))
    (hFG : Ne F G)
    (hPerpP :
      PerpendicularToPlaneThrough Geo pi F P)
    (hMidP :
      HilbertIsMidpoint
        Geo F P (planeReflect Geo pi P))
    (hPerpQ :
      PerpendicularToPlaneThrough Geo pi G Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo G Q (planeReflect Geo pi Q)) :
    Geo.Congruent
      P Q
      (planeReflect Geo pi P)
      (planeReflect Geo pi Q) := by

  rcases hPerpP with
    ⟨l, hPl, hLperp⟩

  rcases hPerpQ with
    ⟨m, hQm, hMperp⟩

  have hFpi :
      S.OnPlane F pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp).2

  have hGpi :
      S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hMperp).2

  have hFl :
      H.OnLine F l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp).1

  have hGm :
      H.OnLine G m :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hMperp).1

  ----------------------------------------------------------------------
  -- XI.6: the two distinct-foot normals are coplanar.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_6
        (Geo := Geo)
        pi l m F G
        hFG
        hLperp
        hMperp with
    ⟨sigma,
     hlsigma,
     hmsigma,
     _hDisjoint⟩

  have hFsigma :
      S.OnPlane F sigma :=
    hlsigma F hFl

  have hGsigma :
      S.OnPlane G sigma :=
    hmsigma G hGm

  have hPsigma :
      S.OnPlane P sigma :=
    hlsigma P hPl

  have hQsigma :
      S.OnPlane Q sigma :=
    hmsigma Q hQm

  have hP'l :
      H.OnLine (planeReflect Geo pi P) l :=
    planeReflect_on_normal_line
      (Geo := Geo)
      pi P F l
      hPl hLperp hMidP

  have hQ'm :
      H.OnLine (planeReflect Geo pi Q) m :=
    planeReflect_on_normal_line
      (Geo := Geo)
      pi Q G m
      hQm hMperp hMidQ

  have hP'sigma :
      S.OnPlane (planeReflect Geo pi P) sigma :=
    hlsigma (planeReflect Geo pi P) hP'l

  have hQ'sigma :
      S.OnPlane (planeReflect Geo pi Q) sigma :=
    hmsigma (planeReflect Geo pi Q) hQ'm

  ----------------------------------------------------------------------
  -- d = FG lies both in pi and in sigma.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        F G hFG with
    ⟨d, hFd, hGd⟩

  have hdpi :
      HilbertLineInPlane Geo d pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      F G hFG
      d hFd hGd
      pi hFpi hGpi

  have hdsigma :
      HilbertLineInPlane Geo d sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      F G hFG
      d hFd hGd
      sigma hFsigma hGsigma

  ----------------------------------------------------------------------
  -- PlaneGeo(sigma) data.
  ----------------------------------------------------------------------

  let Fp : PlanePoint Geo sigma :=
    ⟨F, hFsigma⟩

  let Gp : PlanePoint Geo sigma :=
    ⟨G, hGsigma⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hPsigma⟩

  let Qp : PlanePoint Geo sigma :=
    ⟨Q, hQsigma⟩

  let Pp' : PlanePoint Geo sigma :=
    ⟨planeReflect Geo pi P, hP'sigma⟩

  let Qp' : PlanePoint Geo sigma :=
    ⟨planeReflect Geo pi Q, hQ'sigma⟩

  let dp : PlaneLine Geo sigma :=
    ⟨d, hdsigma⟩

  have hFGp :
      Ne Fp Gp := by
    intro h
    apply hFG
    exact congrArg Subtype.val h

  let axis : ReflectionAxis (PlaneGeo Geo sigma) :=
    { carrier := dp
      A := Fp
      B := Gp
      hAB := hFGp
      hA := hFd
      hB := hGd }

  ----------------------------------------------------------------------
  -- Both ambient plane reflections are exactly the same planar line
  -- reflection in the common slice.
  ----------------------------------------------------------------------

  have hEqP :
      lineReflect
        (PlaneGeo Geo sigma)
        axis Pp = Pp' :=
    planeReflect_eq_lineReflect_in_slice
      (Geo := Geo)
      pi sigma axis
      Pp Fp Gp Pp'
      l
      hPoff
      hdpi
      hFd
      hGd
      hFGp.symm
      hPl
      hLperp
      hMidP

  have hEqQ :
      lineReflect
        (PlaneGeo Geo sigma)
        axis Qp = Qp' :=
    planeReflect_eq_lineReflect_in_slice
      (Geo := Geo)
      pi sigma axis
      Qp Gp Fp Qp'
      m
      hQoff
      hdpi
      hGd
      hFd
      hFGp
      hQm
      hMperp
      hMidQ

  have hCongPlane :
      (PlaneGeo Geo sigma).Congruent
        Pp Qp
        (lineReflect
          (PlaneGeo Geo sigma)
          axis Pp)
        (lineReflect
          (PlaneGeo Geo sigma)
          axis Qp) :=
    lineReflect_preserves_congruence
      (PlaneGeo Geo sigma)
      axis Pp Qp

  have hCongPlane' :
      (PlaneGeo Geo sigma).Congruent
        Pp Qp Pp' Qp' := by
    simpa only [hEqP, hEqQ] using hCongPlane

  exact
    (planeGeo_congruent
      (Geo := Geo)
      sigma Pp Qp Pp' Qp').mp
      hCongPlane'


/--
A plane contains a point distinct from any prescribed point of it.
-/
theorem plane_other_point_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (F : Geo.Point)
    (_hFpi : S.OnPlane F pi) :
    exists R : Geo.Point,
      Ne R F /\
      S.OnPlane R pi := by

  rcases
      hilbert_three_noncollinear_on_plane
        (Geo := Geo) pi with
    ⟨A, B, C,
     hApi, hBpi, _hCpi,
     hABC⟩

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  by_cases hAF : A = F

  · refine ⟨B, ?_, hBpi⟩
    intro hBF
    apply hAB
    exact hAF.trans hBF.symm

  · exact
      ⟨A, hAF, hApi⟩


/--
If two off-plane points have the same perpendicular foot F, XI.13
identifies their normal lines.  Choose any mirror-plane line through F;
the plane generated by that axis and the common normal is a slice in
which both ambient reflections are the same ordinary line reflection.
-/
theorem planeReflect_preserves_congruence_same_foot
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q F : Geo.Point)
    (hPoff : Not (S.OnPlane P pi))
    (hQoff : Not (S.OnPlane Q pi))
    (hPerpP :
      PerpendicularToPlaneThrough Geo pi F P)
    (hMidP :
      HilbertIsMidpoint
        Geo F P (planeReflect Geo pi P))
    (hPerpQ :
      PerpendicularToPlaneThrough Geo pi F Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo F Q (planeReflect Geo pi Q)) :
    Geo.Congruent
      P Q
      (planeReflect Geo pi P)
      (planeReflect Geo pi Q) := by

  rcases hPerpP with
    ⟨l, hPl, hLperp⟩

  rcases hPerpQ with
    ⟨m, hQm, hMperp⟩

  have hFpi :
      S.OnPlane F pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp).2

  have hFl :
      H.OnLine F l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp).1

  ----------------------------------------------------------------------
  -- XI.13: there is only one normal line through F.
  ----------------------------------------------------------------------

  have hlm :
      l = m :=
    euclid_proposition_11_13
      (Geo := Geo)
      pi l m F
      hLperp hMperp

  subst m

  ----------------------------------------------------------------------
  -- Choose R != F in pi.  Since l meets pi only in F, R is off l.
  ----------------------------------------------------------------------

  rcases
      plane_other_point_exists
        (Geo := Geo)
        pi F hFpi with
    ⟨R, hRF, hRpi⟩

  have hRl :
      Not (H.OnLine R l) := by
    intro hRl

    have hEq :
        R = F :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        pi l F R
        hLperp
        hRl
        hRpi

    exact hRF hEq

  ----------------------------------------------------------------------
  -- sigma is the plane generated by the common normal l and R.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l R hRl with
    ⟨sigma,
     hlsigma,
     hRsigma,
     _hSigmaUnique⟩

  have hFsigma :
      S.OnPlane F sigma :=
    hlsigma F hFl

  have hPsigma :
      S.OnPlane P sigma :=
    hlsigma P hPl

  have hQsigma :
      S.OnPlane Q sigma :=
    hlsigma Q hQm

  have hP'l :
      H.OnLine (planeReflect Geo pi P) l :=
    planeReflect_on_normal_line
      (Geo := Geo)
      pi P F l
      hPl hLperp hMidP

  have hQ'l :
      H.OnLine (planeReflect Geo pi Q) l :=
    planeReflect_on_normal_line
      (Geo := Geo)
      pi Q F l
      hQm hMperp hMidQ

  have hP'sigma :
      S.OnPlane (planeReflect Geo pi P) sigma :=
    hlsigma (planeReflect Geo pi P) hP'l

  have hQ'sigma :
      S.OnPlane (planeReflect Geo pi Q) sigma :=
    hlsigma (planeReflect Geo pi Q) hQ'l

  ----------------------------------------------------------------------
  -- d = FR is the mirror line inside sigma.
  ----------------------------------------------------------------------

  have hFR :
      Ne F R :=
    hRF.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        F R hFR with
    ⟨d, hFd, hRd⟩

  have hdpi :
      HilbertLineInPlane Geo d pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      F R hFR
      d hFd hRd
      pi hFpi hRpi

  have hdsigma :
      HilbertLineInPlane Geo d sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      F R hFR
      d hFd hRd
      sigma hFsigma hRsigma

  ----------------------------------------------------------------------
  -- PlaneGeo(sigma) data and one common reflection axis.
  ----------------------------------------------------------------------

  let Fp : PlanePoint Geo sigma :=
    ⟨F, hFsigma⟩

  let Rp : PlanePoint Geo sigma :=
    ⟨R, hRsigma⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hPsigma⟩

  let Qp : PlanePoint Geo sigma :=
    ⟨Q, hQsigma⟩

  let Pp' : PlanePoint Geo sigma :=
    ⟨planeReflect Geo pi P, hP'sigma⟩

  let Qp' : PlanePoint Geo sigma :=
    ⟨planeReflect Geo pi Q, hQ'sigma⟩

  let dp : PlaneLine Geo sigma :=
    ⟨d, hdsigma⟩

  have hFRp :
      Ne Fp Rp := by
    intro h
    apply hFR
    exact congrArg Subtype.val h

  let axis : ReflectionAxis (PlaneGeo Geo sigma) :=
    { carrier := dp
      A := Fp
      B := Rp
      hAB := hFRp
      hA := hFd
      hB := hRd }

  have hEqP :
      lineReflect
        (PlaneGeo Geo sigma)
        axis Pp = Pp' :=
    planeReflect_eq_lineReflect_in_slice
      (Geo := Geo)
      pi sigma axis
      Pp Fp Rp Pp'
      l
      hPoff
      hdpi
      hFd
      hRd
      hFRp.symm
      hPl
      hLperp
      hMidP

  have hEqQ :
      lineReflect
        (PlaneGeo Geo sigma)
        axis Qp = Qp' :=
    planeReflect_eq_lineReflect_in_slice
      (Geo := Geo)
      pi sigma axis
      Qp Fp Rp Qp'
      l
      hQoff
      hdpi
      hFd
      hRd
      hFRp.symm
      hQm
      hMperp
      hMidQ

  have hCongPlane :
      (PlaneGeo Geo sigma).Congruent
        Pp Qp
        (lineReflect
          (PlaneGeo Geo sigma)
          axis Pp)
        (lineReflect
          (PlaneGeo Geo sigma)
          axis Qp) :=
    lineReflect_preserves_congruence
      (PlaneGeo Geo sigma)
      axis Pp Qp

  have hCongPlane' :
      (PlaneGeo Geo sigma).Congruent
        Pp Qp Pp' Qp' := by
    simpa only [hEqP, hEqQ] using hCongPlane

  exact
    (planeGeo_congruent
      (Geo := Geo)
      sigma Pp Qp Pp' Qp').mp
      hCongPlane'


/--
Plane reflection preserves congruence for two points outside the mirror
plane.
-/
theorem planeReflect_preserves_congruence_off_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q : Geo.Point)
    (hPoff : Not (S.OnPlane P pi))
    (hQoff : Not (S.OnPlane Q pi)) :
    Geo.Congruent
      P Q
      (planeReflect Geo pi P)
      (planeReflect Geo pi Q) := by

  rcases
      planeReflect_off_plane_data
        (Geo := Geo)
        pi P hPoff with
    ⟨F, hPerpP, hMidP⟩

  rcases
      planeReflect_off_plane_data
        (Geo := Geo)
        pi Q hQoff with
    ⟨G, hPerpQ, hMidQ⟩

  by_cases hFG : F = G

  · subst G

    exact
      planeReflect_preserves_congruence_same_foot
        (Geo := Geo)
        pi P Q F
        hPoff hQoff
        hPerpP hMidP
        hPerpQ hMidQ

  · exact
      planeReflect_preserves_congruence_distinct_feet
        (Geo := Geo)
        pi P Q F G
        hPoff hQoff
        hFG
        hPerpP hMidP
        hPerpQ hMidQ


/--
Canonical plane reflection is an ambient synthetic isometry:
it preserves segment congruence for all point pairs.
-/
theorem planeReflect_preserves_congruence
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q : Geo.Point) :
    Geo.Congruent
      P Q
      (planeReflect Geo pi P)
      (planeReflect Geo pi Q) := by

  by_cases hPpi : S.OnPlane P pi

  · exact
      planeReflect_preserves_congruence_left_on_plane
        (Geo := Geo)
        pi P Q hPpi

  · by_cases hQpi : S.OnPlane Q pi

    · exact
        planeReflect_preserves_congruence_right_on_plane
          (Geo := Geo)
          pi P Q hQpi

    · exact
        planeReflect_preserves_congruence_off_plane
          (Geo := Geo)
          pi P Q hPpi hQpi

end Geometry

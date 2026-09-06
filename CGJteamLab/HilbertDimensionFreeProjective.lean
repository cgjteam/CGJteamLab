import CGJteamLab.HilbertDimensionFreeWyler

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Local projective geometry over a point

At an ambient point P:

* local points are ambient lines through P;
* local lines are ambient planes through P.

This module defines the local Veblen-Young P3 statement and proves that
Wyler I.7 / LP4, hence Smith I5, implies it.

No exchange principle is assumed.
-/

/--
Three ambient lines through P form a triangle in the local geometry at P.
-/
def WylerLocalTriangleAtPoint
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (P : Geo.Point)
    (r s t : Geo.Line) : Prop :=
  H.OnLine P r /\
  H.OnLine P s /\
  H.OnLine P t /\
  Ne r s /\
  Ne s t /\
  Ne t r /\
  Not (exists delta : S.Plane,
    HilbertLineInPlane Geo r delta /\
    HilbertLineInPlane Geo s delta /\
    HilbertLineInPlane Geo t delta)


/--
Veblen-Young P3 in the local geometry at P.

The side planes are alpha=(r,t), beta=(s,t), pi=(r,s).
A transversal plane epsilon meets alpha and beta in local points x,y
away from t.  The conclusion is a local point d on both epsilon and pi.
-/
def WylerLocalP3AtPoint
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall P : Geo.Point,
    forall r s t : Geo.Line,
      WylerLocalTriangleAtPoint Geo P r s t ->
      forall alpha beta pi : S.Plane,
        HilbertLineInPlane Geo r alpha ->
        HilbertLineInPlane Geo t alpha ->
        HilbertLineInPlane Geo s beta ->
        HilbertLineInPlane Geo t beta ->
        HilbertLineInPlane Geo r pi ->
        HilbertLineInPlane Geo s pi ->
        forall epsilon : S.Plane,
          forall x y : Geo.Line,
            H.OnLine P x ->
            H.OnLine P y ->
            HilbertLineInPlane Geo x alpha ->
            HilbertLineInPlane Geo x epsilon ->
            HilbertLineInPlane Geo y beta ->
            HilbertLineInPlane Geo y epsilon ->
            Ne x t ->
            Ne y t ->
            exists d : Geo.Line,
              H.OnLine P d /\
              HilbertLineInPlane Geo d pi /\
              HilbertLineInPlane Geo d epsilon


/--
On every line through P there is another point distinct from P.
-/
theorem smithCore_other_point_on_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (P : Geo.Point)
    (l : Geo.Line)
    (_hPl : H.OnLine P l) :
    exists Q : Geo.Point,
      Ne P Q /\
      H.OnLine Q l := by

  rcases
      C.two_points_on_each_line l with
    ⟨U, V, hUV, hUl, hVl⟩

  by_cases hPU : P = U

  · have hPV : Ne P V := by
      intro hPV
      apply hUV
      exact hPU.symm.trans hPV

    exact ⟨V, hPV, hVl⟩

  · exact ⟨U, hPU, hUl⟩


/--
Wyler I.7 / LP4 implies the local Veblen-Young P3 statement at every point.
-/
theorem wylerI7IntersectionLine_implies_localP3
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hI7 : WylerI7IntersectionLine Geo) :
    WylerLocalP3AtPoint Geo := by

  intro P r s t hTriangle alpha beta pi hrAlpha htAlpha hsBeta htBeta hrPi hsPi epsilon x y hPx hPy hxAlpha hxEpsilon hyBeta hyEpsilon hxt hyt

  rcases hTriangle with
    ⟨hPr, hPs, hPt, hrs, hst, htr, hNoPlane⟩

  have hPAlpha : S.OnPlane P alpha :=
    hrAlpha P hPr

  have hPBeta : S.OnPlane P beta :=
    hsBeta P hPs

  have hPPi : S.OnPlane P pi :=
    hrPi P hPr

  have hPEpsilon : S.OnPlane P epsilon :=
    hxEpsilon P hPx

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P t hPt with
    ⟨T, hPT, hTt⟩

  have hTAlpha : S.OnPlane T alpha :=
    htAlpha T hTt

  have hTBeta : S.OnPlane T beta :=
    htBeta T hTt

  have hTOutPi : Not (S.OnPlane T pi) := by
    intro hTPi

    have htPi : HilbertLineInPlane Geo t pi :=
      C.line_in_plane
        P T hPT
        t hPt hTt
        pi hPPi hTPi

    exact
      hNoPlane
        ⟨pi,
         hrPi,
         hsPi,
         htPi⟩

  rcases
      hI7
        pi
        r s hrs
        hrPi hsPi
        T hTOutPi
        alpha beta
        hrAlpha hTAlpha
        hsBeta hTBeta with
    ⟨kab, hTkab, hkabAlpha, hkabBeta, hkabIff⟩

  have hPkAB : H.OnLine P kab :=
    (hkabIff P).mp
      ⟨hPAlpha, hPBeta⟩

  have htKab : t = kab :=
    HilbertPlaneIncidence.line_unique
      P T hPT
      t kab
      hPt hTt
      hPkAB hTkab

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P r hPr with
    ⟨R, hPR, hRr⟩

  have hRAlpha : S.OnPlane R alpha :=
    hrAlpha R hRr

  have hROutBeta : Not (S.OnPlane R beta) := by
    intro hRBeta

    have hRkab : H.OnLine R kab :=
      (hkabIff R).mp
        ⟨hRAlpha, hRBeta⟩

    have hrKab : r = kab :=
      HilbertPlaneIncidence.line_unique
        P R hPR
        r kab
        hPr hRr
        hPkAB hRkab

    apply htr

    calc
      t = kab := htKab
      _ = r := hrKab.symm

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P y hPy with
    ⟨Y, hPY, hYy⟩

  have hYBeta : S.OnPlane Y beta :=
    hyBeta Y hYy

  have hYEpsilon : S.OnPlane Y epsilon :=
    hyEpsilon Y hYy

  have hYOutAlpha : Not (S.OnPlane Y alpha) := by
    intro hYAlpha

    have hYkab : H.OnLine Y kab :=
      (hkabIff Y).mp
        ⟨hYAlpha, hYBeta⟩

    have hyKab : y = kab :=
      HilbertPlaneIncidence.line_unique
        P Y hPY
        y kab
        hPy hYy
        hPkAB hYkab

    apply hyt

    calc
      y = kab := hyKab
      _ = t := htKab.symm

  have hRT : Ne R T := by
    intro hRTEq
    subst T

    have hrt : r = t :=
      HilbertPlaneIncidence.line_unique
        P R hPR
        r t
        hPr hRr
        hPt hTt

    exact htr hrt.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        R T hRT with
    ⟨u, hRu, hTu⟩

  have huAlpha : HilbertLineInPlane Geo u alpha :=
    C.line_in_plane
      R T hRT
      u hRu hTu
      alpha
      hRAlpha hTAlpha

  have hRTY :
      Not (PrimCollinear Geo R T Y) := by
    intro hCol

    have hYu : H.OnLine Y u :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        R T Y hRT
        u hRu hTu
        hCol

    exact hYOutAlpha (huAlpha Y hYu)

  rcases
      C.plane_through
        R T Y hRTY with
    ⟨delta, hRDelta, hTDelta, hYDelta⟩

  have huDelta : HilbertLineInPlane Geo u delta :=
    C.line_in_plane
      R T hRT
      u hRu hTu
      delta
      hRDelta hTDelta

  have hTY : Ne T Y := by
    intro hTYEq
    subst Y
    exact hYOutAlpha hTAlpha

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        T Y hTY with
    ⟨v, hTv, hYv⟩

  have hvBeta : HilbertLineInPlane Geo v beta :=
    C.line_in_plane
      T Y hTY
      v hTv hYv
      beta
      hTBeta hYBeta

  have hvDelta : HilbertLineInPlane Geo v delta :=
    C.line_in_plane
      T Y hTY
      v hTv hYv
      delta
      hTDelta hYDelta

  have hux : Ne u x := by
    intro huxEq

    have hTx : H.OnLine T x := by
      rw [← huxEq]
      exact hTu

    have hxtEq : x = t :=
      HilbertPlaneIncidence.line_unique
        P T hPT
        x t
        hPx hTx
        hPt hTt

    exact hxt hxtEq

  rcases
      hI7
        alpha
        u x hux
        huAlpha hxAlpha
        Y hYOutAlpha
        delta epsilon
        huDelta hYDelta
        hxEpsilon hYEpsilon with
    ⟨le, hYle, hleDelta, hleEpsilon, _hleIff⟩

  have hvs : Ne v s := by
    intro hvsEq

    have hTs : H.OnLine T s := by
      rw [← hvsEq]
      exact hTv

    have hstEq : s = t :=
      HilbertPlaneIncidence.line_unique
        P T hPT
        s t
        hPs hTs
        hPt hTt

    exact hst hstEq

  have hRPi : S.OnPlane R pi :=
    hrPi R hRr

  rcases
      hI7
        beta
        v s hvs
        hvBeta hsBeta
        R hROutBeta
        delta pi
        hvDelta hRDelta
        hsPi hRPi with
    ⟨lp, hRlp, hlpDelta, hlpPi, _hlpIff⟩

  have hPRT :
      Not (PrimCollinear Geo P R T) := by
    intro hCol

    have hTOnR : H.OnLine T r :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        P R T hPR
        r hPr hRr
        hCol

    have hrt : r = t :=
      HilbertPlaneIncidence.line_unique
        P T hPT
        r t
        hPr hTOnR
        hPt hTt

    exact htr hrt.symm

  have hPOutDelta : Not (S.OnPlane P delta) := by
    intro hPDelta

    have hAlphaDelta : alpha = delta :=
      C.plane_unique
        P R T hPRT
        alpha delta
        hPAlpha hRAlpha hTAlpha
        hPDelta hRDelta hTDelta

    apply hYOutAlpha

    rw [hAlphaDelta]

    exact hYDelta

  by_cases hTrace : le = lp

  · have hYPi : S.OnPlane Y pi := by
      exact
        hlpPi Y
          (by
            rw [← hTrace]
            exact hYle)

    have hyPi : HilbertLineInPlane Geo y pi :=
      C.line_in_plane
        P Y hPY
        y hPy hYy
        pi
        hPPi hYPi

    exact
      ⟨y,
       hPy,
       hyPi,
       hyEpsilon⟩

  · rcases
        hI7
          delta
          le lp hTrace
          hleDelta hlpDelta
          P hPOutDelta
          epsilon pi
          hleEpsilon hPEpsilon
          hlpPi hPPi with
      ⟨d, hPd, hdEpsilon, hdPi, _hdIff⟩

    exact
      ⟨d,
       hPd,
       hdPi,
       hdEpsilon⟩


/--
Smith I5 implies the local Veblen-Young P3 statement.
-/
theorem smithI5_implies_localP3
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hI5 : SmithI5Statement Geo) :
    WylerLocalP3AtPoint Geo := by

  have hI7 :
      WylerI7IntersectionLine Geo :=
    (wylerI7IntersectionLine_iff_smithI5
      (Geo := Geo)).2 hI5

  exact
    wylerI7IntersectionLine_implies_localP3
      (Geo := Geo)
      hI7

end Geometry

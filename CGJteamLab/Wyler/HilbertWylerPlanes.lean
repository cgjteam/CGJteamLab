import CGJteamLab.Wyler.HilbertWylerEuclidean
import CGJteamLab.Proposition17
import CGJteamLab.HilbertRightAngle

/-!
# Hilbert-Wyler plane-normal core

Reusable metric plane-normal machinery extracted from Euclid XI.14.

This module imports no numbered Book XI proposition.  The original XI.14
proof engine is retained, but its single direct dependency on XI.5 is
redirected to the lower Wyler parallel core.

Main endpoints:

* `euclid_proposition_11_14_normalized_wyler`
* `hilbert_XI14_plane_perpendicular_to_line_at_unique_wyler`

The final public Euclid XI.14 wrapper remains outside this lower layer.
-/

namespace Geometry

universe u

/-!
# Euclid XI.14

Planes to which the same straight line is at right angles are parallel.

The development is neutral: it uses spatial incidence/order/congruence,
Euclid XI.5, and the planar consequence I.17.  No Euclidean parallel
axiom is used.

The explicit distinct-plane hypothesis in the public theorem separates
the nontrivial XI.Def.8 case.  The equal-foot case is handled internally
by uniqueness of the plane perpendicular to a fixed line at a fixed
point.
-/

variable (Geo : Geometry.Geo)


/--
Two ambient planes are parallel when they have no common point.

This is the direct formal counterpart of Euclid XI.Def.8 and belongs to
the general 3D plane API rather than to Proposition XI.14 itself.
-/
def HilbertSpacePlanesParallel
    [S : HilbertSpacePrimitive Geo]
    (pi rho : S.Plane) : Prop :=
  Not
    (exists X : Geo.Point,
      S.OnPlane X pi /\
      S.OnPlane X rho)



theorem hilbert_XI14_common_point_off_normal_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B K : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B)
    (hKpi : S.OnPlane K pi)
    (hKrho : S.OnPlane K rho) :
    Not (H.OnLine K l) := by

  intro hKl

  have hKA : K = A :=
    hilbertLinePerpendicularPlaneAt_foot_unique_wyler
      (Geo := Geo)
      pi l A K
      hPerpPi
      hKl
      hKpi

  have hKB : K = B :=
    hilbertLinePerpendicularPlaneAt_foot_unique_wyler
      (Geo := Geo)
      rho l B K
      hPerpRho
      hKl
      hKrho

  apply hAB
  exact hKA.symm.trans hKB


/--
XI.14 normalized helper, step 2.

A common point `K` of the two planes, together with the common
normal line `l`, determines a plane `sigma`. Since `A` and `B`
lie on `l`, the points `A`, `B`, and `K` all lie in `sigma`.
-/
theorem hilbert_XI14_common_point_normal_plane_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B K : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B)
    (hKpi : S.OnPlane K pi)
    (hKrho : S.OnPlane K rho) :
    exists sigma : S.Plane,
      HilbertLineInPlane Geo l sigma /\
      S.OnPlane A sigma /\
      S.OnPlane B sigma /\
      S.OnPlane K sigma := by

  have hKl : Not (H.OnLine K l) :=
    hilbert_XI14_common_point_off_normal_wyler
      (Geo := Geo)
      pi rho l A B K
      hAB
      hPerpPi
      hPerpRho
      hKpi
      hKrho

  have hSigma :=
    hilbert_plane_through_line_and_external_point
      (Geo := Geo)
      l K hKl

  cases hSigma with
  | intro sigma hData =>
      have hlsigma : HilbertLineInPlane Geo l sigma :=
        hData.1

      have hKsigma : S.OnPlane K sigma :=
        hData.2.1

      have hIncPi :=
        HilbertLinePerpendicularPlaneAt.incidence
          (Geo := Geo) hPerpPi

      have hIncRho :=
        HilbertLinePerpendicularPlaneAt.incidence
          (Geo := Geo) hPerpRho

      have hAl : H.OnLine A l :=
        hIncPi.1

      have hBl : H.OnLine B l :=
        hIncRho.1

      have hAsigma : S.OnPlane A sigma :=
        hlsigma A hAl

      have hBsigma : S.OnPlane B sigma :=
        hlsigma B hBl

      exact
        Exists.intro sigma
          (And.intro hlsigma
            (And.intro hAsigma
              (And.intro hBsigma hKsigma)))


variable (Geo : Geometry.Geo)

/--
XI.14 normalized helper, step 3.

Under the hypothetical assumption that the two planes have a common
point `K`, construct the plane `sigma` through the common normal `l`
and `K`, together with the two connector lines `aK` and `bK`.

The line `aK` lies in both `pi` and `sigma`.
The line `bK` lies in both `rho` and `sigma`.

Because `l` is perpendicular to `pi` at `A`, it is perpendicular to
`aK` at `A`. Likewise, because `l` is perpendicular to `rho` at `B`,
it is perpendicular to `bK` at `B`.
-/
theorem hilbert_XI14_connector_configuration_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B K : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B)
    (hKpi : S.OnPlane K pi)
    (hKrho : S.OnPlane K rho) :
    exists sigma : S.Plane,
    exists aK bK : Geo.Line,
      HilbertLineInPlane Geo l sigma /\
      HilbertLineInPlane Geo aK pi /\
      HilbertLineInPlane Geo aK sigma /\
      HilbertLineInPlane Geo bK rho /\
      HilbertLineInPlane Geo bK sigma /\
      H.OnLine A aK /\
      H.OnLine K aK /\
      H.OnLine B bK /\
      H.OnLine K bK /\
      HilbertLinesPerpendicularAt Geo l aK A /\
      HilbertLinesPerpendicularAt Geo l bK B := by

  rcases
      hilbert_XI14_common_point_normal_plane_wyler
        (Geo := Geo)
        pi rho l A B K
        hAB
        hPerpPi
        hPerpRho
        hKpi
        hKrho
    with
    ⟨sigma, hlsigma, hAsigma, hBsigma, hKsigma⟩

  have hKl : Not (H.OnLine K l) :=
    hilbert_XI14_common_point_off_normal_wyler
      (Geo := Geo)
      pi rho l A B K
      hAB
      hPerpPi
      hPerpRho
      hKpi
      hKrho

  have hIncPi :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerpPi

  have hIncRho :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerpRho

  have hAl : H.OnLine A l :=
    hIncPi.1

  have hBl : H.OnLine B l :=
    hIncRho.1

  have hApi : S.OnPlane A pi :=
    hIncPi.2

  have hBrho : S.OnPlane B rho :=
    hIncRho.2

  have hAK : Ne A K := by
    intro h
    apply hKl
    rw [← h]
    exact hAl

  have hBK : Ne B K := by
    intro h
    apply hKl
    rw [← h]
    exact hBl

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A K hAK
    with
    ⟨aK, hAaK, hKaK⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        B K hBK
    with
    ⟨bK, hBbK, hKbK⟩

  have haKpi : HilbertLineInPlane Geo aK pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A K hAK
      aK hAaK hKaK
      pi hApi hKpi

  have haKsigma : HilbertLineInPlane Geo aK sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A K hAK
      aK hAaK hKaK
      sigma hAsigma hKsigma

  have hbKrho : HilbertLineInPlane Geo bK rho :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B K hBK
      bK hBbK hKbK
      rho hBrho hKrho

  have hbKsigma : HilbertLineInPlane Geo bK sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B K hBK
      bK hBbK hKbK
      sigma hBsigma hKsigma

  have hPerpAK :
      HilbertLinesPerpendicularAt Geo l aK A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerpPi
      haKpi
      hAaK

  have hPerpBK :
      HilbertLinesPerpendicularAt Geo l bK B :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerpRho
      hbKrho
      hBbK

  exact
    ⟨sigma, aK, bK,
     hlsigma,
     haKpi,
     haKsigma,
     hbKrho,
     hbKsigma,
     hAaK,
     hKaK,
     hBbK,
     hKbK,
     hPerpAK,
     hPerpBK⟩


variable (Geo : Geometry.Geo)

/--
XI.14 normalized helper, step 4.

The hypothetical common-point configuration from step 3 is converted
to the induced plane geometry `PlaneGeo Geo sigma`.

The points A, B, K form a nondegenerate triangle in sigma:
A and B lie on the common normal l, while K does not lie on l.

The two ambient perpendicularities are then transported to PlaneGeo:
  l perp aK at A
  l perp bK at B.
-/
theorem hilbert_XI14_planeGeo_triangle_configuration_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B K : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B)
    (hKpi : S.OnPlane K pi)
    (hKrho : S.OnPlane K rho) :
    exists sigma : S.Plane,
    exists lp aKp bKp : PlaneLine Geo sigma,
    exists Ap Bp Kp : PlanePoint Geo sigma,
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Kp) /\
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma)
        lp aKp Ap /\
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma)
        lp bKp Bp /\
      H.OnLine Kp.1 aKp.1 /\
      H.OnLine Kp.1 bKp.1 := by

  rcases
      hilbert_XI14_connector_configuration_wyler
        (Geo := Geo)
        pi rho l A B K
        hAB
        hPerpPi
        hPerpRho
        hKpi
        hKrho
    with
    ⟨sigma, aK, bK,
     hlsigma,
     _haKpi,
     haKsigma,
     _hbKrho,
     hbKsigma,
     hAaK,
     hKaK,
     hBbK,
     hKbK,
     hPerpAK,
     hPerpBK⟩

  have hIncPi :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerpPi

  have hIncRho :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerpRho

  have hAl : H.OnLine A l :=
    hIncPi.1

  have hBl : H.OnLine B l :=
    hIncRho.1

  have hAsigma : S.OnPlane A sigma :=
    hlsigma A hAl

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hKsigma : S.OnPlane K sigma :=
    haKsigma K hKaK

  let lp : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  let aKp : PlaneLine Geo sigma :=
    ⟨aK, haKsigma⟩

  let bKp : PlaneLine Geo sigma :=
    ⟨bK, hbKsigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Kp : PlanePoint Geo sigma :=
    ⟨K, hKsigma⟩

  have hKl : Not (H.OnLine K l) :=
    hilbert_XI14_common_point_off_normal_wyler
      (Geo := Geo)
      pi rho l A B K
      hAB
      hPerpPi
      hPerpRho
      hKpi
      hKrho

  have hNonAmbient :
      Not (PrimCollinear Geo A B K) := by
    intro hCol

    have hKl' : H.OnLine K l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAB
        hAl
        hBl
        hCol

    exact hKl hKl'

  have hNonPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Kp) := by
    intro hColPlane

    have hColAmbient :
        PrimCollinear Geo A B K :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma
        Ap Bp Kp
        hColPlane

    exact hNonAmbient hColAmbient

  have hPerpAKPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma)
        lp aKp Ap := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        sigma
        lp aKp Ap).mpr
    simpa [lp, aKp, Ap] using hPerpAK

  have hPerpBKPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma)
        lp bKp Bp := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        sigma
        lp bKp Bp).mpr
    simpa [lp, bKp, Bp] using hPerpBK

  exact
    ⟨sigma,
     lp, aKp, bKp,
     Ap, Bp, Kp,
     hNonPlane,
     hPerpAKPlane,
     hPerpBKPlane,
     hKaK,
     hKbK⟩


variable (Geo : Geometry.Geo)

/--
XI.14 normalized helper, step 5.

Unpack the two perpendicularities in the plane sigma.

At A we obtain witnesses U,V such that:
  U lies on l,
  V lies on AK,
  angle UAV is right.

At B we obtain witnesses U',V' such that:
  U' lies on l,
  V' lies on BK,
  angle U'BV' is right.

The collinearities with the triangle sides are recorded explicitly.
-/
theorem hilbert_XI14_unpack_right_angle_witnesses_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B K : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B)
    (hKpi : S.OnPlane K pi)
    (hKrho : S.OnPlane K rho) :
    exists sigma : S.Plane,
    exists Ap Bp Kp : PlanePoint Geo sigma,
    exists U V U' V' : PlanePoint Geo sigma,
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Kp) /\
      PrimCollinear
        (PlaneGeo Geo sigma)
        U Ap Bp /\
      PrimCollinear
        (PlaneGeo Geo sigma)
        V Ap Kp /\
      PrimCollinear
        (PlaneGeo Geo sigma)
        U' Bp Ap /\
      PrimCollinear
        (PlaneGeo Geo sigma)
        V' Bp Kp /\
      Ne U Ap /\
      Ne V Ap /\
      Ne U' Bp /\
      Ne V' Bp /\
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        U Ap V /\
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        U' Bp V' := by

  rcases
      hilbert_XI14_planeGeo_triangle_configuration_wyler
        (Geo := Geo)
        pi rho l A B K
        hAB
        hPerpPi
        hPerpRho
        hKpi
        hKrho
    with
    ⟨sigma,
     lp, aKp, bKp,
     Ap, Bp, Kp,
     hNon,
     hPerpA,
     hPerpB,
     hKaK,
     hKbK⟩

  rcases hPerpA with
    ⟨hAl,
     hAaK,
     U, V,
     hUA,
     hVA,
     hUl,
     hVaK,
     _hUAVnon,
     hRightA⟩

  rcases hPerpB with
    ⟨hBl,
     hBbK,
     U', V',
     hU'B,
     hV'B,
     hU'l,
     hV'bK,
     _hU'BV'non,
     hRightB⟩

  have hUAB :
      PrimCollinear
        (PlaneGeo Geo sigma)
        U Ap Bp :=
    ⟨lp, hUl, hAl, hBl⟩

  have hVAK :
      PrimCollinear
        (PlaneGeo Geo sigma)
        V Ap Kp :=
    ⟨aKp, hVaK, hAaK, hKaK⟩

  have hU'BA :
      PrimCollinear
        (PlaneGeo Geo sigma)
        U' Bp Ap :=
    ⟨lp, hU'l, hBl, hAl⟩

  have hV'BK :
      PrimCollinear
        (PlaneGeo Geo sigma)
        V' Bp Kp :=
    ⟨bKp, hV'bK, hBbK, hKbK⟩

  exact
    ⟨sigma,
     Ap, Bp, Kp,
     U, V, U', V',
     hNon,
     hUAB,
     hVAK,
     hU'BA,
     hV'BK,
     hUA,
     hVA,
     hU'B,
     hV'B,
     hRightA,
     hRightB⟩


/--
For three collinear points X,O,Y, with X and Y distinct from O,
the points X and Y are either on the same ray from O or O lies
between X and Y.

The case X = Y belongs to the same-ray alternative.
-/
theorem hilbert_XI14_collinear_arm_orientation_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertOrder G]
    (O X Y : G.Point)
    (hXO : Ne X O)
    (hYO : Ne Y O)
    (hCol : PrimCollinear G X O Y) :
    HilbertSameRay G O X Y \/
    G.Between X O Y := by

  by_cases hXY : X = Y

  · subst Y
    left
    exact
      hilbert_sameRay_refl
        G O X hXO

  · have hOY : Ne O Y :=
      hYO.symm

    rcases
        hilbert_between_trichotomy
          G
          X O Y
          hXO
          hOY
          hXY
          hCol
      with
      hXOY | hOXY | hXYO

    · exact Or.inr hXOY

    · left
      exact
        hilbert_sameRay_of_between
          G O X Y hOXY

    · have hOYX : G.Between O Y X :=
        (HilbertOrder.between_incidence
          X Y O hXYO).2.2.2.2

      have hRayYX :
          HilbertSameRay G O Y X :=
        hilbert_sameRay_of_between
          G O Y X hOYX

      left
      exact
        hilbert_sameRay_symm
          G O Y X hRayYX


/--
A right angle is unchanged when both of its arms are replaced by
points on the same respective rays.

This is a purely planar Hilbert lemma.  The supplement point in the
definition of the original right angle is retained.  Betweenness with
that supplement is transported along the first ray, while both angle
arms are transported by equality of rays.
-/
theorem hilbert_XI14_rightAngle_transport_sameRays_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertCongruence G]
    (U O V X Y : G.Point)
    (hRight : HilbertRightAngle G U O V)
    (hUX : HilbertSameRay G O U X)
    (hVY : HilbertSameRay G O V Y) :
    HilbertRightAngle G X O Y := by

  rcases hRight with
    ⟨C, hUOC, hAngle⟩

  have hCO : Ne C O :=
    (HilbertOrder.between_incidence
      U O C hUOC).2.1.symm

  have hCC :
      HilbertSameRay G O C C :=
    hilbert_sameRay_refl
      G O C hCO

  have hXOC : G.Between X O C :=
    hilbert_between_transport_sameRays
      G U O C X C
      hUOC
      hUX
      hCC

  have hLeftFirst :
      G.Angle U O V =
      G.Angle X O V :=
    hilbert_angle_eq_of_sameRay_first
      G O U X V hUX

  have hLeftSecond :
      G.Angle X O V =
      G.Angle X O Y :=
    hilbert_angle_eq_of_sameRay_second
      G O X V Y hVY

  have hRightFirst :
      G.Angle V O C =
      G.Angle Y O C :=
    hilbert_angle_eq_of_sameRay_first
      G O V Y C hVY

  have hAngle' :
      G.AngleCongruent X O Y Y O C := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢
    rw [← hLeftSecond, ← hLeftFirst, ← hRightFirst]
    exact hAngle

  exact
    ⟨C,
     hXOC,
     hAngle'⟩


/--
A right angle remains right when its first arm is replaced by a point
on the opposite ray.

If U-O-X and angle UOV is right, then angle XOV is right.
-/
theorem hilbert_XI14_rightAngle_transport_opposite_first_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertCongruence G]
    (U O V X : G.Point)
    (hUOX : G.Between U O X)
    (hNon : Not (PrimCollinear G U O V))
    (hRight : HilbertRightAngle G U O V) :
    HilbertRightAngle G X O V := by

  have hChosen :
      G.AngleCongruent U O V V O X :=
    hilbert_right_angle_chosen_supplement
      G
      V O U X
      hUOX
      hNon
      hRight

  have hSymm :
      G.AngleCongruent V O X U O V :=
    G.angle_congruent_symmetry
      U O V
      V O X
      hChosen

  have hReverseFirst :
      G.AngleCongruent X O V U O V :=
    (G.angle_congruent_reverse_first
      V O X
      U O V).mp
      hSymm

  have hTarget :
      G.AngleCongruent X O V V O U :=
    (G.angle_congruent_reverse_second
      X O V
      U O V).mp
      hReverseFirst

  have hXOU : G.Between X O U :=
    (HilbertOrder.between_incidence
      U O X hUOX).2.2.2.2

  exact
    ⟨U,
     hXOU,
     hTarget⟩


/--
A right angle remains right when its second arm is replaced by a point
on the opposite ray.

If V-O-Y and angle UOV is right, then angle UOY is right.

The proof uses the two pairs of vertical angles determined by the
opposite rays U/O/C and V/O/Y.
-/
theorem hilbert_XI14_rightAngle_transport_opposite_second_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertCongruence G]
    (U O V Y : G.Point)
    (hVOY : G.Between V O Y)
    (hNon : Not (PrimCollinear G U O V))
    (hRight : HilbertRightAngle G U O V) :
    HilbertRightAngle G U O Y := by

  rcases hRight with
    ⟨C, hUOC, hAngle⟩

  have hYOV : G.Between Y O V :=
    (HilbertOrder.between_incidence
      V O Y hVOY).2.2.2.2

  have hOY : Ne O Y :=
    (HilbertOrder.between_incidence
      V O Y hVOY).2.1

  have hNonUOY :
      Not (PrimCollinear G U O Y) := by
    intro hUOY

    have hVOYcol :
        PrimCollinear G V O Y :=
      (HilbertOrder.between_incidence
        V O Y hVOY).2.2.2.1

    have hOYV :
        PrimCollinear G O Y V :=
      PrimCollinearCycle
        G V O Y hVOYcol

    have hUOV :
        PrimCollinear G U O V :=
      hilbert_primCollinear_trans
        G
        U O Y V
        hOY
        hUOY
        hOYV

    exact hNon hUOV

  have hVertical1 :
      G.AngleCongruent U O Y C O V :=
    VerticalAngles
      G
      U O Y C V
      hUOC
      hYOV
      hNonUOY

  have hVertical1' :
      G.AngleCongruent U O Y V O C :=
    (G.angle_congruent_reverse_second
      U O Y
      C O V).mp
      hVertical1

  have hVertical2 :
      G.AngleCongruent U O V C O Y :=
    VerticalAngles
      G
      U O V C Y
      hUOC
      hVOY
      hNon

  have hVertical2' :
      G.AngleCongruent U O V Y O C :=
    (G.angle_congruent_reverse_second
      U O V
      C O Y).mp
      hVertical2

  have hAngleSymm :
      G.AngleCongruent V O C U O V :=
    G.angle_congruent_symmetry
      U O V
      V O C
      hAngle

  have hStep :
      G.AngleCongruent U O Y U O V :=
    G.angle_congruent_transitivity
      U O Y
      V O C
      U O V
      hVertical1'
      hAngleSymm

  have hTarget :
      G.AngleCongruent U O Y Y O C :=
    G.angle_congruent_transitivity
      U O Y
      U O V
      Y O C
      hStep
      hVertical2'

  exact
    ⟨C,
     hUOC,
     hTarget⟩


/--
General transport of a right angle along the two carrier lines.

Each new arm may lie either on the same ray as the original witness
or on the opposite ray through the vertex.

The one intermediate noncollinearity hypothesis is needed only when
both arms are reversed.
-/
theorem hilbert_XI14_rightAngle_transport_by_orientations_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertCongruence G]
    (U O V X Y : G.Point)
    (hRight : HilbertRightAngle G U O V)
    (hNonUV : Not (PrimCollinear G U O V))
    (hNonXV : Not (PrimCollinear G X O V))
    (hUX :
      HilbertSameRay G O U X \/
      G.Between U O X)
    (hVY :
      HilbertSameRay G O V Y \/
      G.Between V O Y) :
    HilbertRightAngle G X O Y := by

  rcases hUX with hUXsame | hUXopp

  · rcases hVY with hVYsame | hVYopp

    · exact
        hilbert_XI14_rightAngle_transport_sameRays_wyler
          G
          U O V X Y
          hRight
          hUXsame
          hVYsame

    · have hRightUY :
          HilbertRightAngle G U O Y :=
        hilbert_XI14_rightAngle_transport_opposite_second_wyler
          G
          U O V Y
          hVYopp
          hNonUV
          hRight

      have hYY :
          HilbertSameRay G O Y Y :=
        hilbert_sameRay_refl
          G O Y
          (HilbertOrder.between_incidence
            V O Y hVYopp).2.1.symm

      exact
        hilbert_XI14_rightAngle_transport_sameRays_wyler
          G
          U O Y X Y
          hRightUY
          hUXsame
          hYY

  · rcases hVY with hVYsame | hVYopp

    · have hRightXV :
          HilbertRightAngle G X O V :=
        hilbert_XI14_rightAngle_transport_opposite_first_wyler
          G
          U O V X
          hUXopp
          hNonUV
          hRight

      have hXX :
          HilbertSameRay G O X X :=
        hilbert_sameRay_refl
          G O X
          (HilbertOrder.between_incidence
            U O X hUXopp).2.1.symm

      exact
        hilbert_XI14_rightAngle_transport_sameRays_wyler
          G
          X O V X Y
          hRightXV
          hXX
          hVYsame

    · have hRightXV :
          HilbertRightAngle G X O V :=
        hilbert_XI14_rightAngle_transport_opposite_first_wyler
          G
          U O V X
          hUXopp
          hNonUV
          hRight

      exact
        hilbert_XI14_rightAngle_transport_opposite_second_wyler
          G
          X O V Y
          hVYopp
          hNonXV
          hRightXV


variable (Geo : Geometry.Geo)

/--
XI.14 normalized helper, step 12.

In the hypothetical common-point configuration, the triangle ABK in
the auxiliary plane sigma has two right angles:

  angle BAK is right,
  angle ABK is right.

This is the exact planar configuration used by Euclid before invoking
Proposition I.17.
-/
theorem hilbert_XI14_triangle_has_two_right_angles_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B K : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B)
    (hKpi : S.OnPlane K pi)
    (hKrho : S.OnPlane K rho) :
    exists sigma : S.Plane,
    exists Ap Bp Kp : PlanePoint Geo sigma,
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Kp) /\
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        Bp Ap Kp /\
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        Ap Bp Kp := by

  rcases
      hilbert_XI14_unpack_right_angle_witnesses_wyler
        (Geo := Geo)
        pi rho l A B K
        hAB
        hPerpPi
        hPerpRho
        hKpi
        hKrho
    with
    ⟨sigma,
     Ap, Bp, Kp,
     U, V, U', V',
     hNon,
     hUAB,
     hVAK,
     hU'BA,
     hV'BK,
     hUA,
     hVA,
     hU'B,
     hV'B,
     hRightA,
     hRightB⟩

  let G := PlaneGeo Geo sigma

  have hABp : Ne Ap Bp :=
    hilbert_noncollinear_ne_first
      G Ap Bp Kp hNon

  have hBAp : Ne Bp Ap :=
    hABp.symm

  have hAKp : Ne Ap Kp := by
    apply
      hilbert_noncollinear_ne_first
        G Ap Kp Bp
    intro h
    exact hNon
      (PrimCollinearRotate G Ap Kp Bp h)

  have hKAp : Ne Kp Ap :=
    hAKp.symm

  have hBKp : Ne Bp Kp := by
    apply
      hilbert_noncollinear_ne_first
        G Bp Kp Ap
    intro h
    have hKAB :
        PrimCollinear G Kp Ap Bp :=
      PrimCollinearCycle G Bp Kp Ap h
    exact hNon
      (PrimCollinearCycle G Kp Ap Bp hKAB)

  have hKBp : Ne Kp Bp :=
    hBKp.symm

  have hNonUAV :
      Not (PrimCollinear G U Ap V) := by
    intro hUAV

    have hAVK :
        PrimCollinear G Ap V Kp :=
      PrimCollinearSwap G V Ap Kp hVAK

    have hUAK :
        PrimCollinear G U Ap Kp :=
      hilbert_primCollinear_trans
        G
        U Ap V Kp
        hVA.symm
        hUAV
        hAVK

    have hBAU :
        PrimCollinear G Bp Ap U :=
      PrimCollinearSymm G U Ap Bp hUAB

    have hAUK :
        PrimCollinear G Ap U Kp :=
      PrimCollinearSwap G U Ap Kp hUAK

    have hBAK :
        PrimCollinear G Bp Ap Kp :=
      hilbert_primCollinear_trans
        G
        Bp Ap U Kp
        hUA.symm
        hBAU
        hAUK

    exact hNon
      (PrimCollinearSwap G Bp Ap Kp hBAK)

  have hNonBAV :
      Not (PrimCollinear G Bp Ap V) := by
    intro hBAV

    have hAVK :
        PrimCollinear G Ap V Kp :=
      PrimCollinearSwap G V Ap Kp hVAK

    have hBAK :
        PrimCollinear G Bp Ap Kp :=
      hilbert_primCollinear_trans
        G
        Bp Ap V Kp
        hVA.symm
        hBAV
        hAVK

    exact hNon
      (PrimCollinearSwap G Bp Ap Kp hBAK)

  have hNonU'BV' :
      Not (PrimCollinear G U' Bp V') := by
    intro hU'BV'

    have hBV'K :
        PrimCollinear G Bp V' Kp :=
      PrimCollinearSwap G V' Bp Kp hV'BK

    have hU'BK :
        PrimCollinear G U' Bp Kp :=
      hilbert_primCollinear_trans
        G
        U' Bp V' Kp
        hV'B.symm
        hU'BV'
        hBV'K

    have hABU' :
        PrimCollinear G Ap Bp U' :=
      PrimCollinearSymm G U' Bp Ap hU'BA

    have hBU'K :
        PrimCollinear G Bp U' Kp :=
      PrimCollinearSwap G U' Bp Kp hU'BK

    have hABK :
        PrimCollinear G Ap Bp Kp :=
      hilbert_primCollinear_trans
        G
        Ap Bp U' Kp
        hU'B.symm
        hABU'
        hBU'K

    exact hNon hABK

  have hNonABV' :
      Not (PrimCollinear G Ap Bp V') := by
    intro hABV'

    have hBV'K :
        PrimCollinear G Bp V' Kp :=
      PrimCollinearSwap G V' Bp Kp hV'BK

    have hABK :
        PrimCollinear G Ap Bp Kp :=
      hilbert_primCollinear_trans
        G
        Ap Bp V' Kp
        hV'B.symm
        hABV'
        hBV'K

    exact hNon hABK

  have hOrientUB :=
    hilbert_XI14_collinear_arm_orientation_wyler
      G
      Ap U Bp
      hUA
      hBAp
      hUAB

  have hOrientVK :=
    hilbert_XI14_collinear_arm_orientation_wyler
      G
      Ap V Kp
      hVA
      hKAp
      hVAK

  have hOrientU'A :=
    hilbert_XI14_collinear_arm_orientation_wyler
      G
      Bp U' Ap
      hU'B
      hABp
      hU'BA

  have hOrientV'K :=
    hilbert_XI14_collinear_arm_orientation_wyler
      G
      Bp V' Kp
      hV'B
      hKBp
      hV'BK

  have hRightBAK :
      HilbertRightAngle G Bp Ap Kp :=
    hilbert_XI14_rightAngle_transport_by_orientations_wyler
      G
      U Ap V Bp Kp
      hRightA
      hNonUAV
      hNonBAV
      hOrientUB
      hOrientVK

  have hRightABK :
      HilbertRightAngle G Ap Bp Kp :=
    hilbert_XI14_rightAngle_transport_by_orientations_wyler
      G
      U' Bp V' Ap Kp
      hRightB
      hNonU'BV'
      hNonABV'
      hOrientU'A
      hOrientV'K

  exact
    ⟨sigma,
     Ap, Bp, Kp,
     hNon,
     hRightBAK,
     hRightABK⟩


/--
A strict Hilbert angle inequality is incompatible with congruence of
the two compared angles.

This is an immediate consequence of right-transport for
`HilbertAngleLess` and irreflexivity.
-/
theorem hilbert_XI14_angleLess_not_congruent_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertCongruence G]
    (A O B C P D : G.Point)
    (hLess :
      HilbertAngleLess G A O B C P D)
    (hCong :
      G.AngleCongruent A O B C P D) :
    False := by

  have hTarget :
      Not (PrimCollinear G A O B) :=
    hLess.1

  have hCongSymm :
      G.AngleCongruent C P D A O B :=
    G.angle_congruent_symmetry
      A O B
      C P D
      hCong

  have hSelf :
      HilbertAngleLess G A O B A O B :=
    hilbert_angleLess_transport_right
      G
      A O B
      C P D
      A O B
      hLess
      hTarget
      hCongSymm

  exact
    hilbert_angleLess_irrefl
      G A O B hSelf


theorem hilbert_XI14_two_right_angles_impossible_wyler
    (G : Geometry.Geo)
    [HilbertIncidence G]
    [HilbertCongruence G]
    (A B K : G.Point)
    (hNon : Not (PrimCollinear G A B K))
    (hRightBAK :
      HilbertRightAngle G B A K)
    (hRightABK :
      HilbertRightAngle G A B K) :
    False := by

  have hI17 :
      HilbertAnglesLessThanTwoRightAngles
        G B A K A B K :=
    euclid_proposition_17_BAC_ABC
      G A B K hNon

  rcases hI17 with
    ⟨E, hKBE, hLess⟩

  have hRightABE :
      HilbertRightAngle G A B E :=
    hilbert_XI14_rightAngle_transport_opposite_second_wyler
      G
      A B K E
      hKBE
      hNon
      hRightABK

  have hBAKnon :
      Not (PrimCollinear G B A K) :=
    hLess.1

  have hABEnon :
      Not (PrimCollinear G A B E) :=
    hLess.2.1

  have hCong :
      G.AngleCongruent
        B A K
        A B E :=
    hilbert_all_right_angles_congruent
      G
      B A K
      A B E
      hBAKnon
      hABEnon
      hRightBAK
      hRightABE

  exact
    hilbert_XI14_angleLess_not_congruent_wyler
      G
      B A K
      A B E
      hLess
      hCong



variable (Geo : Geometry.Geo)

/--
Euclid XI.14, normalized form.

If the same line l is perpendicular to plane pi at A and to plane rho
at B, and the two feet A and B are distinct, then the two planes have
no common point.

This is the formal version of Euclid's contradiction argument:
a hypothetical common point K produces, in the auxiliary plane through
l and K, a nondegenerate triangle ABK with two right angles; I.17 makes
that impossible.
-/
theorem euclid_proposition_11_14_normalized_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B) :
    HilbertSpacePlanesParallel Geo pi rho := by

  intro hCommon

  rcases hCommon with
    ⟨K, hKpi, hKrho⟩

  rcases
      hilbert_XI14_triangle_has_two_right_angles_wyler
        (Geo := Geo)
        pi rho l A B K
        hAB
        hPerpPi
        hPerpRho
        hKpi
        hKrho
    with
    ⟨sigma,
     Ap, Bp, Kp,
     hNon,
     hRightBAK,
     hRightABK⟩

  exact
    hilbert_XI14_two_right_angles_impossible_wyler
      (PlaneGeo Geo sigma)
      Ap Bp Kp
      hNon
      hRightBAK
      hRightABK


variable (Geo : Geometry.Geo)

/--
Inside a fixed ambient plane pi, every point A lies on two distinct
ambient lines wholly contained in pi.
-/
theorem hilbert_XI14_two_distinct_lines_through_point_in_plane_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi) :
    exists m n : Geo.Line,
      Ne m n /\
      HilbertLineInPlane Geo m pi /\
      HilbertLineInPlane Geo n pi /\
      H.OnLine A m /\
      H.OnLine A n := by

  let G := PlaneGeo Geo pi

  let Ap : PlanePoint Geo pi :=
    ⟨A, hApi⟩

  rcases
      hilbert_line_through_point
        G Ap
    with
    ⟨mp, hAmp⟩

  rcases
      hilbert_point_off_line
        G mp
    with
    ⟨Pp, hPmp⟩

  have hAP : Ne Ap Pp := by
    intro h
    subst Pp
    exact hPmp hAmp

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := G)
        Ap Pp hAP
    with
    ⟨np, hAnp, hPnp⟩

  have hmnp : Ne mp np := by
    intro h
    subst np
    exact hPmp hPnp

  exact
    ⟨mp.1,
     np.1,
     by
       intro hmn
       apply hmnp
       exact Subtype.ext hmn,
     mp.2,
     np.2,
     hAmp,
     hAnp⟩


variable (Geo : Geometry.Geo)

/--
Uniqueness of a plane perpendicular to a fixed line at a fixed point.

If the same ambient line l is perpendicular to planes pi and rho at
the same point A, then pi = rho.

The proof uses Euclid XI.5:
- choose two distinct lines m,n through A in pi;
- every line p through A in rho is perpendicular to l;
- XI.5 puts m,n,p in one plane;
- since m,n already determine pi, p lies in pi;
- two distinct lines through A in rho therefore lie in both rho and pi,
  so the two planes coincide.
-/
theorem hilbert_XI14_plane_perpendicular_to_line_at_unique_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A : Geo.Point)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho A) :
    pi = rho := by

  have hIncPi :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerpPi

  have hIncRho :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerpRho

  have hApi : S.OnPlane A pi :=
    hIncPi.2

  have hArho : S.OnPlane A rho :=
    hIncRho.2

  rcases
      hilbert_XI14_two_distinct_lines_through_point_in_plane_wyler
        (Geo := Geo)
        pi A hApi
    with
    ⟨m, n,
     hmn,
     hmpi,
     hnpi,
     hAm,
     hAn⟩

  have hPerpM :
      HilbertLinesPerpendicularAt Geo l m A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerpPi
      hmpi
      hAm

  have hPerpN :
      HilbertLinesPerpendicularAt Geo l n A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerpPi
      hnpi
      hAn

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        m n hmn A hAm hAn
    with
    ⟨tau,
     hmtau,
     hntau,
     hUniqueTau⟩

  have hpi_tau : pi = tau :=
    hUniqueTau pi hmpi hnpi

  have hLineRhoToPi :
      forall p : Geo.Line,
        HilbertLineInPlane Geo p rho ->
        H.OnLine A p ->
        HilbertLineInPlane Geo p pi := by

    intro p hprho hAp

    have hPerpP :
        HilbertLinesPerpendicularAt Geo l p A :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hPerpRho
        hprho
        hAp

    rcases
        hilbert_three_common_perpendiculars_coplanar_wyler
          (Geo := Geo)
          l m n p
          A
          hmn
          hPerpM
          hPerpN
          hPerpP
      with
      ⟨sigma,
       hmsigma,
       hnsigma,
       hpsigma⟩

    have hsigma_tau : sigma = tau :=
      hUniqueTau sigma hmsigma hnsigma

    have hptau :
        HilbertLineInPlane Geo p tau := by
      rw [← hsigma_tau]
      exact hpsigma

    rw [hpi_tau]
    exact hptau

  rcases
      hilbert_XI14_two_distinct_lines_through_point_in_plane_wyler
        (Geo := Geo)
        rho A hArho
    with
    ⟨p, q,
     hpq,
     hprho,
     hqrho,
     hAp,
     hAq⟩

  have hppi :
      HilbertLineInPlane Geo p pi :=
    hLineRhoToPi p hprho hAp

  have hqpi :
      HilbertLineInPlane Geo q pi :=
    hLineRhoToPi q hqrho hAq

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        p q hpq A hAp hAq
    with
    ⟨omega,
     hpomega,
     hqomega,
     hUniqueOmega⟩

  have hrho_omega : rho = omega :=
    hUniqueOmega rho hprho hqrho

  have hpi_omega : pi = omega :=
    hUniqueOmega pi hppi hqpi

  exact
    hpi_omega.trans hrho_omega.symm


variable (Geo : Geometry.Geo)

end Geometry

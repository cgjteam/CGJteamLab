import CGJteamLab.Hilbert3DInterface
import CGJteamLab.HilbertDimensionFreeIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert E3 to dimension-free Smith incidence

Purpose:

  HilbertSpaceIncidence
    -> HilbertDimensionFreeIncidence

This production bridge introduces no new `class`, no `axiom`, and no global
`instance`.  It constructs the existing dimension-free Smith incidence
structure as a theorem from the spatial Hilbert incidence axioms.
-/

/--
Any three ambient points of a Hilbert three-space are coplanar.
-/
theorem hilbert3D_three_points_coplanar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (A B C : Geo.Point) :
    exists pi : S.Plane,
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi := by

  by_cases hABC : PrimCollinear Geo A B C

  next =>
    rcases hABC with ⟨l, hAl, hBl, hCl⟩

    rcases hilbert_point_off_line
        (Geo := Geo) l with
      ⟨P, hPl⟩

    rcases hilbert_plane_through_line_and_external_point
        (Geo := Geo) l P hPl with
      ⟨pi, hlpi, _hPpi, _hUnique⟩

    exact
      ⟨pi,
       hlpi A hAl,
       hlpi B hBl,
       hlpi C hCl⟩

  next =>
    exact
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B C hABC


/--
Hilbert I.7 implies Smith I5 in E3.

The coplanarity hypothesis on p0,p1,q0,q1 is not needed in dimension 3.
-/
theorem hilbert3D_smith_i5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo] :
    forall p0 p1 q0 q1 : Geo.Point,
      HilbertCoplanar4 Geo p0 p1 q0 q1 ->
      forall p : Geo.Point,
        exists q : Geo.Point,
          Ne q p /\
          HilbertCoplanar4 Geo p p0 q0 q /\
          HilbertCoplanar4 Geo p p1 q1 q := by

  intro p0 p1 q0 q1 _hBase p

  rcases hilbert3D_three_points_coplanar
      (Geo := Geo) p p0 q0 with
    ⟨alpha, hpAlpha, hp0Alpha, hq0Alpha⟩

  rcases hilbert3D_three_points_coplanar
      (Geo := Geo) p p1 q1 with
    ⟨beta, hpBeta, hp1Beta, hq1Beta⟩

  by_cases hAlphaBeta : alpha = beta

  next =>
    subst beta

    rcases hilbert_point_off_plane
        (Geo := Geo) alpha with
      ⟨R, hRAlpha⟩

    rcases hilbert3D_three_points_coplanar
        (Geo := Geo) p R R with
      ⟨gamma, hpGamma, hRGamma, _hRGamma2⟩

    have hAlphaGamma : Ne alpha gamma := by
      intro hEq
      subst gamma
      exact hRAlpha hRGamma

    rcases
        HilbertSpaceIncidence.plane_second_common_point
          (Geo := Geo)
          alpha gamma hAlphaGamma
          p hpAlpha hpGamma with
      ⟨q, hqp, hqAlpha, _hqGamma⟩

    exact
      ⟨q,
       hqp,
       ⟨alpha, hpAlpha, hp0Alpha, hq0Alpha, hqAlpha⟩,
       ⟨alpha, hpAlpha, hp1Beta, hq1Beta, hqAlpha⟩⟩

  next =>
    rcases
        HilbertSpaceIncidence.plane_second_common_point
          (Geo := Geo)
          alpha beta hAlphaBeta
          p hpAlpha hpBeta with
      ⟨q, hqp, hqAlpha, hqBeta⟩

    exact
      ⟨q,
       hqp,
       ⟨alpha, hpAlpha, hp0Alpha, hq0Alpha, hqAlpha⟩,
       ⟨beta, hpBeta, hp1Beta, hq1Beta, hqBeta⟩⟩


/--
The complete dimension-free Smith incidence package is derived from
Hilbert spatial incidence in E3.
-/
theorem hilbert3D_to_dimension_free_incidence
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo] :
    HilbertDimensionFreeIncidence Geo := by

  refine
    { two_points_on_each_line := ?_
      three_noncollinear_on_plane := ?_
      plane_through := ?_
      plane_unique := ?_
      line_in_plane := ?_
      smith_i5 := ?_ }

  next =>
    exact
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo)

  next =>
    exact
      hilbert_three_noncollinear_on_plane
        (Geo := Geo)

  next =>
    exact
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)

  next =>
    exact
      HilbertSpaceIncidence.plane_unique
        (Geo := Geo)

  next =>
    exact
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)

  next =>
    exact
      hilbert3D_smith_i5
        (Geo := Geo)


end Geometry

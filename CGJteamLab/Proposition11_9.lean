import CGJteamLab.Proposition11_8

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
If `l` and `m` are distinct lines, then `m` has a point not lying on `l`.

This is a small incidence helper for XI.9.
-/
theorem hilbert_XI9_point_on_second_line_off_first
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (hlm : Ne l m) :
    exists P : Geo.Point,
      H.OnLine P m /\
      Not (H.OnLine P l) := by

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) m with
    ⟨A, B, hAB, hAm, hBm⟩

  by_cases hAl : H.OnLine A l
  · by_cases hBl : H.OnLine B l
    · have hml : m = l :=
        HilbertPlaneIncidence.line_unique
          A B hAB
          m l
          hAm hBm
          hAl hBl
      exact False.elim (hlm hml.symm)
    · exact ⟨B, hBm, hBl⟩
  · exact ⟨A, hAm, hAl⟩


/--
Two planes which contain the same line and the same point outside that
line are equal.

This is the uniqueness part of the line-plus-external-point plane theorem.
-/
theorem hilbert_XI9_planes_eq_of_common_line_and_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l))
    (pi rho : S.Plane)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hPpi : S.OnPlane P pi)
    (hPrho : S.OnPlane P rho) :
    pi = rho := by

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l P hPl with
    ⟨eta, hleta, hPeta, hUnique⟩

  have hPiEta : pi = eta :=
    hUnique pi hlpi hPpi

  have hRhoEta : rho = eta :=
    hUnique rho hlrho hPrho

  exact hPiEta.trans hRhoEta.symm


/--
Euclid XI.9.

If two straight lines are each parallel to the same straight line, and the
three lines are not all contained in one plane, then the first two lines are
parallel to one another.

The formal proof is affine and synthetic.  It uses the plane-local Euclidean
parallel uniqueness axiom rather than reconstructing Euclid's perpendicular
argument.
-/
theorem euclid_proposition_11_9
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m n : Geo.Line)
    (hParallelLN : HilbertSpaceLinesParallel Geo l n)
    (hParallelMN : HilbertSpaceLinesParallel Geo m n)
    (hNoCommonPlane :
      Not (exists omega : S.Plane,
        HilbertLineInPlane Geo l omega /\
        HilbertLineInPlane Geo m omega /\
        HilbertLineInPlane Geo n omega)) :
    HilbertSpaceLinesParallel Geo l m := by

  ----------------------------------------------------------------------
  -- The two given parallelisms supply two carrier planes.
  ----------------------------------------------------------------------

  rcases hParallelLN with
    ⟨sigma, hlsigma, hnsigma, hDisjointLN⟩

  rcases hParallelMN with
    ⟨tau, hmtau, hntau, hDisjointMN⟩

  ----------------------------------------------------------------------
  -- The two carrier planes are distinct.
  ----------------------------------------------------------------------

  have hSigmaTau : Ne sigma tau := by
    intro hEq

    have hmsigma :
        HilbertLineInPlane Geo m sigma := by
      rw [hEq]
      exact hmtau

    exact
      hNoCommonPlane
        ⟨sigma, hlsigma, hmsigma, hnsigma⟩

  ----------------------------------------------------------------------
  -- The target lines l and m are distinct.
  ----------------------------------------------------------------------

  have hlm : Ne l m := by
    intro hEq

    have hmsigma :
        HilbertLineInPlane Geo m sigma := by
      rw [← hEq]
      exact hlsigma

    exact
      hNoCommonPlane
        ⟨sigma, hlsigma, hmsigma, hnsigma⟩

  ----------------------------------------------------------------------
  -- Choose B on m but outside l.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI9_point_on_second_line_off_first
        (Geo := Geo)
        l m hlm with
    ⟨B, hBm, hBl⟩

  have hBtau : S.OnPlane B tau :=
    hmtau B hBm

  have hBn : Not (H.OnLine B n) := by
    intro hBn
    exact hDisjointMN ⟨B, hBm, hBn⟩

  ----------------------------------------------------------------------
  -- Let omega be the unique plane through l and the external point B.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l B hBl with
    ⟨omega, hlomega, hBomega, _hUniqueOmega⟩

  ----------------------------------------------------------------------
  -- sigma and omega are distinct.
  ----------------------------------------------------------------------

  have hSigmaOmega : Ne sigma omega := by
    intro hEq

    have hBsigma : S.OnPlane B sigma := by
      rw [hEq]
      exact hBomega

    have hEqSigmaTau : sigma = tau :=
      hilbert_XI9_planes_eq_of_common_line_and_external_point
        (Geo := Geo)
        n B hBn
        sigma tau
        hnsigma hntau
        hBsigma hBtau

    exact hSigmaTau hEqSigmaTau

  ----------------------------------------------------------------------
  -- omega and tau are distinct; otherwise all three original lines
  -- would lie in tau.
  ----------------------------------------------------------------------

  have hOmegaTau : Ne omega tau := by
    intro hEq

    have hltau :
        HilbertLineInPlane Geo l tau := by
      rw [← hEq]
      exact hlomega

    exact
      hNoCommonPlane
        ⟨tau, hltau, hmtau, hntau⟩

  ----------------------------------------------------------------------
  -- Intersect omega and tau in a line r through B.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        omega tau hOmegaTau
        B hBomega hBtau with
    ⟨r, hBr, hromega, hrtau, _hSection⟩

  ----------------------------------------------------------------------
  -- r is disjoint from n.
  --
  -- If P belonged to both, then sigma and omega would both contain l
  -- and the external point P, forcing sigma = omega.
  ----------------------------------------------------------------------

  have hDisjointRN :
      HilbertLinesDisjoint Geo r n := by

    rintro ⟨P, hPr, hPn⟩

    have hPomega : S.OnPlane P omega :=
      hromega P hPr

    have hPsigma : S.OnPlane P sigma :=
      hnsigma P hPn

    have hPl : Not (H.OnLine P l) := by
      intro hPl
      exact hDisjointLN ⟨P, hPl, hPn⟩

    have hEqSigmaOmega : sigma = omega :=
      hilbert_XI9_planes_eq_of_common_line_and_external_point
        (Geo := Geo)
        l P hPl
        sigma omega
        hlsigma hlomega
        hPsigma hPomega

    exact hSigmaOmega hEqSigmaOmega

  ----------------------------------------------------------------------
  -- In tau, both r and m pass through B and are disjoint from n.
  -- Group IV therefore identifies r with m.
  ----------------------------------------------------------------------

  have hrm : r = m :=
    HilbertSpaceEuclidean.parallel_unique_in_plane
      (Geo := Geo)
      tau
      n hntau
      B hBtau hBn
      r m
      hrtau hmtau
      hBr hDisjointRN
      hBm hDisjointMN

  have hmomega :
      HilbertLineInPlane Geo m omega := by
    rw [← hrm]
    exact hromega

  ----------------------------------------------------------------------
  -- Finally l and m are disjoint.
  --
  -- A common point P would be an external point of n lying in both
  -- sigma and tau, again forcing sigma = tau.
  ----------------------------------------------------------------------

  have hDisjointLM :
      HilbertLinesDisjoint Geo l m := by

    rintro ⟨P, hPl, hPm⟩

    have hPn : Not (H.OnLine P n) := by
      intro hPn
      exact hDisjointLN ⟨P, hPl, hPn⟩

    have hPsigma : S.OnPlane P sigma :=
      hlsigma P hPl

    have hPtau : S.OnPlane P tau :=
      hmtau P hPm

    have hEqSigmaTau : sigma = tau :=
      hilbert_XI9_planes_eq_of_common_line_and_external_point
        (Geo := Geo)
        n P hPn
        sigma tau
        hnsigma hntau
        hPsigma hPtau

    exact hSigmaTau hEqSigmaTau

  exact
    ⟨omega,
     hlomega,
     hmomega,
     hDisjointLM⟩

end Geometry

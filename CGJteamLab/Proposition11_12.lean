import CGJteamLab.Proposition11_11
import CGJteamLab.Proposition11_8
import CGJteamLab.Proposition31

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
If a line is perpendicular to a plane at C, then C is the unique
point common to that line and the plane.
-/
theorem hilbert_XI12_perpendicular_foot_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (C A : Geo.Point)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi C)
    (hAl : H.OnLine A l)
    (hApi : S.OnPlane A pi) :
    A = C := by

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hCl : H.OnLine C l :=
    hInc.1

  have hCpi : S.OnPlane C pi :=
    hInc.2

  by_contra hAC

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A C hAC
      l hAl hCl
      pi hApi hCpi

  have hSelfPerp :
      HilbertLinesPerpendicularAt Geo l l C :=
    hPerp.2.2 l hlpi hCl

  have hll : Ne l l :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l l C hSelfPerp

  exact hll rfl


/--
Inside an ambient plane sigma, through a point A not on a line l,
Euclid I.31 constructs a line m through A parallel to l.  The planar
parallelism is then packaged as ambient spatial parallelism.
-/
theorem hilbert_XI12_parallel_through_point_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (l : Geo.Line)
    (A : Geo.Point)
    (hlsigma : HilbertLineInPlane Geo l sigma)
    (hAsigma : S.OnPlane A sigma)
    (hAl : Not (H.OnLine A l)) :
    exists m : Geo.Line,
      H.OnLine A m /\
      HilbertSpaceLinesParallel Geo l m := by

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) l
    with
    ⟨B, C, hBC, hBl, hCl⟩

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hCsigma : S.OnPlane C sigma :=
    hlsigma C hCl

  let Bsigma : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Csigma : PlanePoint Geo sigma :=
    ⟨C, hCsigma⟩

  let Asigma : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let lsigma : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  have hBCsigma : Ne Bsigma Csigma := by
    intro h
    apply hBC
    exact congrArg Subtype.val h

  have hBCA :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Bsigma Csigma Asigma) := by
    intro hColPlane

    have hColAmbient :
        PrimCollinear Geo B C A :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma
        Bsigma Csigma Asigma
        hColPlane

    have hAonL : H.OnLine A l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hBC
        hBl
        hCl
        hColAmbient

    exact hAl hAonL

  rcases
      hilbert_parallel_through_point_exists
        (PlaneGeo Geo sigma)
        Bsigma Csigma Asigma
        hBCsigma
        hBCA
    with
    ⟨Qsigma, hAQ, hParallelPlane⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        Asigma Qsigma hAQ
    with
    ⟨msigma, hAm, hQm⟩

  have hDisjointAmbient :
      HilbertLinesDisjoint Geo l msigma.1 := by
    rintro ⟨X, hXl, hXm⟩

    have hXsigma : S.OnPlane X sigma :=
      hlsigma X hXl

    let Xsigma : PlanePoint Geo sigma :=
      ⟨X, hXsigma⟩

    have hXBC :
        Xsigma ∈
          (PlaneGeo Geo sigma).PointLine
            Bsigma Csigma := by
      apply
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo sigma)
          Bsigma Csigma Xsigma
          lsigma
          hParallelPlane.1
          hBl
          hCl).mpr
      exact hXl

    have hXAQ :
        Xsigma ∈
          (PlaneGeo Geo sigma).PointLine
            Asigma Qsigma := by
      apply
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo sigma)
          Asigma Qsigma Xsigma
          msigma
          hParallelPlane.2.1
          hAm
          hQm).mpr
      exact hXm

    exact
      Set.disjoint_left.mp
        hParallelPlane.2.2
        hXBC
        hXAQ

  refine
    ⟨msigma.1,
     hAm,
     ?_⟩

  exact
    ⟨sigma,
     hlsigma,
     msigma.2,
     hDisjointAmbient⟩


/--
Euclid, Book XI, Proposition XI.12.

To set up a straight line at right angles to a given plane
from a given point in it.

Given a plane pi and a point A on pi, there exists a line
perpendicular to pi at A.

Classical dependency route:
XI.11 -> I.31 -> XI.8.
-/
theorem euclid_proposition_11_12
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi) :
    exists l : Geo.Line,
      HilbertLinePerpendicularPlaneAt Geo l pi A := by

  rcases
      hilbert_point_off_plane
        (Geo := Geo) pi
    with
    ⟨B, hBpi⟩

  rcases
      euclid_proposition_11_11
        (Geo := Geo)
        pi B hBpi
    with
    ⟨l, F, _hBl, hPerp⟩

  by_cases hAl : H.OnLine A l

  · have hAF : A = F :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        pi l F A
        hPerp
        hAl
        hApi

    subst F

    exact ⟨l, hPerp⟩

  · rcases
        hilbert_plane_through_line_and_external_point
          (Geo := Geo)
          l A hAl
      with
      ⟨sigma, hlsigma, hAsigma, _hSigmaUnique⟩

    rcases
        hilbert_XI12_parallel_through_point_in_plane
          (Geo := Geo)
          sigma l A
          hlsigma
          hAsigma
          hAl
      with
      ⟨m, hAm, hParallel⟩

    rcases
        euclid_proposition_11_8
          (Geo := Geo)
          l m pi F
          hParallel
          hPerp
      with
      ⟨D, hPerpM⟩

    have hAD : A = D :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        pi m D A
        hPerpM
        hAm
        hApi

    subst D

    exact ⟨m, hPerpM⟩

end Geometry

import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.7.

If two straight lines are parallel and arbitrary points are chosen on
them, then the straight line joining those points lies in the same
plane as the parallel lines.

In the present spatial Hilbert interface, coplanarity is part of
`HilbertSpaceLinesParallel`. The final line-in-plane step is Hilbert I.6.
-/
theorem euclid_proposition_11_7
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (E F : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hEl : H.OnLine E l)
    (hFm : H.OnLine F m) :
    exists sigma : S.Plane,
      HilbertLineInPlane Geo l sigma /\
      HilbertLineInPlane Geo m sigma /\
      exists n : Geo.Line,
        H.OnLine E n /\
        H.OnLine F n /\
        HilbertLineInPlane Geo n sigma := by

  rcases hParallel with
    ⟨sigma, hlsigma, hmsigma, hDisjoint⟩

  have hEsigma : S.OnPlane E sigma :=
    hlsigma E hEl

  have hFsigma : S.OnPlane F sigma :=
    hmsigma F hFm

  have hEF : Ne E F := by
    intro hEq
    subst F
    exact hDisjoint
      ⟨E, hEl, hFm⟩

  rcases
      HilbertPlaneIncidence.line_through
        E F hEF
    with
    ⟨n, hEn, hFn⟩

  have hnsigma :
      HilbertLineInPlane Geo n sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      E F hEF
      n hEn hFn
      sigma hEsigma hFsigma

  exact
    ⟨sigma,
     hlsigma,
     hmsigma,
     n,
     hEn,
     hFn,
     hnsigma⟩

end Geometry

import CGJteamLab.Proposition11_12

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid, Book XI, Proposition XI.13.

From the same point two straight lines cannot be set up at right angles
to the same plane on the same side.

In the present formalization `Geo.Line` is an unoriented extensional
line. Therefore the natural formal statement is stronger and cleaner:

if two lines are perpendicular to the same plane at the same point,
then the two lines are equal.

The proof is synthetic.

Assume that the two perpendicular lines `l,m` are distinct. Since they
meet at `A`, they determine a plane `sigma`. The planes `pi` and `sigma`
are distinct, because otherwise `l` would lie in `pi`, impossible for a
line perpendicular to `pi`.

Let `q` be the intersection line of `pi` and `sigma` through `A`.
Since both `l` and `m` are perpendicular to `pi`, both are perpendicular
to `q`. Reversing these perpendicularities, XI.4 gives that `q` is
perpendicular to `sigma`. But `q` itself lies in `sigma`, a contradiction.

Thus `l = m`.
-/
theorem euclid_proposition_11_13
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (A : Geo.Point)
    (hLperp :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hMperp :
      HilbertLinePerpendicularPlaneAt Geo m pi A) :
    l = m := by

  by_contra hlm

  have hLInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp

  have hMInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hMperp

  have hAl : H.OnLine A l :=
    hLInc.1

  have hAm : H.OnLine A m :=
    hMInc.1

  have hApi : S.OnPlane A pi :=
    hLInc.2

  ----------------------------------------------------------------------
  -- The supposed distinct lines l,m determine an auxiliary plane sigma.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm
        A hAl hAm
    with
    ⟨sigma, hlsigma, hmsigma, _hSigmaUnique⟩

  have hAsigma : S.OnPlane A sigma :=
    hlsigma A hAl

  ----------------------------------------------------------------------
  -- sigma cannot equal pi.
  ----------------------------------------------------------------------

  have hSigmaPi : Ne sigma pi := by
    intro hEq

    have hlpi :
        HilbertLineInPlane Geo l pi := by
      intro X hXl
      have hXsigma : S.OnPlane X sigma :=
        hlsigma X hXl
      simpa [hEq] using hXsigma

    exact
      (hilbert_linePerpendicularPlaneAt_not_in_plane
        (Geo := Geo)
        l pi A hLperp)
        hlpi

  ----------------------------------------------------------------------
  -- Let q be the intersection line of pi and sigma through A.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        pi sigma hSigmaPi.symm
        A hApi hAsigma
    with
    ⟨q, hAq, hqpi, hqsigma, _hIntersection⟩

  ----------------------------------------------------------------------
  -- Both l and m are perpendicular to q because q lies in pi.
  ----------------------------------------------------------------------

  have hLperpQ :
      HilbertLinesPerpendicularAt Geo l q A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hLperp
      hqpi
      hAq

  have hMperpQ :
      HilbertLinesPerpendicularAt Geo m q A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hMperp
      hqpi
      hAq

  have hQperpL :
      HilbertLinesPerpendicularAt Geo q l A :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      l q A
      hLperpQ

  have hQperpM :
      HilbertLinesPerpendicularAt Geo q m A :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      m q A
      hMperpQ

  ----------------------------------------------------------------------
  -- XI.4 makes q perpendicular to the whole auxiliary plane sigma.
  ----------------------------------------------------------------------

  let lp : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  let mp : PlaneLine Geo sigma :=
    ⟨m, hmsigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  have hlmp : Ne lp mp := by
    intro h
    apply hlm
    exact congrArg Subtype.val h

  have hQperpLp :
      HilbertLinesPerpendicularAt Geo q lp.1 Ap.1 := by
    simpa [lp, Ap] using hQperpL

  have hQperpMp :
      HilbertLinesPerpendicularAt Geo q mp.1 Ap.1 := by
    simpa [mp, Ap] using hQperpM

  have hQperpSigma :
      HilbertLinePerpendicularPlaneAt Geo q sigma A := by
    have h :=
      euclid_proposition_11_4
        (Geo := Geo)
        sigma
        lp mp
        q
        Ap
        hlmp
        hQperpLp
        hQperpMp
    simpa [Ap] using h

  ----------------------------------------------------------------------
  -- Contradiction: q lies in sigma.
  ----------------------------------------------------------------------

  exact
    (hilbert_linePerpendicularPlaneAt_not_in_plane
      (Geo := Geo)
      q sigma A hQperpSigma)
      hqsigma

end Geometry

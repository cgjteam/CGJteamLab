import CGJteamLab.Coxeter.E4MarkedPlaneMetric
import CGJteamLab.Proposition47

/-!
# Corrected E4 normal uniqueness

Production promotion of the validated same-foot normal uniqueness and
hyperplane perpendicular-foot uniqueness results.

The workshop `letI` linter warning is removed with an ordinary `let`
binding; theorem APIs are unchanged.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal uniqueness at a fixed foot

Assume that l and m are both normal to the same hyperplane Sigma at F.
If l != m, test53 places l and m in one ambient 2-plane pi and produces
the intersection line n = pi cap Sigma. Both l and m are perpendicular
to n at F.

The perpendicularity l perpendicular n already contains two points
A on l and B on n such that A,F,B are noncollinear. Since l,n lie in pi,
these three points mark pi as a genuine Hilbert plane. Test61 then gives
l=m inside PlaneGeo pi, contradicting l != m.

No old ambient 3D incidence, order, congruence, or Euclidean instance is
used.
-/

/--
In corrected E4, a normal line to a fixed hyperplane at a fixed foot is
unique.
-/
theorem hilbert4D_normal_same_foot_unique_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (l m : Geo.Line)
    (F : Geo.Point)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma F) :
    l = m := by

  by_contra hLM

  have hConfig :=
    hilbert4D_two_normals_same_foot_plane_configuration_corrected
      (Geo := Geo)
      Sigma l m F
      hLM
      hLNormal
      hMNormal

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hConfig

  have hConfigPi :=
    Classical.choose_spec hConfig

  let n : Geo.Line :=
    Classical.choose hConfigPi

  have hData :=
    Classical.choose_spec hConfigPi

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    hData.1

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    hData.2.1

  have hFn :
      H.OnLine F n :=
    hData.2.2.1

  have hnpi :
      HilbertLineInPlane Geo n pi :=
    hData.2.2.2.1

  have hLperpN :
      HilbertLinesPerpendicularAt Geo l n F :=
    hData.2.2.2.2.2.2.1

  have hMperpN :
      HilbertLinesPerpendicularAt Geo m n F :=
    hData.2.2.2.2.2.2.2

  have hABExists :=
    hLperpN.2.2

  let A : Geo.Point :=
    Classical.choose hABExists

  have hBExists :=
    Classical.choose_spec hABExists

  let B : Geo.Point :=
    Classical.choose hBExists

  have hABData :=
    Classical.choose_spec hBExists

  have hAF : Ne A F :=
    hABData.1

  have hBF : Ne B F :=
    hABData.2.1

  have hAl :
      H.OnLine A l :=
    hABData.2.2.1

  have hBn :
      H.OnLine B n :=
    hABData.2.2.2.1

  have hAFB :
      Not (PrimCollinear Geo A F B) :=
    hABData.2.2.2.2.1

  have hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi :=
    hlpi A hAl

  have hFpi :
      Q.toHilbertSpacePrimitive.OnPlane F pi :=
    hnpi F hFn

  have hBpi :
      Q.toHilbertSpacePrimitive.OnPlane B pi :=
    hnpi B hBn

  let lp : PlaneLine Geo pi :=
    Subtype.mk l hlpi

  let mp : PlaneLine Geo pi :=
    Subtype.mk m hmpi

  let np : PlaneLine Geo pi :=
    Subtype.mk n hnpi

  let Fp : PlanePoint Geo pi :=
    Subtype.mk F hFpi

  have hPlaneEq :
      lp = mp :=
    planeGeo_perpendicular_same_foot_unique4_corrected
      (Geo := Geo)
      pi
      A F B
      hApi hFpi hBpi
      hAFB
      lp mp np Fp
      (by
        simpa [lp, np, Fp] using hLperpN)
      (by
        simpa [mp, np, Fp] using hMperpN)

  have hAmbientEq : l = m := by
    exact congrArg Subtype.val hPlaneEq

  exact hLM hAmbientEq

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 perpendicular-foot uniqueness

The old test25 proved uniqueness of the perpendicular foot by first
claiming that arbitrary normals to the same hyperplane are spatially
parallel and then applying ambient XI.6.  That route is not dimension
safe in genuine E4.

For one fixed point P there is a much shorter corrected argument.

Assume F != G are two perpendicular feet of P on Sigma.  Let l=PF and
m=PG be the corresponding normal lines, and let q=FG inside Sigma.
The three points P,F,G are noncollinear; otherwise one normal would
contain two distinct points of Sigma and hence lie in Sigma, impossible.

Thus P,F,G determine one ambient 2-plane pi.  The lines l,m,q all lie
in pi.  Since l and m are normals to Sigma,

  l perpendicular q at F,
  m perpendicular q at G.

Inside PlaneGeo pi the triangle FGP therefore has right angles at both
F and G, contradicting Euclid I.17 through the already proved helper
`i47_aux_two_right_angles_impossible`.

No ambient 3D structure and no general normal-parallelism theorem are
used.
-/

/--
In corrected E4 the perpendicular foot of a fixed point on a fixed
hyperplane is unique.
-/
theorem hyperplane_perpendicular_foot_unique4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (P F G : Geo.Point)
    (hPerpF :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P)
    (hPerpG :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma G P) :
    F = G := by

  rcases hPerpF with
    ⟨l, hPl, hLNormal⟩

  rcases hPerpG with
    ⟨m, hPm, hMNormal⟩

  by_contra hFG

  have hFl : H.OnLine F l :=
    hLNormal.1

  have hGm : H.OnLine G m :=
    hMNormal.1

  have hFSigma : Q.OnHyperplane F Sigma :=
    hLNormal.2.1

  have hGSigma : Q.OnHyperplane G Sigma :=
    hMNormal.2.1

  ----------------------------------------------------------------------
  -- P cannot coincide with either foot if the two feet are distinct.
  ----------------------------------------------------------------------

  have hPF : Ne P F := by
    intro hPF

    have hFm : H.OnLine F m := by
      rw [← hPF]
      exact hPm

    have hmSigma :
        HilbertLineInHyperplane4 Geo m Sigma :=
      H4I.line_in_hyperplane
        F G hFG
        m hFm hGm
        Sigma hFSigma hGSigma

    exact
      (HilbertLinePerpendicularHyperplaneAt4_corrected.not_line_in_hyperplane
          (Geo := Geo)
          hMNormal)
        hmSigma

  have hPG : Ne P G := by
    intro hPG

    have hGl : H.OnLine G l := by
      rw [← hPG]
      exact hPl

    have hlSigma :
        HilbertLineInHyperplane4 Geo l Sigma :=
      H4I.line_in_hyperplane
        F G hFG
        l hFl hGl
        Sigma hFSigma hGSigma

    exact
      (HilbertLinePerpendicularHyperplaneAt4_corrected.not_line_in_hyperplane
          (Geo := Geo)
          hLNormal)
        hlSigma

  ----------------------------------------------------------------------
  -- P,F,G are noncollinear.
  ----------------------------------------------------------------------

  have hPFG :
      Not (PrimCollinear Geo P F G) := by

    intro hCol

    have hGl : H.OnLine G l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hCol

    have hlSigma :
        HilbertLineInHyperplane4 Geo l Sigma :=
      H4I.line_in_hyperplane
        F G hFG
        l hFl hGl
        Sigma hFSigma hGSigma

    exact
      (HilbertLinePerpendicularHyperplaneAt4_corrected.not_line_in_hyperplane
          (Geo := Geo)
          hLNormal)
        hlSigma

  ----------------------------------------------------------------------
  -- The triangle P,F,G determines one ambient 2-plane pi.
  ----------------------------------------------------------------------

  rcases
      Hilbert4DAmbientIncidence.plane_through
        (Geo := Geo)
        P F G
        hPFG with
    ⟨pi, hPpi, hFpi, hGpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    H4I.line_in_plane
      P F hPF
      l hPl hFl
      pi hPpi hFpi

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    H4I.line_in_plane
      P G hPG
      m hPm hGm
      pi hPpi hGpi

  ----------------------------------------------------------------------
  -- q is the line FG.  It lies both in Sigma and in pi.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        F G hFG with
    ⟨q, hFq, hGq⟩

  have hqSigma :
      HilbertLineInHyperplane4 Geo q Sigma :=
    H4I.line_in_hyperplane
      F G hFG
      q hFq hGq
      Sigma hFSigma hGSigma

  have hqpi :
      HilbertLineInPlane Geo q pi :=
    H4I.line_in_plane
      F G hFG
      q hFq hGq
      pi hFpi hGpi

  ----------------------------------------------------------------------
  -- Both normal lines are perpendicular to q at their feet.
  ----------------------------------------------------------------------

  have hLperpQ :
      HilbertLinesPerpendicularAt Geo l q F :=
    hLNormal.2.2
      q hqSigma hFq

  have hMperpQ :
      HilbertLinesPerpendicularAt Geo m q G :=
    hMNormal.2.2
      q hqSigma hGq

  ----------------------------------------------------------------------
  -- Pass only this concrete configuration to PlaneGeo(pi).
  ----------------------------------------------------------------------

  let Pp : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let Fp : PlanePoint Geo pi :=
    ⟨F, hFpi⟩

  let Gp : PlanePoint Geo pi :=
    ⟨G, hGpi⟩

  let lp : PlaneLine Geo pi :=
    ⟨l, hlpi⟩

  let mp : PlaneLine Geo pi :=
    ⟨m, hmpi⟩

  let qp : PlaneLine Geo pi :=
    ⟨q, hqpi⟩

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi P F G
      hPpi hFpi hGpi
      hPFG

  have hLperpQPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) lp qp Fp :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi lp qp Fp).mpr
      hLperpQ

  have hMperpQPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) mp qp Gp :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi mp qp Gp).mpr
      hMperpQ

  have hPFp : Ne Pp Fp := by
    intro h
    exact hPF (congrArg Subtype.val h)

  have hPGp : Ne Pp Gp := by
    intro h
    exact hPG (congrArg Subtype.val h)

  have hFGp : Ne Fp Gp := by
    intro h
    exact hFG (congrArg Subtype.val h)

  have hGFp : Ne Gp Fp :=
    hFGp.symm

  ----------------------------------------------------------------------
  -- Right angle at F in triangle FGP.
  ----------------------------------------------------------------------

  have hRightPFGData :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo pi)
      lp qp
      Fp
      Pp Gp
      (hilbert_linesPerpendicularAt_ne
        (PlaneGeo Geo pi)
        lp qp Fp hLperpQPlane)
      hLperpQPlane
      hPFp
      hGFp
      hPl
      hGq

  have hRightGFP :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Gp Fp Pp :=
    hilbert_XI4_right_angle_swap
      (PlaneGeo Geo pi)
      Pp Fp Gp
      hRightPFGData.1
      hRightPFGData.2

  ----------------------------------------------------------------------
  -- Right angle at G in triangle FGP.
  ----------------------------------------------------------------------

  have hRightPGFData :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo pi)
      mp qp
      Gp
      Pp Fp
      (hilbert_linesPerpendicularAt_ne
        (PlaneGeo Geo pi)
        mp qp Gp hMperpQPlane)
      hMperpQPlane
      hPGp
      hFGp
      hPm
      hFq

  have hRightFGP :
      HilbertRightAngle
        (PlaneGeo Geo pi)
        Fp Gp Pp :=
    hilbert_XI4_right_angle_swap
      (PlaneGeo Geo pi)
      Pp Gp Fp
      hRightPGFData.1
      hRightPGFData.2

  ----------------------------------------------------------------------
  -- Triangle FGP cannot have two right angles.
  ----------------------------------------------------------------------

  have hFGP :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Fp Gp Pp) := by

    intro hColPlane

    have hColAmbient :
        PrimCollinear Geo F G P :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi Fp Gp Pp
        hColPlane

    have hColPFG :
        PrimCollinear Geo P F G :=
      PrimCollinearCycle
        Geo G P F
        (PrimCollinearCycle
          Geo F G P hColAmbient)

    exact hPFG hColPFG

  exact
    i47_aux_two_right_angles_impossible
      (PlaneGeo Geo pi)
      Fp Gp Pp
      hFGP
      hRightGFP
      hRightFGP

end Geometry

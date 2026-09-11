import CGJteamLab.Coxeter.E4NormalSectionNormal

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Dimension-corrected symmetry of ambient line-line perpendicularity in E4.

The witness points carried by `HilbertLinesPerpendicularAt` determine an
ambient 2-plane.  Symmetry is proved only inside that `PlaneGeo`, where
the corrected E4 order/congruence layers reconstruct ordinary Hilbert
congruence.
-/
theorem hilbert4D_linesPerpendicularAt_symm_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (l m : Geo.Line)
    (O : Geo.Point)
    (hPerp :
      HilbertLinesPerpendicularAt Geo l m O) :
    HilbertLinesPerpendicularAt Geo m l O := by

  rcases hPerp with
    ⟨hOl, hOm,
     A, B,
     hAO, hBO,
     hAl, hBm,
     hNon,
     hRight⟩

  rcases
      H4I.plane_through
        A O B hNon with
    ⟨pi, hApi, hOpi, hBpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    H4I.line_in_plane
      A O hAO
      l hAl hOl
      pi hApi hOpi

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    H4I.line_in_plane
      B O hBO
      m hBm hOm
      pi hBpi hOpi

  let lp : PlaneLine Geo pi :=
    ⟨l, hlpi⟩

  let mp : PlaneLine Geo pi :=
    ⟨m, hmpi⟩

  let Op : PlanePoint Geo pi :=
    ⟨O, hOpi⟩

  have hPerpLocal :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) lp mp Op :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi lp mp Op).mpr
      ⟨hOl, hOm,
       A, B,
       hAO, hBO,
       hAl, hBm,
       hNon,
       hRight⟩

  have hPerpLocalSwap :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) mp lp Op :=
    @hilbert_linesPerpendicularAt_symm_neutral
      (PlaneGeo Geo pi)
      (inferInstance : HilbertIncidence (PlaneGeo Geo pi))
      (planeGeoHilbertCongruence4_corrected
        (Geo := Geo)
        pi
        A O B
        hApi hOpi hBpi
        hNon)
      lp mp Op
      hPerpLocal

  exact
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi mp lp Op).mp
      hPerpLocalSwap


/-!
# Ambient E4 version of Euclid XI.4

The classical production theorem `euclid_proposition_11_4` is stated for
a genuinely 3-dimensional ambient geometry.

In E4 we recover the same conclusion for an arbitrary ambient 2-plane by
localizing the configuration in one 3-hyperplane and applying XI.4 there.

No new axiom is introduced.  In particular this theorem does not assume

* `Hilbert4DHyperplanePerpendicularFrameCriterion_corrected`;
* `Hilbert4DNormalFromExternalPointExistence_corrected`.

It needs only the corrected E4 incidence/order/congruence layers.
-/

/--
Dimension-corrected ambient E4 analogue of Euclid XI.4.

If `s` and `t` are two distinct lines of the plane `N` through `O`, and
`l` is perpendicular at `O` to both, then `l` is perpendicular to the
whole plane `N` at `O`.
-/
theorem hilbert4D_XI4_line_perpendicular_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (N : Q.toHilbertSpacePrimitive.Plane)
    (s t l : Geo.Line)
    (O : Geo.Point)
    (hON :
      Q.toHilbertSpacePrimitive.OnPlane O N)
    (hsN :
      HilbertLineInPlane Geo s N)
    (htN :
      HilbertLineInPlane Geo t N)
    (hOs : H.OnLine O s)
    (hOt : H.OnLine O t)
    (hst : Ne s t)
    (hOl : H.OnLine O l)
    (hLS :
      HilbertLinesPerpendicularAt Geo l s O)
    (hLT :
      HilbertLinesPerpendicularAt Geo l t O) :
    HilbertLinePerpendicularPlaneAt
      Geo l N O := by

  have hSL :
      HilbertLinesPerpendicularAt Geo s l O :=
    hilbert4D_linesPerpendicularAt_symm_corrected
      (Geo := Geo)
      l s O
      hLS

  have hTL :
      HilbertLinesPerpendicularAt Geo t l O :=
    hilbert4D_linesPerpendicularAt_symm_corrected
      (Geo := Geo)
      l t O
      hLT

  have hlNotN :
      Not (HilbertLineInPlane Geo l N) :=
    hilbert4D_normal_section_transverse_line_not_in_plane_corrected
      (Geo := Geo)
      N
      s t l
      O
      hON
      hsN htN
      hOs hOt
      hst
      hSL hTL

  rcases
      hilbert4D_plane_and_transverse_line_common_hyperplane_corrected
        (Geo := Geo)
        N
        s t l
        O
        hON
        hsN htN
        hOs hOt
        hst
        hOl
        hlNotN with
    ⟨Lambda, hNLambda, hlLambda⟩

  have hsLambda :
      HilbertLineInHyperplane4 Geo s Lambda := by
    intro X hXs
    exact hNLambda X (hsN X hXs)

  have htLambda :
      HilbertLineInHyperplane4 Geo t Lambda := by
    intro X hXt
    exact hNLambda X (htN X hXt)

  have hOLambda :
      Q.OnHyperplane O Lambda :=
    hNLambda O hON

  let lL : HyperplaneLine4 Geo Lambda :=
    ⟨l, hlLambda⟩

  let sL : HyperplaneLine4 Geo Lambda :=
    ⟨s, hsLambda⟩

  let tL : HyperplaneLine4 Geo Lambda :=
    ⟨t, htLambda⟩

  let NL : HyperplanePlane4 Geo Lambda :=
    ⟨N, hNLambda⟩

  let OL : HyperplanePoint4 Geo Lambda :=
    ⟨O, hOLambda⟩

  have hsNL :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Lambda)
        sL NL := by
    intro X hXs
    exact hsN X.1 hXs

  have htNL :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Lambda)
        tL NL := by
    intro X hXt
    exact htN X.1 hXt

  let sNL :
      PlaneLine
        (HyperplaneGeo4 Geo Lambda)
        NL :=
    ⟨sL, hsNL⟩

  let tNL :
      PlaneLine
        (HyperplaneGeo4 Geo Lambda)
        NL :=
    ⟨tL, htNL⟩

  let ONL :
      PlanePoint
        (HyperplaneGeo4 Geo Lambda)
        NL :=
    ⟨OL, hON⟩

  have hstLocal :
      Ne sNL tNL := by
    intro hEq
    apply hst
    exact
      congrArg
        (fun q :
          PlaneLine
            (HyperplaneGeo4 Geo Lambda)
            NL =>
          q.1.1)
        hEq

  have hLSLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        lL sL OL :=
    hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
      (Geo := Geo)
      Lambda
      lL sL OL
      hLS

  have hLTLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        lL tL OL :=
    hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
      (Geo := Geo)
      Lambda
      lL tL OL
      hLT

  have hPerpPlaneLocal :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Lambda)
        lL NL OL :=
    euclid_proposition_11_4
      (Geo := HyperplaneGeo4 Geo Lambda)
      NL
      sNL tNL
      lL
      ONL
      hstLocal
      hLSLocal
      hLTLocal

  refine
    ⟨hOl, hON, ?_⟩

  intro m hmN hOm

  have hmLambda :
      HilbertLineInHyperplane4 Geo m Lambda := by
    intro X hXm
    exact hNLambda X (hmN X hXm)

  let mL : HyperplaneLine4 Geo Lambda :=
    ⟨m, hmLambda⟩

  have hmNL :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Lambda)
        mL NL := by
    intro X hXm
    exact hmN X.1 hXm

  have hPerpLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        lL mL OL :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := HyperplaneGeo4 Geo Lambda)
      hPerpPlaneLocal
      hmNL
      hOm

  exact
    hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
      (Geo := Geo)
      Lambda
      lL mL OL
      hPerpLocal

end Geometry

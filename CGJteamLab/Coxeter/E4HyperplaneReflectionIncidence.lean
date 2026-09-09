import CGJteamLab.Coxeter.E4HyperplaneReflectionCarrierCandidate
import CGJteamLab.Coxeter.CoxeterRelations

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection: incidence layer

The corrected E4 reflection is already known to preserve segment
congruence globally.  This module begins the incidence transport needed
for hyperplane carrier conjugation.

The main result is:

  hyperplaneReflect4_corrected_preserves_collinear

The proof deliberately does not install an ambient `HilbertCongruence Geo`.

For a nontrivial collinear triple, choose a carrier line q and one point
P of q outside the mirror Sigma.  The Sigma-normal l through P and q lie
in one dimension-free Smith plane pi.  Since pi contains a Sigma-normal,
the corrected reflection preserves pi.  Inside `PlaneGeo Geo pi` the
ambient reflection is exactly an ordinary line reflection in the trace
pi cap Sigma, so the existing planar theorem
`lineReflect_preserves_collinear` applies.
-/

/-! ## Dimension-free carrier helper -/

/--
Two ambient lines with a common point lie in a common plane.

This is the dimension-free incidence content of Euclid XI.2.  It is
proved from Smith I1-I3; no ambient 3D incidence class is used.
-/
theorem hilbert_dimension_free_plane_through_intersecting_lines
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    (q l : Geo.Line)
    (P : Geo.Point)
    (hPq : H.OnLine P q)
    (hPl : H.OnLine P l) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo q pi /\
      HilbertLineInPlane Geo l pi := by

  by_cases hql :
      q = l

  case pos =>
    have hABExists :=
      D.two_points_on_each_line q

    let A : Geo.Point :=
      Classical.choose hABExists

    have hBExists :=
      Classical.choose_spec hABExists

    let B : Geo.Point :=
      Classical.choose hBExists

    have hABData :=
      Classical.choose_spec hBExists

    have hAB :
        Ne A B :=
      hABData.1

    have hAq :
        H.OnLine A q :=
      hABData.2.1

    have hBq :
        H.OnLine B q :=
      hABData.2.2

    have hRExists :=
      hilbert_point_off_line
        (Geo := Geo)
        q

    let R : Geo.Point :=
      Classical.choose hRExists

    have hRq :
        Not (H.OnLine R q) :=
      Classical.choose_spec hRExists

    have hABR :
        Not (PrimCollinear Geo A B R) := by

      intro hCol

      have hRonq :
          H.OnLine R q :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hAB
          hAq hBq
          hCol

      exact hRq hRonq

    have hPiExists :=
      D.plane_through
        A B R hABR

    let pi : S.Plane :=
      Classical.choose hPiExists

    have hPiData :=
      Classical.choose_spec hPiExists

    have hApi :
        S.OnPlane A pi :=
      hPiData.1

    have hBpi :
        S.OnPlane B pi :=
      hPiData.2.1

    have hqpi :
        HilbertLineInPlane Geo q pi :=
      D.line_in_plane
        A B hAB
        q hAq hBq
        pi hApi hBpi

    have hlpi :
        HilbertLineInPlane Geo l pi := by
      rw [<- hql]
      exact hqpi

    exact
      Exists.intro pi
        (And.intro hqpi hlpi)

  case neg =>
    have hUVExists :=
      D.two_points_on_each_line l

    let U : Geo.Point :=
      Classical.choose hUVExists

    have hVExists :=
      Classical.choose_spec hUVExists

    let V : Geo.Point :=
      Classical.choose hVExists

    have hUVData :=
      Classical.choose_spec hVExists

    have hUV :
        Ne U V :=
      hUVData.1

    have hUl :
        H.OnLine U l :=
      hUVData.2.1

    have hVl :
        H.OnLine V l :=
      hUVData.2.2

    have hGExists :
        exists G : Geo.Point,
          Ne P G /\
          H.OnLine G l := by

      by_cases hPU :
          P = U

      case pos =>
        refine
          Exists.intro V
            (And.intro ?_ hVl)

        intro hPV
        apply hUV
        exact hPU.symm.trans hPV

      case neg =>
        exact
          Exists.intro U
            (And.intro hPU hUl)

    let G : Geo.Point :=
      Classical.choose hGExists

    have hGData :=
      Classical.choose_spec hGExists

    have hPG :
        Ne P G :=
      hGData.1

    have hGl :
        H.OnLine G l :=
      hGData.2

    have hGnotq :
        Not (H.OnLine G q) := by

      intro hGq

      have hql' :
          q = l :=
        HilbertPlaneIncidence.line_unique
          (Geo := Geo)
          P G hPG
          q l
          hPq hGq
          hPl hGl

      exact hql hql'

    let : SmithIncidenceCore Geo :=
      smithIncidenceCore_of_dimensionFree
        (Geo := Geo)

    have hPiExists :=
      smithCore_plane_through_line_and_external_point
        (Geo := Geo)
        q G hGnotq

    let pi : S.Plane :=
      Classical.choose hPiExists

    have hPiData :=
      Classical.choose_spec hPiExists

    have hqpi :
        HilbertLineInPlane Geo q pi :=
      hPiData.1

    have hGpi :
        S.OnPlane G pi :=
      hPiData.2

    have hPpi :
        S.OnPlane P pi :=
      hqpi P hPq

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      D.line_in_plane
        P G hPG
        l hPl hGl
        pi hPpi hGpi

    exact
      Exists.intro pi
        (And.intro hqpi hlpi)


/-! ## Tiny collinearity helper -/

/--
If the first two points coincide, the triple is collinear.
-/
theorem primCollinear_of_eq_first_second_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C : Geo.Point)
    (hAB : A = B) :
    PrimCollinear Geo A B C := by

  subst B

  by_cases hAC :
      A = C

  case pos =>
    subst C

    have hXExists :=
      smithCore_exists_point_ne
        (Geo := Geo)
        A

    let X : Geo.Point :=
      Classical.choose hXExists

    have hXA :
        Ne X A :=
      Classical.choose_spec hXExists

    have hAX :
        Ne A X :=
      hXA.symm

    have hLineExists :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A X hAX

    let q : Geo.Line :=
      Classical.choose hLineExists

    have hqData :=
      Classical.choose_spec hLineExists

    exact
      Exists.intro q
        (And.intro hqData.1
          (And.intro hqData.1 hqData.1))

  case neg =>
    have hLineExists :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A C hAC

    let q : Geo.Line :=
      Classical.choose hLineExists

    have hqData :=
      Classical.choose_spec hLineExists

    exact
      Exists.intro q
        (And.intro hqData.1
          (And.intro hqData.1 hqData.2))


/-! ## Collinearity in a preserved normal slice -/

/--
If A,B,C lie on one line q and q contains a point P outside Sigma, then
the corrected hyperplane reflection sends A,B,C to a collinear triple.
-/
theorem hyperplaneReflect4_corrected_preserves_collinear_of_off_point_on_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (q : Geo.Line)
    (A B C P : Geo.Point)
    (hAB : Ne A B)
    (hAq : H.OnLine A q)
    (hBq : H.OnLine B q)
    (hCq : H.OnLine C q)
    (hPq : H.OnLine P q)
    (hPoff :
      Not (Q.OnHyperplane P Sigma)) :
    PrimCollinear
      Geo
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C) := by

  have hFootExists :=
    hyperplaneReflect4_corrected_off_hyperplane_data
      (Geo := Geo)
      Sigma P hPoff

  let F : Geo.Point :=
    Classical.choose hFootExists

  have hFootData :=
    Classical.choose_spec hFootExists

  have hPerp :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P :=
    hFootData.1

  let l : Geo.Line :=
    Classical.choose hPerp

  have hLData :=
    Classical.choose_spec hPerp

  have hPl :
      H.OnLine P l :=
    hLData.1

  have hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F :=
    hLData.2

  have hPiExists :=
    hilbert_dimension_free_plane_through_intersecting_lines
      (Geo := Geo)
      q l P
      hPq hPl

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hPiExists

  have hPiData :=
    Classical.choose_spec hPiExists

  have hqpi :
      HilbertLineInPlane Geo q pi :=
    hPiData.1

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    hPiData.2

  have hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi :=
    hqpi A hAq

  have hBpi :
      Q.toHilbertSpacePrimitive.OnPlane B pi :=
    hqpi B hBq

  have hCpi :
      Q.toHilbertSpacePrimitive.OnPlane C pi :=
    hqpi C hCq

  have hFpi :
      Q.toHilbertSpacePrimitive.OnPlane F pi :=
    hlpi F hNormal.1

  have hA'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma A)
        pi :=
    hyperplaneReflect4_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      A hApi

  have hB'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma B)
        pi :=
    hyperplaneReflect4_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      B hBpi

  have hC'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma C)
        pi :=
    hyperplaneReflect4_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma pi F l
      hlpi hNormal
      C hCpi

  have hMarkedExists :=
    D.three_noncollinear_on_plane pi

  let U : Geo.Point :=
    Classical.choose hMarkedExists

  have hVExists :=
    Classical.choose_spec hMarkedExists

  let V : Geo.Point :=
    Classical.choose hVExists

  have hWExists :=
    Classical.choose_spec hVExists

  let W : Geo.Point :=
    Classical.choose hWExists

  have hMarkedData :=
    Classical.choose_spec hWExists

  have hUpi :
      Q.toHilbertSpacePrimitive.OnPlane U pi :=
    hMarkedData.1

  have hVpi :
      Q.toHilbertSpacePrimitive.OnPlane V pi :=
    hMarkedData.2.1

  have hWpi :
      Q.toHilbertSpacePrimitive.OnPlane W pi :=
    hMarkedData.2.2.1

  have hUVW :
      Not (PrimCollinear Geo U V W) :=
    hMarkedData.2.2.2

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi
      U V W
      hUpi hVpi hWpi
      hUVW

  have hTraceExists :=
    hilbert4D_normal_plane_intersection_line
      (Geo := Geo)
      hNormal pi hlpi

  let s : Geo.Line :=
    Classical.choose hTraceExists

  have hTraceData :=
    Classical.choose_spec hTraceExists

  have hFs :
      H.OnLine F s :=
    hTraceData.1

  have hspi :
      HilbertLineInPlane Geo s pi :=
    hTraceData.2.1

  have hTrace :
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X pi /\
         Q.OnHyperplane X Sigma) <->
          H.OnLine X s :=
    hTraceData.2.2.2

  have hSTExists :=
    D.two_points_on_each_line s

  let S0 : Geo.Point :=
    Classical.choose hSTExists

  have hTExists :=
    Classical.choose_spec hSTExists

  let T0 : Geo.Point :=
    Classical.choose hTExists

  have hSTData :=
    Classical.choose_spec hTExists

  have hST :
      Ne S0 T0 :=
    hSTData.1

  have hS0s :
      H.OnLine S0 s :=
    hSTData.2.1

  have hT0s :
      H.OnLine T0 s :=
    hSTData.2.2

  have hS0pi :
      Q.toHilbertSpacePrimitive.OnPlane S0 pi :=
    hspi S0 hS0s

  have hT0pi :
      Q.toHilbertSpacePrimitive.OnPlane T0 pi :=
    hspi T0 hT0s

  let Sp : PlanePoint Geo pi :=
    Subtype.mk S0 hS0pi

  let Tp : PlanePoint Geo pi :=
    Subtype.mk T0 hT0pi

  let sp : PlaneLine Geo pi :=
    Subtype.mk s hspi

  have hSTp :
      Ne Sp Tp := by

    intro hEq
    apply hST
    exact
      congrArg Subtype.val hEq

  let axis :
      ReflectionAxis (PlaneGeo Geo pi) :=
    {
      carrier := sp
      A := Sp
      B := Tp
      hAB := hSTp
      hA := hS0s
      hB := hT0s
    }

  let Ap : PlanePoint Geo pi :=
    Subtype.mk A hApi

  let Bp : PlanePoint Geo pi :=
    Subtype.mk B hBpi

  let Cp : PlanePoint Geo pi :=
    Subtype.mk C hCpi

  let Ap' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma A)
      hA'pi

  let Bp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma B)
      hB'pi

  let Cp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma C)
      hC'pi

  have hABp :
      Ne Ap.1 Bp.1 :=
    hAB

  have hABCplane :
      PrimCollinear
        (PlaneGeo Geo pi)
        Ap Bp Cp :=
    planeGeo_primCollinear_of_ambient_of_ne4_corrected
      (Geo := Geo)
      pi
      Ap Bp Cp
      hABp
      (Exists.intro q
        (And.intro hAq
          (And.intro hBq hCq)))

  have hEqReflection :
      forall X : Geo.Point,
        forall hXpi :
          Q.toHilbertSpacePrimitive.OnPlane X pi,
        forall hX'pi :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma X)
            pi,
        lineReflect
            (PlaneGeo Geo pi)
            axis
            (Subtype.mk X hXpi) =
          (Subtype.mk
            (hyperplaneReflect4_corrected Geo Sigma X)
            hX'pi :
            PlanePoint Geo pi) := by

    intro X hXpi hX'pi

    let Xp : PlanePoint Geo pi :=
      Subtype.mk X hXpi

    let Xp' : PlanePoint Geo pi :=
      Subtype.mk
        (hyperplaneReflect4_corrected Geo Sigma X)
        hX'pi

    have hRestricted :
        IsLineReflection
          (PlaneGeo Geo pi)
          axis Xp Xp' :=
      hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
        (Geo := Geo)
        (N := pi)
        Sigma F
        l s
        hlpi
        hNormal
        hspi
        hTrace
        axis
        rfl
        Xp Xp'
        (hyperplaneReflect4_corrected_spec
          (Geo := Geo)
          Sigma X)

    have hCanonical :
        IsLineReflection
          (PlaneGeo Geo pi)
          axis Xp
          (lineReflect
            (PlaneGeo Geo pi)
            axis Xp) :=
      lineReflect_spec
        (PlaneGeo Geo pi)
        axis Xp

    exact
      line_reflection_unique
        (PlaneGeo Geo pi)
        axis
        Xp
        (lineReflect
          (PlaneGeo Geo pi)
          axis Xp)
        Xp'
        hCanonical
        hRestricted

  have hEqA :
      lineReflect
          (PlaneGeo Geo pi)
          axis Ap =
        Ap' := by
    exact
      hEqReflection
        A hApi hA'pi

  have hEqB :
      lineReflect
          (PlaneGeo Geo pi)
          axis Bp =
        Bp' := by
    exact
      hEqReflection
        B hBpi hB'pi

  have hEqC :
      lineReflect
          (PlaneGeo Geo pi)
          axis Cp =
        Cp' := by
    exact
      hEqReflection
        C hCpi hC'pi

  have hImagePlane :
      PrimCollinear
        (PlaneGeo Geo pi)
        (lineReflect (PlaneGeo Geo pi) axis Ap)
        (lineReflect (PlaneGeo Geo pi) axis Bp)
        (lineReflect (PlaneGeo Geo pi) axis Cp) :=
    lineReflect_preserves_collinear
      (PlaneGeo Geo pi)
      axis
      Ap Bp Cp
      hABCplane

  have hImagePlane' :
      PrimCollinear
        (PlaneGeo Geo pi)
        Ap' Bp' Cp' := by

    rw [<- hEqA, <- hEqB, <- hEqC]
    exact hImagePlane

  have hAmbient :=
    planeGeo_primCollinear_to_ambient
      (Geo := Geo)
      pi
      Ap' Bp' Cp'
      hImagePlane'

  exact hAmbient


/-! ## Global corrected E4 collinearity preservation -/

/--
Corrected E4 hyperplane reflection preserves ambient collinearity.
-/
theorem hyperplaneReflect4_corrected_preserves_collinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A B C : Geo.Point)
    (hABC :
      PrimCollinear Geo A B C) :
    PrimCollinear
      Geo
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C) := by

  by_cases hAB :
      A = B

  case pos =>
    have hImageEq :
        hyperplaneReflect4_corrected Geo Sigma A =
          hyperplaneReflect4_corrected Geo Sigma B :=
      congrArg
        (hyperplaneReflect4_corrected Geo Sigma)
        hAB

    exact
      primCollinear_of_eq_first_second_corrected
        (Geo := Geo)
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma C)
        hImageEq

  case neg =>
    have hQExists :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB

    let q : Geo.Line :=
      Classical.choose hQExists

    have hQData :=
      Classical.choose_spec hQExists

    have hAq :
        H.OnLine A q :=
      hQData.1

    have hBq :
        H.OnLine B q :=
      hQData.2

    have hCq :
        H.OnLine C q :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAB
        hAq hBq
        hABC

    by_cases hASigma :
        Q.OnHyperplane A Sigma

    case neg =>
      exact
        hyperplaneReflect4_corrected_preserves_collinear_of_off_point_on_line
          (Geo := Geo)
          Sigma q
          A B C A
          hAB
          hAq hBq hCq
          hAq
          hASigma

    case pos =>
      by_cases hBSigma :
          Q.OnHyperplane B Sigma

      case neg =>
        exact
          hyperplaneReflect4_corrected_preserves_collinear_of_off_point_on_line
            (Geo := Geo)
            Sigma q
            A B C B
            hAB
            hAq hBq hCq
            hBq
            hBSigma

      case pos =>
        have hqSigma :
            HilbertLineInHyperplane4
              Geo q Sigma :=
          C4.line_in_hyperplane
            A B hAB
            q hAq hBq
            Sigma
            hASigma hBSigma

        have hCSigma :
            Q.OnHyperplane C Sigma :=
          hqSigma C hCq

        have hFixA :
            hyperplaneReflect4_corrected Geo Sigma A = A :=
          hyperplaneReflect4_corrected_of_on_hyperplane
            (Geo := Geo)
            Sigma A hASigma

        have hFixB :
            hyperplaneReflect4_corrected Geo Sigma B = B :=
          hyperplaneReflect4_corrected_of_on_hyperplane
            (Geo := Geo)
            Sigma B hBSigma

        have hFixC :
            hyperplaneReflect4_corrected Geo Sigma C = C :=
          hyperplaneReflect4_corrected_of_on_hyperplane
            (Geo := Geo)
            Sigma C hCSigma

        rw [hFixA, hFixB, hFixC]

        exact hABC


/--
Because corrected hyperplane reflection is involutive, it also preserves
noncollinearity.
-/
theorem hyperplaneReflect4_corrected_preserves_noncollinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (A B C : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C)) :
    Not
      (PrimCollinear
        Geo
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma C)) := by

  intro hImage

  have hBack :
      PrimCollinear
        Geo
        (hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma A))
        (hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma B))
        (hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma C)) :=
    hyperplaneReflect4_corrected_preserves_collinear
      (Geo := Geo)
      Sigma
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C)
      hImage

  rw [
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo) Sigma A,
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo) Sigma B,
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo) Sigma C
  ] at hBack

  exact hABC hBack

end Geometry

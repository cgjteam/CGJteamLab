import CGJteamLab.Coxeter.E4NormalSection
import CGJteamLab.Proposition11_6

/-!
# Corrected E4 normal parallelism

Production promotion of:
* the common 3-hyperplane for distinct-foot normals;
* a common ambient plane for two hyperplanes through two points;
* dimension-safe E4 line parallelism;
* localized Euclid XI.6 for normals to one E4 hyperplane.

No historical test module is imported.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: a common 3-hyperplane for two distinct-foot normals

To apply Euclid XI.6 dimension-correctly to two normals of the same
ambient E4 hyperplane, we first need a genuine 3-dimensional carrier
containing both normal lines.

This file proves that carrier-existence statement synthetically.

Let l,m be normals to Sigma at distinct feet F,G.

* choose A on l with A != F;
* G cannot lie on l, because then l would contain two distinct points
  of Sigma and hence lie in Sigma, contradicting normality;
* therefore A,F,G are noncollinear and determine a plane rho;
* choose B on m with B != G;
* if B is outside rho, the four noncoplanar points A,F,G,B determine
  a hyperplane Lambda containing l and m;
* if B lies in rho, choose D in Sigma outside rho using the internal
  3-dimensionality of Sigma; then A,F,G,D determine Lambda, and rho
  lies in Lambda, hence so do l and m.

No old ambient HilbertSpaceIncidence is used.
-/

/--
Inside a genuinely 3-dimensional E4 hyperplane Sigma, every ambient
2-plane misses at least one point of Sigma.
-/
theorem hilbert4D_hyperplane_point_off_plane_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (rho : Q.toHilbertSpacePrimitive.Plane) :
    exists D : Geo.Point,
      Q.OnHyperplane D Sigma /\
      Not (Q.toHilbertSpacePrimitive.OnPlane D rho) := by

  rcases
      H4L.four_noncoplanar_on_hyperplane Sigma with
    ⟨A, B, C, D,
     hASigma, hBSigma, hCSigma, hDSigma,
     hNoncop⟩

  by_cases hArho :
      Q.toHilbertSpacePrimitive.OnPlane A rho

  · by_cases hBrho :
        Q.toHilbertSpacePrimitive.OnPlane B rho

    · by_cases hCrho :
          Q.toHilbertSpacePrimitive.OnPlane C rho

      · by_cases hDrho :
            Q.toHilbertSpacePrimitive.OnPlane D rho

        · exact
            False.elim
              (hNoncop
                ⟨rho,
                 hArho,
                 hBrho,
                 hCrho,
                 hDrho⟩)

        · exact
            ⟨D, hDSigma, hDrho⟩

      · exact
          ⟨C, hCSigma, hCrho⟩

    · exact
        ⟨B, hBSigma, hBrho⟩

  · exact
      ⟨A, hASigma, hArho⟩

/--
Two corrected E4 normals to the same hyperplane at distinct feet lie
in one ambient 3-hyperplane.
-/
theorem hilbert4D_distinct_foot_normals_common_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (l m : Geo.Line)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G) :
    exists Lambda : Q.Hyperplane,
      HilbertLineInHyperplane4 Geo l Lambda /\
      HilbertLineInHyperplane4 Geo m Lambda := by

  have hFl :
      H.OnLine F l :=
    hLNormal.1

  have hGm :
      H.OnLine G m :=
    hMNormal.1

  have hFSigma :
      Q.OnHyperplane F Sigma :=
    hLNormal.2.1

  have hGSigma :
      Q.OnHyperplane G Sigma :=
    hMNormal.2.1

  ----------------------------------------------------------------------
  -- G is not on l.
  ----------------------------------------------------------------------

  have hGnotl :
      Not (H.OnLine G l) := by

    intro hGl

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
  -- Pick A on l, A != F. Then A,F,G are noncollinear.
  ----------------------------------------------------------------------

  rcases
      hilbert4D_other_point_on_line_corrected
        (Geo := Geo)
        l F with
    ⟨A, hAF, hAl⟩

  have hAFG :
      Not (PrimCollinear Geo A F G) := by

    intro hCol

    have hGl :
        H.OnLine G l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAF
        hAl hFl
        hCol

    exact hGnotl hGl

  rcases
      H4I.plane_through
        A F G hAFG with
    ⟨rho, hArho, hFrho, hGrho⟩

  have hlrho :
      HilbertLineInPlane Geo l rho :=
    H4I.line_in_plane
      A F hAF
      l hAl hFl
      rho hArho hFrho

  ----------------------------------------------------------------------
  -- Pick B on m, B != G.
  ----------------------------------------------------------------------

  rcases
      hilbert4D_other_point_on_line_corrected
        (Geo := Geo)
        m G with
    ⟨B, hBG, hBm⟩

  by_cases hBrho :
      Q.toHilbertSpacePrimitive.OnPlane B rho

  ----------------------------------------------------------------------
  -- Coplanar case: both lines already lie in rho.
  ----------------------------------------------------------------------

  · have hmrho :
        HilbertLineInPlane Geo m rho :=
      H4I.line_in_plane
        B G hBG
        m hBm hGm
        rho hBrho hGrho

    rcases
        hilbert4D_hyperplane_point_off_plane_corrected
          (Geo := Geo)
          Sigma rho with
      ⟨D, hDSigma, hDoffrho⟩

    have hAFGD :
        Not (HilbertCoplanar4 Geo A F G D) :=
      hilbert4D_noncoplanar_of_off_plane_through_three_corrected
        (Geo := Geo)
        A F G D
        rho
        hAFG
        hArho hFrho hGrho
        hDoffrho

    rcases
        H4I.hyperplane_through
          A F G D hAFGD with
      ⟨Lambda,
       hALambda,
       hFLambda,
       hGLambda,
       hDLambda⟩

    have hrhoLambda :
        HilbertPlaneInHyperplane4 Geo rho Lambda :=
      H4L.plane_in_hyperplane
        A F G hAFG
        rho
        hArho hFrho hGrho
        Lambda
        hALambda hFLambda hGLambda

    have hlLambda :
        HilbertLineInHyperplane4 Geo l Lambda := by
      intro X hXl
      exact
        hrhoLambda X (hlrho X hXl)

    have hmLambda :
        HilbertLineInHyperplane4 Geo m Lambda := by
      intro X hXm
      exact
        hrhoLambda X (hmrho X hXm)

    exact
      ⟨Lambda, hlLambda, hmLambda⟩

  ----------------------------------------------------------------------
  -- Noncoplanar case: A,F,G,B directly determine Lambda.
  ----------------------------------------------------------------------

  · have hAFGB :
        Not (HilbertCoplanar4 Geo A F G B) :=
      hilbert4D_noncoplanar_of_off_plane_through_three_corrected
        (Geo := Geo)
        A F G B
        rho
        hAFG
        hArho hFrho hGrho
        hBrho

    rcases
        H4I.hyperplane_through
          A F G B hAFGB with
      ⟨Lambda,
       hALambda,
       hFLambda,
       hGLambda,
       hBLambda⟩

    have hlLambda :
        HilbertLineInHyperplane4 Geo l Lambda :=
      H4I.line_in_hyperplane
        A F hAF
        l hAl hFl
        Lambda
        hALambda hFLambda

    have hmLambda :
        HilbertLineInHyperplane4 Geo m Lambda :=
      H4I.line_in_hyperplane
        B G hBG
        m hBm hGm
        Lambda
        hBLambda hGLambda

    exact
      ⟨Lambda, hlLambda, hmLambda⟩

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: a common plane of two hyperplanes through two common points

Test73 put two distinct-foot normals into one ambient 3-hyperplane
Lambda.  To apply XI.6 inside Lambda we still need a 2-plane contained
in both Sigma and Lambda and passing through the two feet F,G.

This file derives exactly that incidence fact from the corrected E4
plane-hyperplane intersection clause.

The key auxiliary fact is purely local 3D:

given distinct points F,G of one hyperplane Sigma, there is an internal
plane of Sigma through F but avoiding G.

Intersect that plane with another ambient hyperplane Lambda through F.
The corrected E4 plane-hyperplane clause gives a second common point C.
Because the chosen plane avoids G, C cannot lie on FG.  Hence F,G,C are
noncollinear and determine a 2-plane rho contained in both hyperplanes.
-/

/--
Inside one corrected E4 hyperplane, through F there is an internal plane
which avoids any prescribed distinct point G.
-/
theorem hyperplaneGeo4_plane_through_point_avoiding_point_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (F G : HyperplanePoint4 Geo Sigma)
    (hFG : Ne F G) :
    exists pi : HyperplanePlane4 Geo Sigma,
      HyperplaneOnPlane4 Geo F pi /\
      Not (HyperplaneOnPlane4 Geo G pi) := by

  ----------------------------------------------------------------------
  -- q = FG and C off q.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := HyperplaneGeo4 Geo Sigma)
        F G hFG with
    ⟨q, hFq, hGq⟩

  rcases
      hilbert_point_off_line
        (Geo := HyperplaneGeo4 Geo Sigma)
        q with
    ⟨C, hCq⟩

  have hFGC :
      Not
        (PrimCollinear
          (HyperplaneGeo4 Geo Sigma)
          F G C) :=
    hilbert_not_collinear_of_off_line
      (HyperplaneGeo4 Geo Sigma)
      F G C q
      hFG
      hFq hGq hCq

  ----------------------------------------------------------------------
  -- pi0 = plane(F,G,C), then choose D outside pi0.
  ----------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := HyperplaneGeo4 Geo Sigma)
        F G C hFGC with
    ⟨pi0, hFpi0, hGpi0, hCpi0⟩

  rcases
      hilbert_point_off_plane
        (Geo := HyperplaneGeo4 Geo Sigma)
        pi0 with
    ⟨D, hDpi0⟩

  have hFD : Ne F D := by
    intro hEq
    apply hDpi0
    rw [← hEq]
    exact hFpi0

  ----------------------------------------------------------------------
  -- r = FD.  C is not on r, otherwise D would return to pi0.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := HyperplaneGeo4 Geo Sigma)
        F D hFD with
    ⟨r, hFr, hDr⟩

  have hFC : Ne F C := by
    intro hEq
    apply hCq
    rw [← hEq]
    exact hFq

  have hCr :
      Not
        (HilbertIncidence.OnLine C r) := by

    intro hCr

    have hrPi0 :
        HilbertLineInPlane
          (HyperplaneGeo4 Geo Sigma)
          r pi0 :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := HyperplaneGeo4 Geo Sigma)
        F C hFC
        r hFr hCr
        pi0 hFpi0 hCpi0

    exact
      hDpi0
        (hrPi0 D hDr)

  ----------------------------------------------------------------------
  -- pi1 = plane(r,C).  It contains F,D,C but cannot contain G.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := HyperplaneGeo4 Geo Sigma)
        r C hCr with
    ⟨pi1, hrPi1, hCpi1, _hUniquePi1⟩

  have hFpi1 :
      HyperplaneOnPlane4 Geo F pi1 :=
    hrPi1 F hFr

  have hDpi1 :
      HyperplaneOnPlane4 Geo D pi1 :=
    hrPi1 D hDr

  have hGnotPi1 :
      Not (HyperplaneOnPlane4 Geo G pi1) := by

    intro hGpi1

    have hEq :
        pi0 = pi1 :=
      HilbertSpaceIncidence.plane_unique
        (Geo := HyperplaneGeo4 Geo Sigma)
        F G C
        hFGC
        pi0 pi1
        hFpi0 hGpi0 hCpi0
        hFpi1 hGpi1 hCpi1

    apply hDpi0

    rw [hEq]

    exact hDpi1

  exact
    ⟨pi1, hFpi1, hGnotPi1⟩

/--
Two corrected E4 hyperplanes containing two distinct common points
contain a common ambient 2-plane through those points.

This is the dimension-4 incidence fact needed to localize XI.6.
-/
theorem hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    (Sigma Lambda : Q.Hyperplane)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hFSigma : Q.OnHyperplane F Sigma)
    (hGSigma : Q.OnHyperplane G Sigma)
    (hFLambda : Q.OnHyperplane F Lambda)
    (hGLambda : Q.OnHyperplane G Lambda) :
    exists rho : Q.toHilbertSpacePrimitive.Plane,
      Q.toHilbertSpacePrimitive.OnPlane F rho /\
      Q.toHilbertSpacePrimitive.OnPlane G rho /\
      HilbertPlaneInHyperplane4 Geo rho Sigma /\
      HilbertPlaneInHyperplane4 Geo rho Lambda := by

  let Fp : HyperplanePoint4 Geo Sigma :=
    ⟨F, hFSigma⟩

  let Gp : HyperplanePoint4 Geo Sigma :=
    ⟨G, hGSigma⟩

  have hFpGp : Ne Fp Gp := by
    intro hEq
    apply hFG
    exact congrArg Subtype.val hEq

  rcases
      hyperplaneGeo4_plane_through_point_avoiding_point_corrected
        (Geo := Geo)
        Sigma Fp Gp hFpGp with
    ⟨pi, hFpi, hGnotPi⟩

  ----------------------------------------------------------------------
  -- Intersect pi with Lambda at F and obtain C != F.
  ----------------------------------------------------------------------

  rcases
      Hilbert4DPlaneHyperplaneIncidence.plane_hyperplane_second_common_point
        (Geo := Geo)
        pi.1 Lambda
        F hFpi hFLambda with
    ⟨C, hCF, hCpi, hCLambda⟩

  have hCSigma :
      Q.OnHyperplane C Sigma :=
    pi.2 C hCpi

  ----------------------------------------------------------------------
  -- C is not on FG, because pi contains F,C but was chosen to avoid G.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        F G hFG with
    ⟨q, hFq, hGq⟩

  have hCnotq :
      Not (H.OnLine C q) := by

    intro hCq

    have hFC : Ne F C :=
      hCF.symm

    have hqPi :
        HilbertLineInPlane Geo q pi.1 :=
      H4I.line_in_plane
        F C hFC
        q hFq hCq
        pi.1 hFpi hCpi

    apply hGnotPi

    exact
      hqPi G hGq

  have hFGC :
      Not (PrimCollinear Geo F G C) :=
    hilbert_not_collinear_of_off_line
      Geo
      F G C q
      hFG
      hFq hGq hCnotq

  ----------------------------------------------------------------------
  -- rho = plane(F,G,C), contained in both Sigma and Lambda.
  ----------------------------------------------------------------------

  rcases
      H4I.plane_through
        F G C hFGC with
    ⟨rho, hFrho, hGrho, hCrho⟩

  have hRhoSigma :
      HilbertPlaneInHyperplane4
        Geo rho Sigma :=
    H4L.plane_in_hyperplane
      F G C hFGC
      rho
      hFrho hGrho hCrho
      Sigma
      hFSigma hGSigma hCSigma

  have hRhoLambda :
      HilbertPlaneInHyperplane4
        Geo rho Lambda :=
    H4L.plane_in_hyperplane
      F G C hFGC
      rho
      hFrho hGrho hCrho
      Lambda
      hFLambda hGLambda hCLambda

  exact
    ⟨rho,
     hFrho,
     hGrho,
     hRhoSigma,
     hRhoLambda⟩

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: distinct-foot normals to one hyperplane are parallel

This is the dimension-corrected E4 version of the old ambient XI.6
step.

The proof does NOT install `HilbertSpaceIncidence Geo` in ambient E4.

Instead:

1. test73 gives one genuine 3-hyperplane Lambda containing both normals;
2. test74 gives a plane rho contained in Sigma and Lambda through both
   feet F,G;
3. ambient perpendicularity is transferred to the local geometry
   `HyperplaneGeo4 Geo Lambda`;
4. Euclid XI.6 is applied only inside that local 3-dimensional geometry;
5. the resulting coplanarity and disjointness are transferred back to
   ambient E4.

This is exactly the localization that was missing in the old E4 route.
-/

/--
Dimension-safe ambient parallelism in E4: two lines are parallel when
they lie in one ambient 2-plane and are disjoint.

This duplicates only the proposition-level content of the old
`HilbertSpaceLinesParallel`, without requiring an ambient 3D
`HilbertSpaceIncidence Geo` instance.
-/
def Hilbert4DLinesParallel_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (l m : Geo.Line) : Prop :=
  exists pi : Q.toHilbertSpacePrimitive.Plane,
    HilbertLineInPlane Geo l pi /\
    HilbertLineInPlane Geo m pi /\
    HilbertLinesDisjoint Geo l m

/--
If two ambient lines contained in one corrected E4 hyperplane are
perpendicular at O in ambient geometry, then they are perpendicular at
O in the induced local 3D geometry.
-/
theorem hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (Lambda : Q.Hyperplane)
    (l m : HyperplaneLine4 Geo Lambda)
    (O : HyperplanePoint4 Geo Lambda)
    (hPerp :
      HilbertLinesPerpendicularAt Geo l.1 m.1 O.1) :
    HilbertLinesPerpendicularAt
      (HyperplaneGeo4 Geo Lambda) l m O := by

  rcases hPerp with
    ⟨hOl, hOm,
     A, B,
     hAO, hBO,
     hAl, hBm,
     hNon,
     hRight⟩

  have hALambda :
      Q.OnHyperplane A Lambda :=
    l.2 A hAl

  have hBLambda :
      Q.OnHyperplane B Lambda :=
    m.2 B hBm

  let Ap : HyperplanePoint4 Geo Lambda :=
    ⟨A, hALambda⟩

  let Bp : HyperplanePoint4 Geo Lambda :=
    ⟨B, hBLambda⟩

  have hAOp : Ne Ap O := by
    intro hEq
    apply hAO
    exact congrArg Subtype.val hEq

  have hBOp : Ne Bp O := by
    intro hEq
    apply hBO
    exact congrArg Subtype.val hEq

  have hNonLocal :
      Not
        (PrimCollinear
          (HyperplaneGeo4 Geo Lambda)
          Ap O Bp) := by

    intro hLocal

    apply hNon

    exact
      hyperplaneGeo4_primCollinear_to_ambient
        (Geo := Geo)
        Lambda
        Ap O Bp
        hLocal

  have hRightLocal :
      HilbertRightAngle
        (HyperplaneGeo4 Geo Lambda)
        Ap O Bp := by

    rcases hRight with
      ⟨C, hAOC, hAngle⟩

    have hAOCinc :=
      H4O.between_incidence
        A O.1 C hAOC

    have hAOCcol :
        PrimCollinear Geo A O.1 C :=
      hAOCinc.2.2.2.1

    have hCl :
        H.OnLine C l.1 :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAO
        hAl hOl
        hAOCcol

    have hCLambda :
        Q.OnHyperplane C Lambda :=
      l.2 C hCl

    let Cp : HyperplanePoint4 Geo Lambda :=
      ⟨C, hCLambda⟩

    have hBetweenLocal :
        (HyperplaneGeo4 Geo Lambda).Between
          Ap O Cp := by
      exact hAOC

    have hAngleLocal :
        (HyperplaneGeo4 Geo Lambda).AngleCongruent
          Ap O Bp
          Bp O Cp := by

      apply
        (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
          (Geo := Geo)
          Lambda
          Ap O Bp
          Bp O Cp).2

      exact hAngle

    exact
      ⟨Cp,
       hBetweenLocal,
       hAngleLocal⟩

  exact
    ⟨hOl,
     hOm,
     Ap, Bp,
     hAOp,
     hBOp,
     hAl,
     hBm,
     hNonLocal,
     hRightLocal⟩

/--
Two corrected E4 normals to the same hyperplane at distinct feet are
parallel in the dimension-safe ambient E4 sense.

The only invocation of Euclid XI.6 occurs inside
`HyperplaneGeo4 Geo Lambda`, where the old spatial theorem is valid.
-/
theorem hilbert4D_normals_to_same_hyperplane_parallel_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (l m : Geo.Line)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G) :
    Hilbert4DLinesParallel_corrected Geo l m := by

  ----------------------------------------------------------------------
  -- Put both normals into one genuine local E3 carrier Lambda.
  ----------------------------------------------------------------------

  rcases
      hilbert4D_distinct_foot_normals_common_hyperplane_corrected
        (Geo := Geo)
        Sigma
        l m
        F G
        hFG
        hLNormal
        hMNormal with
    ⟨Lambda, hlLambda, hmLambda⟩

  have hFLambda :
      Q.OnHyperplane F Lambda :=
    hlLambda F hLNormal.1

  have hGLambda :
      Q.OnHyperplane G Lambda :=
    hmLambda G hMNormal.1

  ----------------------------------------------------------------------
  -- Build rho subset Sigma cap Lambda through F,G.
  ----------------------------------------------------------------------

  rcases
      hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
        (Geo := Geo)
        Sigma Lambda
        F G
        hFG
        hLNormal.2.1
        hMNormal.2.1
        hFLambda
        hGLambda with
    ⟨rho,
     hFrho,
     hGrho,
     hRhoSigma,
     hRhoLambda⟩

  let lL : HyperplaneLine4 Geo Lambda :=
    ⟨l, hlLambda⟩

  let mL : HyperplaneLine4 Geo Lambda :=
    ⟨m, hmLambda⟩

  let FL : HyperplanePoint4 Geo Lambda :=
    ⟨F, hFLambda⟩

  let GL : HyperplanePoint4 Geo Lambda :=
    ⟨G, hGLambda⟩

  let rhoL : HyperplanePlane4 Geo Lambda :=
    ⟨rho, hRhoLambda⟩

  have hFLGL : Ne FL GL := by
    intro hEq
    apply hFG
    exact congrArg Subtype.val hEq

  ----------------------------------------------------------------------
  -- The ambient Sigma-normal l becomes rho-normal inside Lambda.
  ----------------------------------------------------------------------

  have hLperpLocal :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Lambda)
        lL rhoL FL := by

    refine
      ⟨hLNormal.1,
       hFrho,
       ?_⟩

    intro q hqRho hFq

    have hqRhoAmbient :
        HilbertLineInPlane Geo q.1 rho :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Lambda
        q rhoL
        hqRho

    have hqSigma :
        HilbertLineInHyperplane4 Geo q.1 Sigma := by

      intro X hXq

      exact
        hRhoSigma X
          (hqRhoAmbient X hXq)

    have hAmbientPerp :
        HilbertLinesPerpendicularAt
          Geo l q.1 F :=
      HilbertLinePerpendicularHyperplaneAt4_corrected.perpendicular_to_line
        (Geo := Geo)
        hLNormal
        q.1
        hqSigma
        hFq

    exact
      hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
        (Geo := Geo)
        Lambda
        lL q FL
        hAmbientPerp

  ----------------------------------------------------------------------
  -- The ambient Sigma-normal m becomes rho-normal inside Lambda.
  ----------------------------------------------------------------------

  have hMperpLocal :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Lambda)
        mL rhoL GL := by

    refine
      ⟨hMNormal.1,
       hGrho,
       ?_⟩

    intro q hqRho hGq

    have hqRhoAmbient :
        HilbertLineInPlane Geo q.1 rho :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Lambda
        q rhoL
        hqRho

    have hqSigma :
        HilbertLineInHyperplane4 Geo q.1 Sigma := by

      intro X hXq

      exact
        hRhoSigma X
          (hqRhoAmbient X hXq)

    have hAmbientPerp :
        HilbertLinesPerpendicularAt
          Geo m q.1 G :=
      HilbertLinePerpendicularHyperplaneAt4_corrected.perpendicular_to_line
        (Geo := Geo)
        hMNormal
        q.1
        hqSigma
        hGq

    exact
      hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
        (Geo := Geo)
        Lambda
        mL q GL
        hAmbientPerp

  ----------------------------------------------------------------------
  -- XI.6, but only inside the genuine local E3 geometry Lambda.
  ----------------------------------------------------------------------

  have hParallelLocal :
      HilbertSpaceLinesParallel
        (HyperplaneGeo4 Geo Lambda)
        lL mL :=
    euclid_proposition_11_6
      (Geo := HyperplaneGeo4 Geo Lambda)
      rhoL
      lL mL
      FL GL
      hFLGL
      hLperpLocal
      hMperpLocal

  rcases hParallelLocal with
    ⟨piL,
     hlPiLocal,
     hmPiLocal,
     hDisjointLocal⟩

  have hlPiAmbient :
      HilbertLineInPlane Geo l piL.1 :=
    hyperplaneGeo4_lineInPlane_to_ambient_corrected
      (Geo := Geo)
      Lambda
      lL piL
      hlPiLocal

  have hmPiAmbient :
      HilbertLineInPlane Geo m piL.1 :=
    hyperplaneGeo4_lineInPlane_to_ambient_corrected
      (Geo := Geo)
      Lambda
      mL piL
      hmPiLocal

  have hDisjointAmbient :
      HilbertLinesDisjoint Geo l m :=
    (hyperplaneGeo4_linesDisjoint_iff_ambient_corrected
      (Geo := Geo)
      Lambda
      lL mL).1
      hDisjointLocal

  exact
    ⟨piL.1,
     hlPiAmbient,
     hmPiAmbient,
     hDisjointAmbient⟩

end Geometry

-- E4HyperplaneXI11 FIX4 - 2026-09-11
import CGJteamLab.E4HyperplaneXI12
import CGJteamLab.Coxeter.E4HyperplaneReflectionCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.11 lifted to E4 hyperplanes

This file derives the corrected E4 analogue of Euclid XI.11 from the
already derived E4 analogue of XI.12 together with localized XI.8 and
XI.6.

Let Sigma be an E4 hyperplane and let P lie outside Sigma.

1. Choose O in Sigma.
2. By E4-XI.12 construct a normal r to Sigma at O.
3. If P lies on r, r itself is the required perpendicular.
4. Otherwise choose the plane pi through r and P.
5. Extend pi to a hyperplane Lambda.
6. Inside the genuine local E3 geometry Lambda, construct through P a
   line q parallel to r.
7. The intersection Sigma cap Lambda contains a 2-plane Delta through O.
8. Since r is normal to Sigma, r is perpendicular to Delta.
9. Local Euclid XI.8 in Lambda shows that q meets Delta at F and is
   perpendicular to Delta there.  Hence F lies in Sigma.
10. E4-XI.12 gives a genuine Sigma-normal s at F.
11. Corrected E4 XI.6 gives r parallel s, while q parallel r.
12. Uniqueness of the parallel through F forces q = s.

Therefore q is the required normal through the external point P.

No `Hilbert4DNormalFromExternalPointExistence_corrected` assumption is
used in the proof.
-/

/--
Transfer an ambient line-plane perpendicularity into one fixed local
hyperplane geometry.
-/
theorem hyperplaneGeo4_linePerpendicularPlaneAt_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (Lambda : Q.Hyperplane)
    (l : HyperplaneLine4 Geo Lambda)
    (pi : HyperplanePlane4 Geo Lambda)
    (O : HyperplanePoint4 Geo Lambda)
    (hPerp :
      HilbertLinePerpendicularPlaneAt
        Geo l.1 pi.1 O.1) :
    HilbertLinePerpendicularPlaneAt
      (HyperplaneGeo4 Geo Lambda)
      l pi O := by

  refine ⟨hPerp.1, hPerp.2.1, ?_⟩

  intro m hmPi hOm

  have hmPiAmbient :
      HilbertLineInPlane Geo m.1 pi.1 := by
    intro X hXm

    have hXLambda :
        Q.OnHyperplane X Lambda :=
      m.2 X hXm

    exact
      hmPi
        ⟨X, hXLambda⟩
        hXm

  have hAmbient :
      HilbertLinesPerpendicularAt
        Geo l.1 m.1 O.1 :=
    hPerp.2.2
      m.1
      hmPiAmbient
      hOm

  exact
    hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
      (Geo := Geo)
      Lambda
      l m O
      hAmbient


/--
Local spatial parallelism inside a hyperplane implies the corrected
ambient E4 parallel relation for the carrier lines.
-/
theorem hyperplaneGeo4_parallel_to_ambient4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Lambda : Q.Hyperplane)
    (l m : HyperplaneLine4 Geo Lambda)
    (hPar :
      HilbertSpaceLinesParallel
        (HyperplaneGeo4 Geo Lambda)
        l m) :
    Hilbert4DLinesParallel_corrected Geo l.1 m.1 := by

  rcases hPar with
    ⟨pi, hlPi, hmPi, hDisjoint⟩

  have hlPiAmbient :
      HilbertLineInPlane Geo l.1 pi.1 := by
    intro X hXl
    exact
      hlPi
        ⟨X, l.2 X hXl⟩
        hXl

  have hmPiAmbient :
      HilbertLineInPlane Geo m.1 pi.1 := by
    intro X hXm
    exact
      hmPi
        ⟨X, m.2 X hXm⟩
        hXm

  have hDisjointAmbient :
      HilbertLinesDisjoint Geo l.1 m.1 := by
    rintro ⟨X, hXl, hXm⟩

    have hXLambda :
        Q.OnHyperplane X Lambda :=
      l.2 X hXl

    exact
      hDisjoint
        ⟨⟨X, hXLambda⟩, hXl, hXm⟩

  exact
    ⟨pi.1,
     hlPiAmbient,
     hmPiAmbient,
     hDisjointAmbient⟩


/--
Corrected E4 analogue of Euclid XI.11.

From an external point P draw a perpendicular to the hyperplane Sigma.
-/
theorem hilbert4D_normal_through_point_to_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [H4E : Hilbert4DAmbientEuclidean Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P := by

  rcases
      C4.point_on_each_hyperplane Sigma with
    ⟨O, hOSigma⟩

  rcases
      hilbert4D_XI12_normal_at_hyperplane_point_corrected
        (Geo := Geo)
        Sigma O hOSigma with
    ⟨r, hRNormal⟩

  have hOr :
      H.OnLine O r :=
    hRNormal.1

  by_cases hPr : H.OnLine P r

  · exact
      ⟨O,
       ⟨r,
        hPr,
        hRNormal⟩⟩

  · ------------------------------------------------------------------
    -- pi is the ambient plane through r and P.
    ------------------------------------------------------------------

    rcases
        hilbert4D_plane_through_line_and_external_point
          (Geo := Geo)
          r P hPr with
      ⟨pi, hrPi, hPpi⟩

    have hOpi :
        Q.toHilbertSpacePrimitive.OnPlane O pi :=
      hrPi O hOr

    ------------------------------------------------------------------
    -- Pick C in Sigma outside pi, then extend pi to a hyperplane
    -- Lambda.  Thus Lambda contains r and P but is distinct from Sigma.
    ------------------------------------------------------------------

    rcases
        hilbert4D_hyperplane_point_off_plane_corrected
          (Geo := Geo)
          Sigma pi with
      ⟨C, hCSigma, hCpi⟩

    rcases
        hilbert4D_hyperplane_through_plane_and_external_point_corrected
          (Geo := Geo)
          pi C hCpi with
      ⟨Lambda, hPiLambda, hCLambda⟩

    have hrLambda :
        HilbertLineInHyperplane4 Geo r Lambda := by
      intro X hXr
      exact hPiLambda X (hrPi X hXr)

    have hPLambda :
        Q.OnHyperplane P Lambda :=
      hPiLambda P hPpi

    have hOLambda :
        Q.OnHyperplane O Lambda :=
      hPiLambda O hOpi

    have hOC : Ne O C := by
      intro hOC
      subst C
      exact hCpi hOpi

    ------------------------------------------------------------------
    -- Work inside the genuine E3 geometry Lambda and construct
    -- q through P parallel to r.
    ------------------------------------------------------------------

    let piL : HyperplanePlane4 Geo Lambda :=
      ⟨pi, hPiLambda⟩

    let rL : HyperplaneLine4 Geo Lambda :=
      ⟨r, hrLambda⟩

    let PL : HyperplanePoint4 Geo Lambda :=
      ⟨P, hPLambda⟩

    rcases
        hilbert_XI12_parallel_through_point_in_plane
          (Geo := HyperplaneGeo4 Geo Lambda)
          piL rL PL
          (by
            intro X hXr
            exact hrPi X.1 hXr)
          hPpi
          hPr with
      ⟨qL, hPq, hRQParallel⟩

    ------------------------------------------------------------------
    -- Sigma and Lambda have O,C in common, hence contain a common
    -- 2-plane Delta through O.
    ------------------------------------------------------------------

    rcases
        hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
          (Geo := Geo)
          Sigma Lambda
          O C
          hOC
          hOSigma hCSigma
          hOLambda hCLambda with
      ⟨Delta,
       hODelta,
       _hCDelta,
       hDeltaSigma,
       hDeltaLambda⟩

    have hRPerpDelta :
        HilbertLinePerpendicularPlaneAt
          Geo r Delta O := by

      refine
        ⟨hOr,
         hODelta,
         ?_⟩

      intro m hmDelta hOm

      have hmSigma :
          HilbertLineInHyperplane4 Geo m Sigma := by
        intro X hXm
        exact hDeltaSigma X (hmDelta X hXm)

      exact
        hRNormal.2.2
          m
          hmSigma
          hOm

    let DeltaL : HyperplanePlane4 Geo Lambda :=
      ⟨Delta, hDeltaLambda⟩

    let OL : HyperplanePoint4 Geo Lambda :=
      ⟨O, hOLambda⟩

    have hRPerpDeltaLocal :
        HilbertLinePerpendicularPlaneAt
          (HyperplaneGeo4 Geo Lambda)
          rL DeltaL OL :=
      hyperplaneGeo4_linePerpendicularPlaneAt_of_ambient_corrected
        (Geo := Geo)
        Lambda
        rL DeltaL OL
        hRPerpDelta

    ------------------------------------------------------------------
    -- XI.8: the parallel q meets Delta and is perpendicular to Delta.
    ------------------------------------------------------------------

    rcases
        euclid_proposition_11_8
          (Geo := HyperplaneGeo4 Geo Lambda)
          rL qL DeltaL OL
          hRQParallel
          hRPerpDeltaLocal with
      ⟨FL, hQPerpDeltaLocal⟩

    let F : Geo.Point :=
      FL.1

    have hFq :
        H.OnLine F qL.1 :=
      hQPerpDeltaLocal.1

    have hFDelta :
        Q.toHilbertSpacePrimitive.OnPlane F Delta :=
      hQPerpDeltaLocal.2.1

    have hFSigma :
        Q.OnHyperplane F Sigma :=
      hDeltaSigma F hFDelta

    ------------------------------------------------------------------
    -- The parallel pair r,q is disjoint, so F != O.
    ------------------------------------------------------------------

    have hRQParallelAmbient :
        Hilbert4DLinesParallel_corrected
          Geo r qL.1 :=
      hyperplaneGeo4_parallel_to_ambient4_corrected
        (Geo := Geo)
        Lambda
        rL qL
        hRQParallel

    rcases hRQParallelAmbient with
      ⟨omega,
       hrOmega,
       hqOmega,
       hRQDisjoint⟩

    have hFnotr :
        Not (H.OnLine F r) := by
      intro hFr

      exact
        hRQDisjoint
          ⟨F, hFr, hFq⟩

    have hOF : Ne O F := by
      intro hEqOF
      apply hFnotr
      rw [<- hEqOF]
      exact hOr

    ------------------------------------------------------------------
    -- XI.12 gives the genuine Sigma-normal s at F.
    ------------------------------------------------------------------

    rcases
        hilbert4D_XI12_normal_at_hyperplane_point_corrected
          (Geo := Geo)
          Sigma F hFSigma with
      ⟨s, hSNormal⟩

    have hFs :
        H.OnLine F s :=
      hSNormal.1

    ------------------------------------------------------------------
    -- Corrected XI.6: r and s are parallel.
    ------------------------------------------------------------------

    have hRSParallel :
        Hilbert4DLinesParallel_corrected Geo r s :=
      hilbert4D_normals_to_same_hyperplane_parallel_corrected
        (Geo := Geo)
        Sigma
        r s
        O F
        hOF
        hRNormal
        hSNormal

    rcases hRSParallel with
      ⟨rho,
       hrRho,
       hsRho,
       hRSDisjoint⟩

    ------------------------------------------------------------------
    -- omega and rho are both the plane through r and F.
    ------------------------------------------------------------------

    rcases
        H4I.two_points_on_each_line r with
      ⟨A, B, hAB, hAr, hBr⟩

    have hABF :
        Not (PrimCollinear Geo A B F) := by

      intro hCol

      have hFr :
          H.OnLine F r :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hAB
          hAr hBr
          hCol

      exact hFnotr hFr

    have hAomega :
        Q.toHilbertSpacePrimitive.OnPlane A omega :=
      hrOmega A hAr

    have hBomega :
        Q.toHilbertSpacePrimitive.OnPlane B omega :=
      hrOmega B hBr

    have hFomega :
        Q.toHilbertSpacePrimitive.OnPlane F omega :=
      hqOmega F hFq

    have hArho :
        Q.toHilbertSpacePrimitive.OnPlane A rho :=
      hrRho A hAr

    have hBrho :
        Q.toHilbertSpacePrimitive.OnPlane B rho :=
      hrRho B hBr

    have hFrho :
        Q.toHilbertSpacePrimitive.OnPlane F rho :=
      hsRho F hFs

    have hOmegaRho :
        omega = rho :=
      H4I.plane_unique
        A B F
        hABF
        omega rho
        hAomega hBomega hFomega
        hArho hBrho hFrho

    have hsOmega :
        HilbertLineInPlane Geo s omega := by
      rw [hOmegaRho]
      exact hsRho

    ------------------------------------------------------------------
    -- q and s both pass through F and are parallel to r in omega.
    -- Group IV uniqueness therefore gives q = s.
    ------------------------------------------------------------------

    have hQRDisjoint :
        HilbertLinesDisjoint Geo qL.1 r := by
      rintro ⟨X, hXq, hXr⟩
      exact
        hRQDisjoint
          ⟨X, hXr, hXq⟩

    have hSRDisjoint :
        HilbertLinesDisjoint Geo s r := by
      rintro ⟨X, hXs, hXr⟩
      exact
        hRSDisjoint
          ⟨X, hXr, hXs⟩

    have hQS :
        qL.1 = s :=
      H4E.parallel_unique_in_plane
        omega
        r
        hrOmega
        F
        hFomega
        hFnotr
        qL.1 s
        hqOmega hsOmega
        hFq
        hQRDisjoint
        hFs
        hSRDisjoint

    have hQNormal :
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo qL.1 Sigma F := by
      rw [hQS]
      exact hSNormal

    exact
      ⟨F,
       ⟨qL.1,
        hPq,
        hQNormal⟩⟩


/--
Corrected E4 analogue of Euclid XI.11.

The externality hypothesis is needed only to match the historical XI.11
statement; the construction above actually works for every point.
-/
theorem hilbert4D_XI11_normal_from_external_point_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [H4E : Hilbert4DAmbientEuclidean Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (_hPSigma : Not (Q.OnHyperplane P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P :=
  hilbert4D_normal_through_point_to_hyperplane_corrected
    (Geo := Geo)
    Sigma P


/--
The former XI.11-type existence class is derivable from the corrected
E4 Hilbert layers.
-/
theorem hilbert4D_XI11_implies_normalFromExternalPointExistence_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo] :
    Hilbert4DNormalFromExternalPointExistence_corrected Geo where

  normal_from_external_point := by
    intro Sigma P hPSigma

    exact
      hilbert4D_XI11_normal_from_external_point_corrected
        (Geo := Geo)
        Sigma P hPSigma

end Geometry

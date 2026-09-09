import CGJteamLab.Coxeter.E4HyperplaneIntersection
import CGJteamLab.Coxeter.E4NormalCore
import CGJteamLab.Proposition11_12
import CGJteamLab.Proposition11_5

/-!
# Corrected E4 normal section

Production promotion of the validated normal-section existence theorem
and the exact-trace theorem for a pair of distinct hyperplanes.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: normal 2-plane for a pair of intersecting hyperplanes

Assume two distinct E4 hyperplanes Sigma and Tau meet exactly in the
ambient 2-plane Delta, and choose O in Delta.

Inside Sigma, the local 3D geometry supplies by Euclid XI.12 a line s
through O perpendicular to Delta.

Inside Tau, the local 3D geometry supplies by Euclid XI.12 a line t
through O perpendicular to Delta.

The two carrier lines s and t are distinct.  Otherwise the common line
would lie in both hyperplanes, hence in Delta, contradicting its
perpendicularity to Delta.

Therefore s and t determine an ambient 2-plane N.  This N is the
synthetic normal section of the pair (Sigma,Tau) at O.

No coordinates, inner product, normal vector, or dimension formula is
used.
-/

/--
For two hyperplanes meeting exactly in Delta and a point O on Delta,
there exist distinct lines s,t through O, with

* s contained in Sigma and perpendicular to Delta inside Sigma;
* t contained in Tau and perpendicular to Delta inside Tau;

and the carrier lines s,t lie in one ambient 2-plane N.
-/
theorem hilbert4D_hyperplane_pair_normal_section_exists_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta) :
    exists s : HyperplaneLine4 Geo Sigma,
      exists t : HyperplaneLine4 Geo Tau,
        HilbertLinePerpendicularPlaneAt
            (HyperplaneGeo4 Geo Sigma)
            s
            (Subtype.mk Delta hMeet.2.1)
            (Subtype.mk O (hMeet.2.1 O hODelta)) /\
        HilbertLinePerpendicularPlaneAt
            (HyperplaneGeo4 Geo Tau)
            t
            (Subtype.mk Delta hMeet.2.2.1)
            (Subtype.mk O (hMeet.2.2.1 O hODelta)) /\
        Ne s.1 t.1 /\
        exists N : Q.toHilbertSpacePrimitive.Plane,
          Q.toHilbertSpacePrimitive.OnPlane O N /\
          HilbertLineInPlane Geo s.1 N /\
          HilbertLineInPlane Geo t.1 N := by

  let DeltaSigma : HyperplanePlane4 Geo Sigma :=
    Subtype.mk Delta hMeet.2.1

  let DeltaTau : HyperplanePlane4 Geo Tau :=
    Subtype.mk Delta hMeet.2.2.1

  have hOSigma :
      Q.OnHyperplane O Sigma :=
    hMeet.2.1 O hODelta

  have hOTau :
      Q.OnHyperplane O Tau :=
    hMeet.2.2.1 O hODelta

  let OSigma : HyperplanePoint4 Geo Sigma :=
    Subtype.mk O hOSigma

  let OTau : HyperplanePoint4 Geo Tau :=
    Subtype.mk O hOTau

  have hODeltaSigma :
      HyperplaneOnPlane4 Geo OSigma DeltaSigma := by
    exact hODelta

  have hODeltaTau :
      HyperplaneOnPlane4 Geo OTau DeltaTau := by
    exact hODelta

  ----------------------------------------------------------------------
  -- XI.12 inside Sigma and Tau.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_12
        (Geo := HyperplaneGeo4 Geo Sigma)
        DeltaSigma
        OSigma
        hODeltaSigma with
    ⟨s, hSPerp⟩

  rcases
      euclid_proposition_11_12
        (Geo := HyperplaneGeo4 Geo Tau)
        DeltaTau
        OTau
        hODeltaTau with
    ⟨t, hTPerp⟩

  have hOs :
      H.OnLine O s.1 :=
    hSPerp.1

  have hOt :
      H.OnLine O t.1 :=
    hTPerp.1

  ----------------------------------------------------------------------
  -- The two carrier lines are distinct.
  ----------------------------------------------------------------------

  have hst : Ne s.1 t.1 := by
    intro hEq

    have hsDeltaAmbient :
        HilbertLineInPlane Geo s.1 Delta := by

      intro X hXs

      have hXSigma :
          Q.OnHyperplane X Sigma :=
        s.2 X hXs

      have hXt :
          H.OnLine X t.1 := by
        rw [← hEq]
        exact hXs

      have hXTau :
          Q.OnHyperplane X Tau :=
        t.2 X hXt

      exact
        (hMeet.2.2.2 X).mp
          (And.intro hXSigma hXTau)

    have hsDeltaLocal :
        HilbertLineInPlane
          (HyperplaneGeo4 Geo Sigma)
          s
          DeltaSigma := by

      intro X hXs

      exact
        hsDeltaAmbient X.1 hXs

    exact
      (hilbert_linePerpendicularPlaneAt_not_in_plane
        (Geo := HyperplaneGeo4 Geo Sigma)
        s DeltaSigma OSigma hSPerp)
        hsDeltaLocal

  ----------------------------------------------------------------------
  -- Choose one non-O point on each line.
  ----------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := HyperplaneGeo4 Geo Sigma)
        s OSigma with
    ⟨A, hAO, hAs⟩

  rcases
      hilbert_other_point_on_line
        (Geo := HyperplaneGeo4 Geo Tau)
        t OTau with
    ⟨B, hBO, hBt⟩

  have hAOval : Ne A.1 O := by
    intro h
    apply hAO
    exact Subtype.ext h

  have hBOval : Ne B.1 O := by
    intro h
    apply hBO
    exact Subtype.ext h

  ----------------------------------------------------------------------
  -- A,O,B are noncollinear, otherwise s=t.
  ----------------------------------------------------------------------

  have hAOB :
      Not (PrimCollinear Geo A.1 O B.1) := by

    intro hCol

    have hBs :
        H.OnLine B.1 s.1 :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAOval
        hAs hOs
        hCol

    have hEq :
        s.1 = t.1 :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O B.1
        hBOval.symm
        s.1 t.1
        hOs hBs
        hOt hBt

    exact hst hEq

  ----------------------------------------------------------------------
  -- The three noncollinear points determine the normal section N.
  ----------------------------------------------------------------------

  rcases
      H4I.plane_through
        A.1 O B.1
        hAOB with
    ⟨N, hAN, hON, hBN⟩

  have hsN :
      HilbertLineInPlane Geo s.1 N :=
    H4I.line_in_plane
      A.1 O
      hAOval
      s.1
      hAs hOs
      N
      hAN hON

  have htN :
      HilbertLineInPlane Geo t.1 N :=
    H4I.line_in_plane
      O B.1
      hBOval.symm
      t.1
      hOt hBt
      N
      hON hBN

  refine Exists.intro s ?_
  refine Exists.intro t ?_

  refine And.intro ?_ ?_
  · simpa [DeltaSigma, OSigma] using hSPerp

  refine And.intro ?_ ?_
  · simpa [DeltaTau, OTau] using hTPerp

  refine And.intro hst ?_

  exact
    Exists.intro N
      (And.intro hON
        (And.intro hsN htN))

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: exact mirror lines in the normal section

Test71 constructed, for two distinct hyperplanes Sigma,Tau meeting
exactly in Delta and O in Delta, a normal 2-plane N containing

  s subset Sigma,  s perpendicular Delta at O inside Sigma,
  t subset Tau,    t perpendicular Delta at O inside Tau.

This file proves that the traces of the two reflecting hyperplanes on N
are exactly those carrier lines:

  N cap Sigma = s,
  N cap Tau   = t.

The proof is still pure synthetic incidence plus line-plane
perpendicularity.  In particular, if N were contained in Sigma, then
t would lie in both Sigma and Tau, hence in Delta, contradicting
t perpendicular Delta.  The argument for Tau is symmetric.

No reflection properties are used yet.
-/

/--
The normal section from test71 is not contained in either reflecting
hyperplane, and each plane-hyperplane intersection is exactly the
corresponding normal-section line.
-/
theorem hilbert4D_hyperplane_pair_normal_section_exact_traces_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta) :
    exists s : HyperplaneLine4 Geo Sigma,
      exists t : HyperplaneLine4 Geo Tau,
        exists N : Q.toHilbertSpacePrimitive.Plane,
          HilbertLinePerpendicularPlaneAt
              (HyperplaneGeo4 Geo Sigma)
              s
              (Subtype.mk Delta hMeet.2.1)
              (Subtype.mk O (hMeet.2.1 O hODelta)) /\
          HilbertLinePerpendicularPlaneAt
              (HyperplaneGeo4 Geo Tau)
              t
              (Subtype.mk Delta hMeet.2.2.1)
              (Subtype.mk O (hMeet.2.2.1 O hODelta)) /\
          Ne s.1 t.1 /\
          Q.toHilbertSpacePrimitive.OnPlane O N /\
          HilbertLineInPlane Geo s.1 N /\
          HilbertLineInPlane Geo t.1 N /\
          Not (HilbertPlaneInHyperplane4 Geo N Sigma) /\
          Not (HilbertPlaneInHyperplane4 Geo N Tau) /\
          (forall X : Geo.Point,
            (Q.toHilbertSpacePrimitive.OnPlane X N /\
             Q.OnHyperplane X Sigma) <->
              H.OnLine X s.1) /\
          (forall X : Geo.Point,
            (Q.toHilbertSpacePrimitive.OnPlane X N /\
             Q.OnHyperplane X Tau) <->
              H.OnLine X t.1) := by

  rcases
      hilbert4D_hyperplane_pair_normal_section_exists_corrected
        (Geo := Geo)
        Sigma Tau Delta hMeet
        O hODelta with
    ⟨s, t,
     hSPerp,
     hTPerp,
     hst,
     N,
     hON,
     hsN,
     htN⟩

  let DeltaSigma : HyperplanePlane4 Geo Sigma :=
    Subtype.mk Delta hMeet.2.1

  let DeltaTau : HyperplanePlane4 Geo Tau :=
    Subtype.mk Delta hMeet.2.2.1

  have hOSigma :
      Q.OnHyperplane O Sigma :=
    hMeet.2.1 O hODelta

  have hOTau :
      Q.OnHyperplane O Tau :=
    hMeet.2.2.1 O hODelta

  let OSigma : HyperplanePoint4 Geo Sigma :=
    Subtype.mk O hOSigma

  let OTau : HyperplanePoint4 Geo Tau :=
    Subtype.mk O hOTau

  have hOs :
      H.OnLine O s.1 :=
    hSPerp.1

  have hOt :
      H.OnLine O t.1 :=
    hTPerp.1

  ----------------------------------------------------------------------
  -- N is not contained in Sigma.
  ----------------------------------------------------------------------

  have hNnotSigma :
      Not (HilbertPlaneInHyperplane4 Geo N Sigma) := by

    intro hNSigma

    have htSigma :
        HilbertLineInHyperplane4 Geo t.1 Sigma := by

      intro X hXt

      exact hNSigma X (htN X hXt)

    have htDeltaAmbient :
        HilbertLineInPlane Geo t.1 Delta := by

      intro X hXt

      have hXSigma :
          Q.OnHyperplane X Sigma :=
        htSigma X hXt

      have hXTau :
          Q.OnHyperplane X Tau :=
        t.2 X hXt

      exact
        (hMeet.2.2.2 X).mp
          (And.intro hXSigma hXTau)

    have htDeltaLocal :
        HilbertLineInPlane
          (HyperplaneGeo4 Geo Tau)
          t
          DeltaTau := by

      intro X hXt

      exact
        htDeltaAmbient X.1 hXt

    exact
      (hilbert_linePerpendicularPlaneAt_not_in_plane
        (Geo := HyperplaneGeo4 Geo Tau)
        t DeltaTau OTau hTPerp)
        htDeltaLocal

  ----------------------------------------------------------------------
  -- N is not contained in Tau.
  ----------------------------------------------------------------------

  have hNnotTau :
      Not (HilbertPlaneInHyperplane4 Geo N Tau) := by

    intro hNTau

    have hsTau :
        HilbertLineInHyperplane4 Geo s.1 Tau := by

      intro X hXs

      exact hNTau X (hsN X hXs)

    have hsDeltaAmbient :
        HilbertLineInPlane Geo s.1 Delta := by

      intro X hXs

      have hXSigma :
          Q.OnHyperplane X Sigma :=
        s.2 X hXs

      have hXTau :
          Q.OnHyperplane X Tau :=
        hsTau X hXs

      exact
        (hMeet.2.2.2 X).mp
          (And.intro hXSigma hXTau)

    have hsDeltaLocal :
        HilbertLineInPlane
          (HyperplaneGeo4 Geo Sigma)
          s
          DeltaSigma := by

      intro X hXs

      exact
        hsDeltaAmbient X.1 hXs

    exact
      (hilbert_linePerpendicularPlaneAt_not_in_plane
        (Geo := HyperplaneGeo4 Geo Sigma)
        s DeltaSigma OSigma hSPerp)
        hsDeltaLocal

  ----------------------------------------------------------------------
  -- Exact trace of Sigma on N.
  ----------------------------------------------------------------------

  rcases
      hilbert4D_plane_hyperplane_intersection_line
        (Geo := Geo)
        N Sigma
        hNnotSigma
        O hON hOSigma with
    ⟨u, hOu, huN, huSigma, hExactU⟩

  rcases
      hilbert_other_point_on_line
        (Geo := HyperplaneGeo4 Geo Sigma)
        s OSigma with
    ⟨A, hAO, hAs⟩

  have hAOval : Ne A.1 O := by
    intro hEq
    apply hAO
    exact Subtype.ext hEq

  have hAu :
      H.OnLine A.1 u :=
    (hExactU A.1).mp
      (And.intro
        (hsN A.1 hAs)
        (s.2 A.1 hAs))

  have hUS :
      u = s.1 :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      O A.1
      hAOval.symm
      u s.1
      hOu hAu
      hOs hAs

  have hExactSigma :
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X N /\
         Q.OnHyperplane X Sigma) <->
          H.OnLine X s.1 := by

    intro X

    rw [← hUS]

    exact hExactU X

  ----------------------------------------------------------------------
  -- Exact trace of Tau on N.
  ----------------------------------------------------------------------

  rcases
      hilbert4D_plane_hyperplane_intersection_line
        (Geo := Geo)
        N Tau
        hNnotTau
        O hON hOTau with
    ⟨v, hOv, hvN, hvTau, hExactV⟩

  rcases
      hilbert_other_point_on_line
        (Geo := HyperplaneGeo4 Geo Tau)
        t OTau with
    ⟨B, hBO, hBt⟩

  have hBOval : Ne B.1 O := by
    intro hEq
    apply hBO
    exact Subtype.ext hEq

  have hBv :
      H.OnLine B.1 v :=
    (hExactV B.1).mp
      (And.intro
        (htN B.1 hBt)
        (t.2 B.1 hBt))

  have hVT :
      v = t.1 :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      O B.1
      hBOval.symm
      v t.1
      hOv hBv
      hOt hBt

  have hExactTau :
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X N /\
         Q.OnHyperplane X Tau) <->
          H.OnLine X t.1 := by

    intro X

    rw [← hVT]

    exact hExactV X

  ----------------------------------------------------------------------
  -- Package the strengthened normal-section statement.
  ----------------------------------------------------------------------

  exact
    ⟨s, t, N,
     hSPerp,
     hTPerp,
     hst,
     hON,
     hsN,
     htN,
     hNnotSigma,
     hNnotTau,
     hExactSigma,
     hExactTau⟩

end Geometry

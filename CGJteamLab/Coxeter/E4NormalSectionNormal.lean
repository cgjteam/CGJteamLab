import CGJteamLab.Coxeter.E4HyperplanePerpendicularFrame
import CGJteamLab.Proposition11_4

/-!
# Corrected E4 normal inside a normal section

Production consolidation of the validated test77--test80 chain.

This module contains the dimension-safe bridge between local
perpendicularity inside hyperplanes and ambient E4 perpendicularity,
the XI.4 construction for the normal-section plane, a spanning-frame
criterion inside a hyperplane, and the construction of a hyperplane
normal lying in the normal-section plane.

No `AffineFlat4D_testNN`, `*_fixN`, or ambient
`HilbertSpaceIncidence Geo` dependency is imported here.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: local-to-ambient perpendicularity and Delta directions

Test75 established the ambient-to-local bridge for line
perpendicularity inside a corrected E4 hyperplane.

This file proves the converse bridge.  It then applies the equivalence
to the normal-section data: every line of the common plane Delta
through O is perpendicular to each trace line s,t.

This is the direct input needed for the next local XI.4 step.
-/

/--
If two lines are perpendicular in `HyperplaneGeo4 Geo Lambda`, then
their ambient carrier lines are perpendicular in Geo.
-/
theorem hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Lambda : Q.Hyperplane)
    (l m : HyperplaneLine4 Geo Lambda)
    (O : HyperplanePoint4 Geo Lambda)
    (hPerp :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda) l m O) :
    HilbertLinesPerpendicularAt Geo l.1 m.1 O.1 := by

  have hOl :
      H.OnLine O.1 l.1 :=
    hPerp.1

  have hOm :
      H.OnLine O.1 m.1 :=
    hPerp.2.1

  have hWitness :=
    hPerp.2.2

  let A : HyperplanePoint4 Geo Lambda :=
    Classical.choose hWitness

  have hWitnessB :=
    Classical.choose_spec hWitness

  let B : HyperplanePoint4 Geo Lambda :=
    Classical.choose hWitnessB

  have hData :=
    Classical.choose_spec hWitnessB

  have hAOlocal :
      Ne A O :=
    hData.1

  have hBOlocal :
      Ne B O :=
    hData.2.1

  have hAl :
      H.OnLine A.1 l.1 :=
    hData.2.2.1

  have hBm :
      H.OnLine B.1 m.1 :=
    hData.2.2.2.1

  have hNonLocal :
      Not
        (PrimCollinear
          (HyperplaneGeo4 Geo Lambda)
          A O B) :=
    hData.2.2.2.2.1

  have hRightLocal :
      HilbertRightAngle
        (HyperplaneGeo4 Geo Lambda)
        A O B :=
    hData.2.2.2.2.2

  have hAO :
      Ne A.1 O.1 := by
    intro hEq
    apply hAOlocal
    exact Subtype.ext hEq

  have hBO :
      Ne B.1 O.1 := by
    intro hEq
    apply hBOlocal
    exact Subtype.ext hEq

  have hNonAmbient :
      Not (PrimCollinear Geo A.1 O.1 B.1) :=
    hyperplaneGeo4_noncollinear_to_ambient_corrected
      (Geo := Geo)
      Lambda
      A O B
      hNonLocal

  have hRightWitness :=
    hRightLocal

  let C : HyperplanePoint4 Geo Lambda :=
    Classical.choose hRightWitness

  have hRightData :=
    Classical.choose_spec hRightWitness

  have hBetweenAmbient :
      Geo.Between A.1 O.1 C.1 :=
    (hyperplaneGeo4_between_iff_ambient_corrected
      (Geo := Geo)
      Lambda
      A O C).1
      hRightData.1

  have hAngleAmbient :
      Geo.AngleCongruent
        A.1 O.1 B.1
        B.1 O.1 C.1 :=
    (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
      (Geo := Geo)
      Lambda
      A O B
      B O C).1
      hRightData.2

  have hRightAmbient :
      HilbertRightAngle Geo A.1 O.1 B.1 :=
    Exists.intro C.1
      (And.intro
        hBetweenAmbient
        hAngleAmbient)

  exact
    And.intro hOl
      (And.intro hOm
        (Exists.intro A.1
          (Exists.intro B.1
            (And.intro hAO
              (And.intro hBO
                (And.intro hAl
                  (And.intro hBm
                    (And.intro
                      hNonAmbient
                      hRightAmbient))))))))

/--
For lines lying in one corrected E4 hyperplane, local and ambient
perpendicularity are equivalent.
-/
theorem hyperplaneGeo4_linesPerpendicularAt_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Lambda : Q.Hyperplane)
    (l m : HyperplaneLine4 Geo Lambda)
    (O : HyperplanePoint4 Geo Lambda) :
    HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda) l m O <->
      HilbertLinesPerpendicularAt
        Geo l.1 m.1 O.1 := by

  constructor

  case mp =>
    intro h
    exact
      hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
        (Geo := Geo)
        Lambda l m O h

  case mpr =>
    intro h
    exact
      hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
        (Geo := Geo)
        Lambda l m O h

/--
Let Sigma,Tau meet exactly in Delta at O, and let s,t be the two trace
lines supplied by the normal-section construction.

Every ambient line a contained in Delta and passing through O is
perpendicular at O to both carrier lines s and t.
-/
theorem hilbert4D_delta_line_perpendicular_to_normal_section_traces_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (s : HyperplaneLine4 Geo Sigma)
    (t : HyperplaneLine4 Geo Tau)
    (hSPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Sigma)
        s
        (Subtype.mk Delta hMeet.2.1)
        (Subtype.mk O (hMeet.2.1 O hODelta)))
    (hTPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Tau)
        t
        (Subtype.mk Delta hMeet.2.2.1)
        (Subtype.mk O (hMeet.2.2.1 O hODelta)))
    (a : Geo.Line)
    (haDelta :
      HilbertLineInPlane Geo a Delta)
    (hOa :
      H.OnLine O a) :
    HilbertLinesPerpendicularAt Geo s.1 a O /\
    HilbertLinesPerpendicularAt Geo t.1 a O := by

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

  let DeltaSigma : HyperplanePlane4 Geo Sigma :=
    Subtype.mk Delta hMeet.2.1

  let DeltaTau : HyperplanePlane4 Geo Tau :=
    Subtype.mk Delta hMeet.2.2.1

  have haSigma :
      HilbertLineInHyperplane4 Geo a Sigma := by
    intro X hXa
    exact hMeet.2.1 X (haDelta X hXa)

  have haTau :
      HilbertLineInHyperplane4 Geo a Tau := by
    intro X hXa
    exact hMeet.2.2.1 X (haDelta X hXa)

  let aSigma : HyperplaneLine4 Geo Sigma :=
    Subtype.mk a haSigma

  let aTau : HyperplaneLine4 Geo Tau :=
    Subtype.mk a haTau

  have haDeltaSigma :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Sigma)
        aSigma DeltaSigma := by
    intro X hXa
    exact haDelta X.1 hXa

  have haDeltaTau :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Tau)
        aTau DeltaTau := by
    intro X hXa
    exact haDelta X.1 hXa

  have hSLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Sigma)
        s aSigma OSigma :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := HyperplaneGeo4 Geo Sigma)
      hSPerp
      haDeltaSigma
      hOa

  have hTLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Tau)
        t aTau OTau :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := HyperplaneGeo4 Geo Tau)
      hTPerp
      haDeltaTau
      hOa

  have hSAmbient :
      HilbertLinesPerpendicularAt Geo s.1 a O :=
    hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
      (Geo := Geo)
      Sigma
      s aSigma OSigma
      hSLocal

  have hTAmbient :
      HilbertLinesPerpendicularAt Geo t.1 a O :=
    hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
      (Geo := Geo)
      Tau
      t aTau OTau
      hTLocal

  exact
    And.intro
      hSAmbient
      hTAmbient

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: every Delta direction is perpendicular to the normal section

Let Sigma and Tau meet exactly in Delta, and let N be the normal
section at O with trace lines s and t.

Test77 proved that every line a contained in Delta through O is
perpendicular to both s and t.

This file localizes Euclid XI.4 dimension-correctly:

1. prove that a is not contained in N, using planar uniqueness of the
   perpendicular through O and the fact s != t;
2. construct one ambient 3-hyperplane Lambda containing N and a;
3. apply Euclid XI.4 only inside HyperplaneGeo4 Geo Lambda;
4. transfer the resulting line-plane perpendicularity back to ambient
   E4.

No ambient HilbertSpaceIncidence Geo instance is introduced.
-/

/--
If N contains two distinct lines s,t through O and a is perpendicular
to both, then a cannot itself lie in N.
-/
theorem hilbert4D_normal_section_transverse_line_not_in_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (N : Q.toHilbertSpacePrimitive.Plane)
    (s t a : Geo.Line)
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
    (hSA :
      HilbertLinesPerpendicularAt Geo s a O)
    (hTA :
      HilbertLinesPerpendicularAt Geo t a O) :
    Not (HilbertLineInPlane Geo a N) := by

  have hSExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      s O

  let S : Geo.Point :=
    Classical.choose hSExists

  have hSData :=
    Classical.choose_spec hSExists

  have hSO : Ne S O :=
    hSData.1

  have hSs : H.OnLine S s :=
    hSData.2

  have hTExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      t O

  let T : Geo.Point :=
    Classical.choose hTExists

  have hTData :=
    Classical.choose_spec hTExists

  have hTO : Ne T O :=
    hTData.1

  have hTt : H.OnLine T t :=
    hTData.2

  have hOST :
      Not (PrimCollinear Geo O S T) := by

    intro hCol

    have hTs :
        H.OnLine T s :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hSO.symm
        hOs hSs
        hCol

    have hEq :
        s = t :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O T
        hTO.symm
        s t
        hOs hTs
        hOt hTt

    exact hst hEq

  have hSN :
      Q.toHilbertSpacePrimitive.OnPlane S N :=
    hsN S hSs

  have hTN :
      Q.toHilbertSpacePrimitive.OnPlane T N :=
    htN T hTt

  intro haN

  let sN : PlaneLine Geo N :=
    Subtype.mk s hsN

  let tN : PlaneLine Geo N :=
    Subtype.mk t htN

  let aN : PlaneLine Geo N :=
    Subtype.mk a haN

  let ON : PlanePoint Geo N :=
    Subtype.mk O hON

  have hEqLocal :
      sN = tN :=
    planeGeo_perpendicular_same_foot_unique4_corrected
      (Geo := Geo)
      N
      O S T
      hON hSN hTN hOST
      sN tN aN ON
      hSA hTA

  apply hst

  exact
    congrArg
      (fun q : PlaneLine Geo N => q.1)
      hEqLocal

/--
A line a through O which is not contained in N can be localized together
with N in one genuine E4 hyperplane Lambda.
-/
theorem hilbert4D_plane_and_transverse_line_common_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    (N : Q.toHilbertSpacePrimitive.Plane)
    (s t a : Geo.Line)
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
    (hOa : H.OnLine O a)
    (haNotN :
      Not (HilbertLineInPlane Geo a N)) :
    exists Lambda : Q.Hyperplane,
      HilbertPlaneInHyperplane4 Geo N Lambda /\
      HilbertLineInHyperplane4 Geo a Lambda := by

  have hSExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      s O

  let S : Geo.Point :=
    Classical.choose hSExists

  have hSData :=
    Classical.choose_spec hSExists

  have hSO : Ne S O :=
    hSData.1

  have hSs : H.OnLine S s :=
    hSData.2

  have hTExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      t O

  let T : Geo.Point :=
    Classical.choose hTExists

  have hTData :=
    Classical.choose_spec hTExists

  have hTO : Ne T O :=
    hTData.1

  have hTt : H.OnLine T t :=
    hTData.2

  have hOST :
      Not (PrimCollinear Geo O S T) := by

    intro hCol

    have hTs :
        H.OnLine T s :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hSO.symm
        hOs hSs
        hCol

    have hEq :
        s = t :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O T
        hTO.symm
        s t
        hOs hTs
        hOt hTt

    exact hst hEq

  have hSN :
      Q.toHilbertSpacePrimitive.OnPlane S N :=
    hsN S hSs

  have hTN :
      Q.toHilbertSpacePrimitive.OnPlane T N :=
    htN T hTt

  have hAExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      a O

  let A : Geo.Point :=
    Classical.choose hAExists

  have hAData :=
    Classical.choose_spec hAExists

  have hAO : Ne A O :=
    hAData.1

  have hAa : H.OnLine A a :=
    hAData.2

  have hAoffN :
      Not
        (Q.toHilbertSpacePrimitive.OnPlane A N) := by

    intro hAN

    have haN :
        HilbertLineInPlane Geo a N :=
      H4I.line_in_plane
        O A
        hAO.symm
        a
        hOa hAa
        N
        hON hAN

    exact haNotN haN

  have hOSTA :
      Not (HilbertCoplanar4 Geo O S T A) :=
    hilbert4D_noncoplanar_of_off_plane_through_three_corrected
      (Geo := Geo)
      O S T A
      N
      hOST
      hON hSN hTN
      hAoffN

  have hLambdaExists :=
    H4I.hyperplane_through
      O S T A
      hOSTA

  let Lambda : Q.Hyperplane :=
    Classical.choose hLambdaExists

  have hLambdaData :=
    Classical.choose_spec hLambdaExists

  have hOLambda :
      Q.OnHyperplane O Lambda :=
    hLambdaData.1

  have hSLambda :
      Q.OnHyperplane S Lambda :=
    hLambdaData.2.1

  have hTLambda :
      Q.OnHyperplane T Lambda :=
    hLambdaData.2.2.1

  have hALambda :
      Q.OnHyperplane A Lambda :=
    hLambdaData.2.2.2

  have hNLambda :
      HilbertPlaneInHyperplane4 Geo N Lambda :=
    H4L.plane_in_hyperplane
      O S T
      hOST
      N
      hON hSN hTN
      Lambda
      hOLambda hSLambda hTLambda

  have haLambda :
      HilbertLineInHyperplane4 Geo a Lambda :=
    H4I.line_in_hyperplane
      O A
      hAO.symm
      a
      hOa hAa
      Lambda
      hOLambda hALambda

  exact
    Exists.intro Lambda
      (And.intro hNLambda haLambda)

/--
Every line a of Delta through O is perpendicular to the normal-section
plane N at O.

The invocation of Euclid XI.4 occurs only in a local
`HyperplaneGeo4 Geo Lambda`.
-/
theorem hilbert4D_delta_line_perpendicular_to_normal_section_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta N : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (s : HyperplaneLine4 Geo Sigma)
    (t : HyperplaneLine4 Geo Tau)
    (hSPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Sigma)
        s
        (Subtype.mk Delta hMeet.2.1)
        (Subtype.mk O (hMeet.2.1 O hODelta)))
    (hTPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Tau)
        t
        (Subtype.mk Delta hMeet.2.2.1)
        (Subtype.mk O (hMeet.2.2.1 O hODelta)))
    (hst : Ne s.1 t.1)
    (hON :
      Q.toHilbertSpacePrimitive.OnPlane O N)
    (hsN :
      HilbertLineInPlane Geo s.1 N)
    (htN :
      HilbertLineInPlane Geo t.1 N)
    (a : Geo.Line)
    (haDelta :
      HilbertLineInPlane Geo a Delta)
    (hOa :
      H.OnLine O a) :
    HilbertLinePerpendicularPlaneAt
      Geo a N O := by

  have hPerpTraces :=
    hilbert4D_delta_line_perpendicular_to_normal_section_traces_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta
      s t
      hSPerp hTPerp
      a haDelta hOa

  have hSA :
      HilbertLinesPerpendicularAt Geo s.1 a O :=
    hPerpTraces.1

  have hTA :
      HilbertLinesPerpendicularAt Geo t.1 a O :=
    hPerpTraces.2

  have hOs :
      H.OnLine O s.1 :=
    hSPerp.1

  have hOt :
      H.OnLine O t.1 :=
    hTPerp.1

  have haNotN :
      Not (HilbertLineInPlane Geo a N) :=
    hilbert4D_normal_section_transverse_line_not_in_plane_corrected
      (Geo := Geo)
      N
      s.1 t.1 a
      O
      hON
      hsN htN
      hOs hOt
      hst
      hSA hTA

  have hLambdaExists :=
    hilbert4D_plane_and_transverse_line_common_hyperplane_corrected
      (Geo := Geo)
      N
      s.1 t.1 a
      O
      hON
      hsN htN
      hOs hOt
      hst
      hOa
      haNotN

  let Lambda : Q.Hyperplane :=
    Classical.choose hLambdaExists

  have hLambdaData :=
    Classical.choose_spec hLambdaExists

  have hNLambda :
      HilbertPlaneInHyperplane4 Geo N Lambda :=
    hLambdaData.1

  have haLambda :
      HilbertLineInHyperplane4 Geo a Lambda :=
    hLambdaData.2

  have hsLambda :
      HilbertLineInHyperplane4 Geo s.1 Lambda := by
    intro X hXs
    exact
      hNLambda X
        (hsN X hXs)

  have htLambda :
      HilbertLineInHyperplane4 Geo t.1 Lambda := by
    intro X hXt
    exact
      hNLambda X
        (htN X hXt)

  have hOLambda :
      Q.OnHyperplane O Lambda :=
    hNLambda O hON

  let aL : HyperplaneLine4 Geo Lambda :=
    Subtype.mk a haLambda

  let sL : HyperplaneLine4 Geo Lambda :=
    Subtype.mk s.1 hsLambda

  let tL : HyperplaneLine4 Geo Lambda :=
    Subtype.mk t.1 htLambda

  let NL : HyperplanePlane4 Geo Lambda :=
    Subtype.mk N hNLambda

  let OL : HyperplanePoint4 Geo Lambda :=
    Subtype.mk O hOLambda

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
    Subtype.mk sL hsNL

  let tNL :
      PlaneLine
        (HyperplaneGeo4 Geo Lambda)
        NL :=
    Subtype.mk tL htNL

  let ONL :
      PlanePoint
        (HyperplaneGeo4 Geo Lambda)
        NL :=
    Subtype.mk OL hON

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

  have hSALocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        sL aL OL :=
    hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
      (Geo := Geo)
      Lambda
      sL aL OL
      hSA

  have hTALocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        tL aL OL :=
    hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
      (Geo := Geo)
      Lambda
      tL aL OL
      hTA

  have hASLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        aL sL OL :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := HyperplaneGeo4 Geo Lambda)
      sL aL OL
      hSALocal

  have hATLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        aL tL OL :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := HyperplaneGeo4 Geo Lambda)
      tL aL OL
      hTALocal

  have hPerpPlaneLocal :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Lambda)
        aL NL OL :=
    euclid_proposition_11_4
      (Geo := HyperplaneGeo4 Geo Lambda)
      NL
      sNL tNL
      aL
      ONL
      hstLocal
      hASLocal
      hATLocal

  refine
    And.intro
      hOa
      ?_

  refine
    And.intro
      hON
      ?_

  intro q hqN hOq

  have hqLambda :
      HilbertLineInHyperplane4 Geo q Lambda := by
    intro X hXq
    exact
      hNLambda X
        (hqN X hXq)

  let qL : HyperplaneLine4 Geo Lambda :=
    Subtype.mk q hqLambda

  have hqNL :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Lambda)
        qL NL := by
    intro X hXq
    exact hqN X.1 hXq

  have hPerpLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        aL qL OL :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := HyperplaneGeo4 Geo Lambda)
      hPerpPlaneLocal
      hqNL
      hOq

  exact
    hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
      (Geo := Geo)
      Lambda
      aL qL OL
      hPerpLocal

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: a spanning frame for one reflecting hyperplane

Assume Sigma and Tau meet exactly in Delta, O lies in Delta, and
s is the Sigma-trace line of the normal section at O.

This file constructs two independent lines a,b in Delta through O and
proves that a,b,s form a genuine 3-direction frame of Sigma.

Geometrically:

  a,b span Delta,
  s is transverse to Delta,
  therefore a,b,s span Sigma.

The proof remains synthetic and incidence-based.
-/

/--
For any point O of the common plane Delta and any line s in Sigma
perpendicular to Delta at O, there are two lines a,b in Delta through O
such that a,b,s form a spanning frame of Sigma.
-/
theorem hilbert4D_hyperplane_frame_from_common_plane_and_trace_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (s : HyperplaneLine4 Geo Sigma)
    (hSPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Sigma)
        s
        (Subtype.mk Delta hMeet.2.1)
        (Subtype.mk O (hMeet.2.1 O hODelta))) :
    exists a b : Geo.Line,
      HilbertLineInPlane Geo a Delta /\
      HilbertLineInPlane Geo b Delta /\
      H.OnLine O a /\
      H.OnLine O b /\
      Ne a b /\
      Hilbert4DHyperplaneFrameAt_corrected
        Geo Sigma O a b s.1 := by

  let DeltaSigma : HyperplanePlane4 Geo Sigma :=
    Subtype.mk Delta hMeet.2.1

  have hOSigma :
      Q.OnHyperplane O Sigma :=
    hMeet.2.1 O hODelta

  let OSigma : HyperplanePoint4 Geo Sigma :=
    Subtype.mk O hOSigma

  ----------------------------------------------------------------------
  -- Get three noncollinear points of Delta, inside local E3 = Sigma.
  ----------------------------------------------------------------------

  have hABCExists :=
    hilbert_three_noncollinear_on_plane
      (Geo := HyperplaneGeo4 Geo Sigma)
      DeltaSigma

  let A : HyperplanePoint4 Geo Sigma :=
    Classical.choose hABCExists

  have hBExists :=
    Classical.choose_spec hABCExists

  let B : HyperplanePoint4 Geo Sigma :=
    Classical.choose hBExists

  have hCExists :=
    Classical.choose_spec hBExists

  let C : HyperplanePoint4 Geo Sigma :=
    Classical.choose hCExists

  have hData :=
    Classical.choose_spec hCExists

  have hADelta := hData.1
  have hBDelta := hData.2.1
  have hCDelta := hData.2.2.1
  have hABC_local := hData.2.2.2

  have hABC :
      Not (PrimCollinear Geo A.1 B.1 C.1) :=
    hyperplaneGeo4_noncollinear_to_ambient_corrected
      (Geo := Geo)
      Sigma
      A B C
      hABC_local

  ----------------------------------------------------------------------
  -- Choose U,V in Delta such that O,U,V are noncollinear.
  ----------------------------------------------------------------------

  have hUV :
      exists U V : Geo.Point,
        Q.toHilbertSpacePrimitive.OnPlane U Delta /\
        Q.toHilbertSpacePrimitive.OnPlane V Delta /\
        Not (PrimCollinear Geo O U V) := by

    by_cases hOA : O = A.1

    case pos =>
      refine Exists.intro B.1 ?_
      refine Exists.intro C.1 ?_
      refine And.intro hBDelta ?_
      refine And.intro hCDelta ?_

      intro hOBC

      apply hABC

      simpa [hOA] using hOBC

    case neg =>
      by_cases hOAB :
          PrimCollinear Geo O A.1 B.1

      case pos =>
        refine Exists.intro A.1 ?_
        refine Exists.intro C.1 ?_
        refine And.intro hADelta ?_
        refine And.intro hCDelta ?_

        intro hOAC

        have hqExists :=
          HilbertPlaneIncidence.line_through
            (Geo := Geo)
            O A.1 hOA

        let q : Geo.Line :=
          Classical.choose hqExists

        have hqData :=
          Classical.choose_spec hqExists

        have hOq := hqData.1
        have hAq := hqData.2

        have hBq :
            H.OnLine B.1 q :=
          hilbert_on_line_of_primCollinear_with_two_on_line
            (Geo := Geo)
            hOA
            hOq hAq
            hOAB

        have hCq :
            H.OnLine C.1 q :=
          hilbert_on_line_of_primCollinear_with_two_on_line
            (Geo := Geo)
            hOA
            hOq hAq
            hOAC

        exact
          hABC
            (Exists.intro q
              (And.intro hAq
                (And.intro hBq hCq)))

      case neg =>
        exact
          Exists.intro A.1
            (Exists.intro B.1
              (And.intro hADelta
                (And.intro hBDelta hOAB)))

  let U : Geo.Point :=
    Classical.choose hUV

  have hVExists :=
    Classical.choose_spec hUV

  let V : Geo.Point :=
    Classical.choose hVExists

  have hDataUV :=
    Classical.choose_spec hVExists

  have hUDelta := hDataUV.1
  have hVDelta := hDataUV.2.1
  have hOUV := hDataUV.2.2

  have hOU : Ne O U :=
    hilbert_noncollinear_ne_first
      Geo O U V hOUV

  have hOV : Ne O V := by
    intro hEq

    apply hOUV

    have hqExists :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        O U hOU

    let q : Geo.Line :=
      Classical.choose hqExists

    have hqData :=
      Classical.choose_spec hqExists

    have hOq := hqData.1
    have hUq := hqData.2

    have hOqQ :
        H.OnLine O q := by
      change H.OnLine O (Classical.choose hqExists)
      exact hOq

    have hVq :
        H.OnLine V q :=
      Eq.mp
        (congrArg
          (fun X : Geo.Point => H.OnLine X q)
          hEq)
        hOqQ

    exact
      Exists.intro q
        (And.intro hOq
          (And.intro hUq hVq))

  ----------------------------------------------------------------------
  -- a = OU, b = OV, both lying in Delta.
  ----------------------------------------------------------------------

  have haExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      O U hOU

  let a : Geo.Line :=
    Classical.choose haExists

  have haData :=
    Classical.choose_spec haExists

  have hOa := haData.1
  have hUa := haData.2

  have hbExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      O V hOV

  let b : Geo.Line :=
    Classical.choose hbExists

  have hbData :=
    Classical.choose_spec hbExists

  have hOb := hbData.1
  have hVb := hbData.2

  have haDelta :
      HilbertLineInPlane Geo a Delta :=
    H4I.line_in_plane
      O U hOU
      a hOa hUa
      Delta
      hODelta hUDelta

  have hbDelta :
      HilbertLineInPlane Geo b Delta :=
    H4I.line_in_plane
      O V hOV
      b hOb hVb
      Delta
      hODelta hVDelta

  have hab : Ne a b := by

    intro hEq

    apply hOUV

    have hVa :
        H.OnLine V a := by
      rw [hEq]
      exact hVb

    exact
      Exists.intro a
        (And.intro hOa
          (And.intro hUa hVa))

  ----------------------------------------------------------------------
  -- Choose S on s away from O and prove S is outside Delta.
  ----------------------------------------------------------------------

  have hOs :
      H.OnLine O s.1 :=
    hSPerp.1

  have hSExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      s.1 O

  let S : Geo.Point :=
    Classical.choose hSExists

  have hSData :=
    Classical.choose_spec hSExists

  have hSO := hSData.1
  have hSs := hSData.2

  have hSoffDelta :
      Not
        (Q.toHilbertSpacePrimitive.OnPlane S Delta) := by

    intro hSDelta

    have hsDeltaAmbient :
        HilbertLineInPlane Geo s.1 Delta :=
      H4I.line_in_plane
        O S hSO.symm
        s.1
        hOs hSs
        Delta
        hODelta hSDelta

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

  have hOUVS :
      Not (HilbertCoplanar4 Geo O U V S) :=
    hilbert4D_noncoplanar_of_off_plane_through_three_corrected
      (Geo := Geo)
      O U V S
      Delta
      hOUV
      hODelta hUDelta hVDelta
      hSoffDelta

  ----------------------------------------------------------------------
  -- a,b,s all lie in Sigma, and O,U,V,S witness that they span it.
  ----------------------------------------------------------------------

  have haSigma :
      HilbertLineInHyperplane4 Geo a Sigma := by

    intro X hXa

    exact
      hMeet.2.1 X
        (haDelta X hXa)

  have hbSigma :
      HilbertLineInHyperplane4 Geo b Sigma := by

    intro X hXb

    exact
      hMeet.2.1 X
        (hbDelta X hXb)

  have hFrame :
      Hilbert4DHyperplaneFrameAt_corrected
        Geo Sigma O a b s.1 := by

    unfold Hilbert4DHyperplaneFrameAt_corrected

    refine
      And.intro haSigma ?_

    refine
      And.intro hbSigma ?_

    refine
      And.intro s.2 ?_

    refine
      And.intro hOa ?_

    refine
      And.intro hOb ?_

    refine
      And.intro hOs ?_

    exact
      Exists.intro U
        (Exists.intro V
          (Exists.intro S
            (And.intro hUa
              (And.intro hVb
                (And.intro hSs hOUVS)))))

  exact
    Exists.intro a
      (Exists.intro b
        (And.intro haDelta
          (And.intro hbDelta
            (And.intro hOa
              (And.intro hOb
                (And.intro hab hFrame))))))

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4: construct the Sigma-normal inside the normal section

Tests78-79 give the two ingredients:

* every Delta-line through O is perpendicular to the normal-section
  plane N;
* two independent Delta-lines a,b together with the Sigma trace s form
  a spanning frame of Sigma.

This file constructs, inside N, the line r through O perpendicular to
s.  Then:

* r is perpendicular to s by construction;
* a and b are perpendicular to N, so by local symmetry r is
  perpendicular to a and b;
* the corrected E4 hyperplane frame criterion from test76 therefore
  gives r perpendicular to Sigma.

The only genuinely new boundary used here is the explicitly isolated
`Hilbert4DHyperplanePerpendicularFrameCriterion_corrected`.
-/

/--
Dimension-safe symmetry step for a line perpendicular to an ambient
2-plane.

Assume l is perpendicular to N at O, r lies in N through O, and l is
known not to lie in N.  If N is marked by two distinct lines s,t through
O, then r is perpendicular to l.

The proof places N and l in one genuine 3-hyperplane Lambda and uses
perpendicular symmetry only inside `HyperplaneGeo4 Geo Lambda`.
-/
theorem hilbert4D_plane_perpendicular_line_symm_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (N : Q.toHilbertSpacePrimitive.Plane)
    (s t l r : Geo.Line)
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
    (hLperpN :
      HilbertLinePerpendicularPlaneAt Geo l N O)
    (hlNotN :
      Not (HilbertLineInPlane Geo l N))
    (hrN :
      HilbertLineInPlane Geo r N)
    (hOr :
      H.OnLine O r) :
    HilbertLinesPerpendicularAt Geo r l O := by

  have hOl :
      H.OnLine O l :=
    hLperpN.1

  have hLperpR :
      HilbertLinesPerpendicularAt Geo l r O :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hLperpN
      hrN
      hOr

  have hLambdaExists :=
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
      hlNotN

  let Lambda : Q.Hyperplane :=
    Classical.choose hLambdaExists

  have hLambdaData :=
    Classical.choose_spec hLambdaExists

  have hNLambda :
      HilbertPlaneInHyperplane4 Geo N Lambda :=
    hLambdaData.1

  have hlLambda :
      HilbertLineInHyperplane4 Geo l Lambda :=
    hLambdaData.2

  have hrLambda :
      HilbertLineInHyperplane4 Geo r Lambda := by
    intro X hXr
    exact
      hNLambda X
        (hrN X hXr)

  have hOLambda :
      Q.OnHyperplane O Lambda :=
    hNLambda O hON

  let lL : HyperplaneLine4 Geo Lambda :=
    Subtype.mk l hlLambda

  let rL : HyperplaneLine4 Geo Lambda :=
    Subtype.mk r hrLambda

  let OL : HyperplanePoint4 Geo Lambda :=
    Subtype.mk O hOLambda

  have hLperpRLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        lL rL OL :=
    hyperplaneGeo4_linesPerpendicularAt_of_ambient_corrected
      (Geo := Geo)
      Lambda
      lL rL OL
      hLperpR

  have hRperpLLocal :
      HilbertLinesPerpendicularAt
        (HyperplaneGeo4 Geo Lambda)
        rL lL OL :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := HyperplaneGeo4 Geo Lambda)
      lL rL OL
      hLperpRLocal

  exact
    hyperplaneGeo4_linesPerpendicularAt_to_ambient_corrected
      (Geo := Geo)
      Lambda
      rL lL OL
      hRperpLLocal

/--
For the normal section N of Sigma,Tau at O, construct a line r in N
through O which is perpendicular to Sigma.

This is the first theorem that consumes the corrected E4 hyperplane
frame criterion isolated in test76.
-/
theorem hilbert4D_normal_to_hyperplane_inside_normal_section_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta N : Q.toHilbertSpacePrimitive.Plane)
    (hMeet :
      HyperplanesMeetInPlane4_corrected
        Geo Sigma Tau Delta)
    (O : Geo.Point)
    (hODelta :
      Q.toHilbertSpacePrimitive.OnPlane O Delta)
    (s : HyperplaneLine4 Geo Sigma)
    (t : HyperplaneLine4 Geo Tau)
    (hSPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Sigma)
        s
        (Subtype.mk Delta hMeet.2.1)
        (Subtype.mk O (hMeet.2.1 O hODelta)))
    (hTPerp :
      HilbertLinePerpendicularPlaneAt
        (HyperplaneGeo4 Geo Tau)
        t
        (Subtype.mk Delta hMeet.2.2.1)
        (Subtype.mk O (hMeet.2.2.1 O hODelta)))
    (hst : Ne s.1 t.1)
    (hON :
      Q.toHilbertSpacePrimitive.OnPlane O N)
    (hsN :
      HilbertLineInPlane Geo s.1 N)
    (htN :
      HilbertLineInPlane Geo t.1 N) :
    exists r : Geo.Line,
      HilbertLineInPlane Geo r N /\
      H.OnLine O r /\
      HilbertLinesPerpendicularAt Geo r s.1 O /\
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O := by

  have hOs :
      H.OnLine O s.1 :=
    hSPerp.1

  have hOt :
      H.OnLine O t.1 :=
    hTPerp.1

  ----------------------------------------------------------------------
  -- Mark N by O,S,T so that its corrected planar Hilbert geometry is
  -- available.
  ----------------------------------------------------------------------

  have hSExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      s.1 O

  let S : Geo.Point :=
    Classical.choose hSExists

  have hSData :=
    Classical.choose_spec hSExists

  have hSO :
      Ne S O :=
    hSData.1

  have hSs :
      H.OnLine S s.1 :=
    hSData.2

  have hTExists :=
    hilbert4D_other_point_on_line_corrected
      (Geo := Geo)
      t.1 O

  let T : Geo.Point :=
    Classical.choose hTExists

  have hTData :=
    Classical.choose_spec hTExists

  have hTO :
      Ne T O :=
    hTData.1

  have hTt :
      H.OnLine T t.1 :=
    hTData.2

  have hOST :
      Not (PrimCollinear Geo O S T) := by

    intro hCol

    have hTs :
        H.OnLine T s.1 :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hSO.symm
        hOs hSs
        hCol

    have hEq :
        s.1 = t.1 :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O T
        hTO.symm
        s.1 t.1
        hOs hTs
        hOt hTt

    exact hst hEq

  have hSN :
      Q.toHilbertSpacePrimitive.OnPlane S N :=
    hsN S hSs

  have hTN :
      Q.toHilbertSpacePrimitive.OnPlane T N :=
    htN T hTt

  let : HilbertCongruence (PlaneGeo Geo N) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      N O S T
      hON hSN hTN hOST

  let ON : PlanePoint Geo N :=
    Subtype.mk O hON

  let SN : PlanePoint Geo N :=
    Subtype.mk S hSN

  let sN : PlaneLine Geo N :=
    Subtype.mk s.1 hsN

  have hSON :
      Ne SN ON := by
    intro hEq
    apply hSO
    exact congrArg Subtype.val hEq

  have hONsN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo N)
        ON sN := by
    exact hOs

  have hSNsN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo N)
        SN sN := by
    exact hSs

  ----------------------------------------------------------------------
  -- Erect r perpendicular to s inside PlaneGeo(N).
  ----------------------------------------------------------------------

  have hXExists :=
    HilbertOrder.between_extension
      (Geo := PlaneGeo Geo N)
      SN ON hSON

  let XN : PlanePoint Geo N :=
    Classical.choose hXExists

  have hSOX :=
    Classical.choose_spec hXExists

  have hYExists :=
    hilbert_right_angle_exists_nondegenerate
      (PlaneGeo Geo N)
      SN ON XN hSOX

  let YN : PlanePoint Geo N :=
    Classical.choose hYExists

  have hYData :=
    Classical.choose_spec hYExists

  have hNonSOY :
      Not
        (PrimCollinear
          (PlaneGeo Geo N)
          SN ON YN) :=
    hYData.1

  have hRightSOY :
      HilbertRightAngle
        (PlaneGeo Geo N)
        SN ON YN :=
    hYData.2

  have hOY :
      Ne ON YN := by

    intro hEq

    apply hNonSOY

    have hYNsN :
        HilbertIncidence.OnLine
          (Geo := PlaneGeo Geo N)
          YN sN := by
      rw [<- hEq]
      exact hONsN

    exact
      Exists.intro sN
        (And.intro hSNsN
          (And.intro hONsN hYNsN))

  have hrExists :=
    HilbertPlaneIncidence.line_through
      (Geo := PlaneGeo Geo N)
      ON YN hOY

  let rN : PlaneLine Geo N :=
    Classical.choose hrExists

  have hrData :=
    Classical.choose_spec hrExists

  have hONrN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo N)
        ON rN :=
    hrData.1

  have hYNrN :
      HilbertIncidence.OnLine
        (Geo := PlaneGeo Geo N)
        YN rN :=
    hrData.2

  have hSperpRLocal :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo N)
        sN rN ON := by

    exact
      And.intro hONsN
        (And.intro hONrN
          (Exists.intro SN
            (Exists.intro YN
              (And.intro hSON
                (And.intro hOY.symm
                  (And.intro hSNsN
                    (And.intro hYNrN
                      (And.intro
                        hNonSOY
                        hRightSOY))))))))

  have hRperpSLocal :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo N)
        rN sN ON :=
    hilbert_linesPerpendicularAt_symm_neutral
      (PlaneGeo Geo N)
      sN rN ON
      hSperpRLocal

  have hRperpS :
      HilbertLinesPerpendicularAt
        Geo rN.1 s.1 O :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      N rN sN ON).mp
      hRperpSLocal

  have hrN :
      HilbertLineInPlane Geo rN.1 N :=
    rN.2

  have hOr :
      H.OnLine O rN.1 :=
    hONrN

  ----------------------------------------------------------------------
  -- Build a,b in Delta such that a,b,s span Sigma.
  ----------------------------------------------------------------------

  have hFrameExists :=
    hilbert4D_hyperplane_frame_from_common_plane_and_trace_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta
      s hSPerp

  let a : Geo.Line :=
    Classical.choose hFrameExists

  have hBExists :=
    Classical.choose_spec hFrameExists

  let b : Geo.Line :=
    Classical.choose hBExists

  have hFrameData :=
    Classical.choose_spec hBExists

  have haDelta :=
    hFrameData.1

  have hbDelta :=
    hFrameData.2.1

  have hOa :=
    hFrameData.2.2.1

  have hOb :=
    hFrameData.2.2.2.1

  have hab :=
    hFrameData.2.2.2.2.1

  have hFrame :
      Hilbert4DHyperplaneFrameAt_corrected
        Geo Sigma O a b s.1 :=
    hFrameData.2.2.2.2.2

  ----------------------------------------------------------------------
  -- a and b are perpendicular to the whole normal-section plane N.
  ----------------------------------------------------------------------

  have hAperpN :
      HilbertLinePerpendicularPlaneAt Geo a N O :=
    hilbert4D_delta_line_perpendicular_to_normal_section_plane_corrected
      (Geo := Geo)
      Sigma Tau
      Delta N
      hMeet
      O hODelta
      s t
      hSPerp hTPerp
      hst
      hON
      hsN htN
      a
      haDelta
      hOa

  have hBperpN :
      HilbertLinePerpendicularPlaneAt Geo b N O :=
    hilbert4D_delta_line_perpendicular_to_normal_section_plane_corrected
      (Geo := Geo)
      Sigma Tau
      Delta N
      hMeet
      O hODelta
      s t
      hSPerp hTPerp
      hst
      hON
      hsN htN
      b
      hbDelta
      hOb

  ----------------------------------------------------------------------
  -- Record that a,b are transverse to N.  This is the same uniqueness
  -- argument used in test78.
  ----------------------------------------------------------------------

  have hATraces :=
    hilbert4D_delta_line_perpendicular_to_normal_section_traces_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta
      s t
      hSPerp hTPerp
      a haDelta hOa

  have hBTraces :=
    hilbert4D_delta_line_perpendicular_to_normal_section_traces_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hMeet
      O hODelta
      s t
      hSPerp hTPerp
      b hbDelta hOb

  have haNotN :
      Not (HilbertLineInPlane Geo a N) :=
    hilbert4D_normal_section_transverse_line_not_in_plane_corrected
      (Geo := Geo)
      N
      s.1 t.1 a
      O
      hON
      hsN htN
      hOs hOt
      hst
      hATraces.1
      hATraces.2

  have hbNotN :
      Not (HilbertLineInPlane Geo b N) :=
    hilbert4D_normal_section_transverse_line_not_in_plane_corrected
      (Geo := Geo)
      N
      s.1 t.1 b
      O
      hON
      hsN htN
      hOs hOt
      hst
      hBTraces.1
      hBTraces.2

  ----------------------------------------------------------------------
  -- Since r lies in N, symmetry gives r perpendicular to a and b.
  ----------------------------------------------------------------------

  have hRperpA :
      HilbertLinesPerpendicularAt Geo rN.1 a O :=
    hilbert4D_plane_perpendicular_line_symm_corrected
      (Geo := Geo)
      N
      s.1 t.1 a rN.1
      O
      hON
      hsN htN
      hOs hOt
      hst
      hAperpN
      haNotN
      hrN
      hOr

  have hRperpB :
      HilbertLinesPerpendicularAt Geo rN.1 b O :=
    hilbert4D_plane_perpendicular_line_symm_corrected
      (Geo := Geo)
      N
      s.1 t.1 b rN.1
      O
      hON
      hsN htN
      hOs hOt
      hst
      hBperpN
      hbNotN
      hrN
      hOr

  ----------------------------------------------------------------------
  -- The E4 XI.4 frame criterion now promotes the three line-line
  -- perpendicularities to r perpendicular Sigma.
  ----------------------------------------------------------------------

  have hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo rN.1 Sigma O :=
    hilbert4D_normal_of_spanning_perpendicular_frame_corrected
      (Geo := Geo)
      Sigma O
      rN.1 a b s.1
      hOr
      hFrame
      hRperpA
      hRperpB
      hRperpS

  exact
    Exists.intro rN.1
      (And.intro hrN
        (And.intro hOr
          (And.intro hRperpS hRNormal)))

end Geometry

import CGJteamLab.Proposition11_16
import CGJteamLab.Hilbert3DProportion

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.17

Three pairwise parallel planes cut two transversals in the orders

    A-E-B
    C-F-D.

Then

    AE : EB = CF : FD.

The proof is fully synthetic.

Architecture:

1. construct Euclid's auxiliary point O on AD in the middle plane
   using XI.16 and Pasch;
2. use XI.16 twice to obtain the two parallel section-line pairs;
3. apply planar VI.2 in the two explicit `PlaneGeo` slices;
4. transport both raw proportions back to ambient 3-space;
5. conclude by spatial V.11.

No segment arithmetic, quotient segment classes, numerical lengths,
division, multiplication, coordinates, or real numbers are used.
-/

theorem euclid_proposition_11_17_spatial_core
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi0 pi1 pi2 : S.Plane)
    (A E B C F D O : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallelIncidence Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi2)
    (hApi0 : S.OnPlane A pi0)
    (hCpi0 : S.OnPlane C pi0)
    (hEpi1 : S.OnPlane E pi1)
    (hFpi1 : S.OnPlane F pi1)
    (hOpi1 : S.OnPlane O pi1)
    (hBpi2 : S.OnPlane B pi2)
    (hDpi2 : S.OnPlane D pi2)
    (hAEB : Geo.Between A E B)
    (hCFD : Geo.Between C F D)
    (hAOD : Geo.Between A O D)
    (hBD : Ne B D)
    (hAC : Ne A C) :
    exists lEO lBD lAC lOF : Geo.Line,
      H.OnLine E lEO /\
      H.OnLine O lEO /\
      H.OnLine B lBD /\
      H.OnLine D lBD /\
      HilbertSpaceLinesParallel Geo lEO lBD /\
      H.OnLine A lAC /\
      H.OnLine C lAC /\
      H.OnLine O lOF /\
      H.OnLine F lOF /\
      HilbertSpaceLinesParallel Geo lAC lOF := by

  ----------------------------------------------------------------------
  -- Ambient order data.
  ----------------------------------------------------------------------

  have hAEBData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A E B hAEB

  have hCFDData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C F D hCFD

  have hAODData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O D hAOD

  have hAB : Ne A B :=
    hAEBData.2.2.1

  have hCD : Ne C D :=
    hCFDData.2.2.1

  have hAD : Ne A D :=
    hAODData.2.2.1

  have hAEBcol :
      PrimCollinear Geo A E B :=
    hAEBData.2.2.2.1

  have hCFDcol :
      PrimCollinear Geo C F D :=
    hCFDData.2.2.2.1

  have hAODcol :
      PrimCollinear Geo A O D :=
    hAODData.2.2.2.1

  have hABEcol :
      PrimCollinear Geo A B E :=
    PrimCollinearRotate
      Geo A E B hAEBcol

  have hCDFcol :
      PrimCollinear Geo C D F :=
    PrimCollinearRotate
      Geo C F D hCFDcol

  have hADOcol :
      PrimCollinear Geo A D O :=
    PrimCollinearRotate
      Geo A O D hAODcol

  ----------------------------------------------------------------------
  -- The outer planes are disjoint, hence A is outside pi2 and
  -- D is outside pi0.
  ----------------------------------------------------------------------

  have hAnotPi2 :
      Not (S.OnPlane A pi2) := by
    intro hApi2
    apply hParallel02
    exact
      Exists.intro A
        (And.intro hApi0 hApi2)

  have hDnotPi0 :
      Not (S.OnPlane D pi0) := by
    intro hDpi0
    apply hParallel02
    exact
      Exists.intro D
        (And.intro hDpi0 hDpi2)

  ----------------------------------------------------------------------
  -- sigma1 = plane(A,B,D).
  ----------------------------------------------------------------------

  have hABD :
      Not (PrimCollinear Geo A B D) := by
    intro hCol
    apply hAnotPi2
    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi2
        B D A
        hBD
        hBpi2 hDpi2
        (PrimCollinearCycle Geo A B D hCol)

  cases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B D hABD with
  | intro sigma1 hSigma1 =>

      have hAsigma1 : S.OnPlane A sigma1 :=
        hSigma1.1

      have hBsigma1 : S.OnPlane B sigma1 :=
        hSigma1.2.1

      have hDsigma1 : S.OnPlane D sigma1 :=
        hSigma1.2.2

      have hEsigma1 :
          S.OnPlane E sigma1 :=
        hilbert_onPlane_of_primCollinear_with_two_on_plane
          (Geo := Geo)
          sigma1
          A B E
          hAB
          hAsigma1 hBsigma1
          hABEcol

      have hOsigma1 :
          S.OnPlane O sigma1 :=
        hilbert_onPlane_of_primCollinear_with_two_on_plane
          (Geo := Geo)
          sigma1
          A D O
          hAD
          hAsigma1 hDsigma1
          hADOcol

      ------------------------------------------------------------------
      -- sigma2 = plane(A,C,D).
      ------------------------------------------------------------------

      have hACD :
          Not (PrimCollinear Geo A C D) := by
        intro hCol
        apply hDnotPi0
        exact
          hilbert_onPlane_of_primCollinear_with_two_on_plane
            (Geo := Geo)
            pi0
            A C D
            hAC
            hApi0 hCpi0
            hCol

      cases
          HilbertSpaceIncidence.plane_through
            (Geo := Geo)
            A C D hACD with
      | intro sigma2 hSigma2 =>

          have hAsigma2 : S.OnPlane A sigma2 :=
            hSigma2.1

          have hCsigma2 : S.OnPlane C sigma2 :=
            hSigma2.2.1

          have hDsigma2 : S.OnPlane D sigma2 :=
            hSigma2.2.2

          have hFsigma2 :
              S.OnPlane F sigma2 :=
            hilbert_onPlane_of_primCollinear_with_two_on_plane
              (Geo := Geo)
              sigma2
              C D F
              hCD
              hCsigma2 hDsigma2
              hCDFcol

          have hOsigma2 :
              S.OnPlane O sigma2 :=
            hilbert_onPlane_of_primCollinear_with_two_on_plane
              (Geo := Geo)
              sigma2
              A D O
              hAD
              hAsigma2 hDsigma2
              hADOcol

          --------------------------------------------------------------
          -- First XI.16:
          --
          -- pi1 || pi2 cut by sigma1.
          --------------------------------------------------------------

          cases
              euclid_proposition_11_16
                (Geo := Geo)
                pi1 pi2 sigma1
                E B
                hParallel12
                hEpi1 hEsigma1
                hBpi2 hBsigma1 with
          | intro lEO hFirst =>
              cases hFirst with
              | intro lBD hData1 =>

                  have hElEO : H.OnLine E lEO :=
                    hData1.1

                  have hBlBD : H.OnLine B lBD :=
                    hData1.2.1

                  have hMeetEO :=
                    hData1.2.2.1

                  have hMeetBD :=
                    hData1.2.2.2.1

                  have hParallelEOBD :=
                    hData1.2.2.2.2

                  have hOlEO :
                      H.OnLine O lEO := by
                    exact
                      (hMeetEO O).mp
                        (And.intro hOpi1 hOsigma1)

                  have hDlBD :
                      H.OnLine D lBD := by
                    exact
                      (hMeetBD D).mp
                        (And.intro hDpi2 hDsigma1)

                  ------------------------------------------------------
                  -- Second XI.16:
                  --
                  -- pi0 || pi1 cut by sigma2.
                  ------------------------------------------------------

                  cases
                      euclid_proposition_11_16
                        (Geo := Geo)
                        pi0 pi1 sigma2
                        A O
                        hParallel01
                        hApi0 hAsigma2
                        hOpi1 hOsigma2 with
                  | intro lAC hSecond =>
                      cases hSecond with
                      | intro lOF hData2 =>

                          have hAlAC : H.OnLine A lAC :=
                            hData2.1

                          have hOlOF : H.OnLine O lOF :=
                            hData2.2.1

                          have hMeetAC :=
                            hData2.2.2.1

                          have hMeetOF :=
                            hData2.2.2.2.1

                          have hParallelACOF :=
                            hData2.2.2.2.2

                          have hClAC :
                              H.OnLine C lAC := by
                            exact
                              (hMeetAC C).mp
                                (And.intro hCpi0 hCsigma2)

                          have hFlOF :
                              H.OnLine F lOF := by
                            exact
                              (hMeetOF F).mp
                                (And.intro hFpi1 hFsigma2)

                          refine Exists.intro lEO ?_
                          refine Exists.intro lBD ?_
                          refine Exists.intro lAC ?_
                          refine Exists.intro lOF ?_
                          refine And.intro hElEO ?_
                          refine And.intro hOlEO ?_
                          refine And.intro hBlBD ?_
                          refine And.intro hDlBD ?_
                          refine And.intro hParallelEOBD ?_
                          refine And.intro hAlAC ?_
                          refine And.intro hClAC ?_
                          refine And.intro hOlOF ?_
                          refine And.intro hFlOF ?_
                          exact hParallelACOF


theorem euclid_proposition_11_17_with_O_core
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (hVI2 :
      forall tau : S.Plane,
        HilbertVI2Raw (PlaneGeo Geo tau))
    (pi0 pi1 pi2 : S.Plane)
    (A E B C F D O : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallelIncidence Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi2)
    (hApi0 : S.OnPlane A pi0)
    (hCpi0 : S.OnPlane C pi0)
    (hEpi1 : S.OnPlane E pi1)
    (hFpi1 : S.OnPlane F pi1)
    (hOpi1 : S.OnPlane O pi1)
    (hBpi2 : S.OnPlane B pi2)
    (hDpi2 : S.OnPlane D pi2)
    (hAEB : Geo.Between A E B)
    (hCFD : Geo.Between C F D)
    (hAOD : Geo.Between A O D)
    (hEO : Ne E O)
    (hBD : Ne B D)
    (hOF : Ne O F)
    (hAC : Ne A C) :
    HilbertSpaceSegmentProportionRaw
      Geo
      A E
      E B
      C F
      F D := by

  ----------------------------------------------------------------------
  -- Spatial XI.16 core.
  ----------------------------------------------------------------------

  cases
      euclid_proposition_11_17_spatial_core
        (Geo := Geo)
        pi0 pi1 pi2
        A E B C F D O
        hParallel01
        hParallel12
        hParallel02
        hApi0 hCpi0
        hEpi1 hFpi1 hOpi1
        hBpi2 hDpi2
        hAEB hCFD hAOD
        hBD hAC with
  | intro lEO h0 =>
      cases h0 with
      | intro lBD h1 =>
          cases h1 with
          | intro lAC h2 =>
              cases h2 with
              | intro lOF hData =>

                  have hElEO := hData.1
                  have hOlEO := hData.2.1
                  have hBlBD := hData.2.2.1
                  have hDlBD := hData.2.2.2.1
                  have hParallelEOBD := hData.2.2.2.2.1
                  have hAlAC := hData.2.2.2.2.2.1
                  have hClAC := hData.2.2.2.2.2.2.1
                  have hOlOF := hData.2.2.2.2.2.2.2.1
                  have hFlOF := hData.2.2.2.2.2.2.2.2.1
                  have hParallelACOF := hData.2.2.2.2.2.2.2.2.2

                  ------------------------------------------------------
                  -- First section plane: EO || BD.
                  ------------------------------------------------------

                  cases hParallelEOBD with
                  | intro tau1 hTau1 =>

                      have hlEOtau1 := hTau1.1
                      have hlBDtau1 := hTau1.2.1
                      have hDisjoint1 := hTau1.2.2

                      have hEtau1 : S.OnPlane E tau1 :=
                        hlEOtau1 E hElEO

                      have hOtau1 : S.OnPlane O tau1 :=
                        hlEOtau1 O hOlEO

                      have hBtau1 : S.OnPlane B tau1 :=
                        hlBDtau1 B hBlBD

                      have hDtau1 : S.OnPlane D tau1 :=
                        hlBDtau1 D hDlBD

                      have hAEBData :=
                        HilbertSpaceOrder.between_incidence
                          (Geo := Geo)
                          A E B hAEB

                      have hEB : Ne E B :=
                        hAEBData.2.1

                      have hAEBcol :
                          PrimCollinear Geo A E B :=
                        hAEBData.2.2.2.1

                      have hEBAcol :
                          PrimCollinear Geo E B A :=
                        PrimCollinearCycle
                          Geo A E B hAEBcol

                      have hAtau1 : S.OnPlane A tau1 :=
                        hilbert_onPlane_of_primCollinear_with_two_on_plane
                          (Geo := Geo)
                          tau1
                          E B A
                          hEB
                          hEtau1 hBtau1
                          hEBAcol

                      have hFirstPlane :
                          HilbertSegmentProportionRaw
                            (PlaneGeo Geo tau1)
                            (Subtype.mk A hAtau1)
                            (Subtype.mk E hEtau1)
                            (Subtype.mk E hEtau1)
                            (Subtype.mk B hBtau1)
                            (Subtype.mk A hAtau1)
                            (Subtype.mk O hOtau1)
                            (Subtype.mk O hOtau1)
                            (Subtype.mk D hDtau1) :=
                        hilbertVI2Raw_of_ambient_disjoint_carriers
                          (Geo := Geo)
                          tau1
                          A E B O D
                          hAtau1 hEtau1 hBtau1 hOtau1 hDtau1
                          hAEB hAOD
                          lEO lBD
                          hlEOtau1 hlBDtau1
                          hElEO hOlEO
                          hBlBD hDlBD
                          hEO hBD
                          hDisjoint1
                          (hVI2 tau1)

                      have hFirstSpace :
                          HilbertSpaceSegmentProportionRaw
                            Geo
                            A E
                            E B
                            A O
                            O D :=
                        hilbertSegmentProportionRaw_to_space
                          (Geo := Geo)
                          tau1
                          (Subtype.mk A hAtau1)
                          (Subtype.mk E hEtau1)
                          (Subtype.mk E hEtau1)
                          (Subtype.mk B hBtau1)
                          (Subtype.mk A hAtau1)
                          (Subtype.mk O hOtau1)
                          (Subtype.mk O hOtau1)
                          (Subtype.mk D hDtau1)
                          hFirstPlane

                      --------------------------------------------------
                      -- Second section plane: AC || OF.
                      --------------------------------------------------

                      cases hParallelACOF with
                      | intro tau2 hTau2 =>

                          have hlACtau2 := hTau2.1
                          have hlOFtau2 := hTau2.2.1
                          have hDisjoint2 := hTau2.2.2

                          have hAtau2 : S.OnPlane A tau2 :=
                            hlACtau2 A hAlAC

                          have hCtau2 : S.OnPlane C tau2 :=
                            hlACtau2 C hClAC

                          have hOtau2 : S.OnPlane O tau2 :=
                            hlOFtau2 O hOlOF

                          have hFtau2 : S.OnPlane F tau2 :=
                            hlOFtau2 F hFlOF

                          have hAODData :=
                            HilbertSpaceOrder.between_incidence
                              (Geo := Geo)
                              A O D hAOD

                          have hAO : Ne A O :=
                            hAODData.1

                          have hAODcol :
                              PrimCollinear Geo A O D :=
                            hAODData.2.2.2.1

                          have hDtau2 : S.OnPlane D tau2 :=
                            hilbert_onPlane_of_primCollinear_with_two_on_plane
                              (Geo := Geo)
                              tau2
                              A O D
                              hAO
                              hAtau2 hOtau2
                              hAODcol

                          have hDOA : Geo.Between D O A :=
                            hAODData.2.2.2.2

                          have hCFDData :=
                            HilbertSpaceOrder.between_incidence
                              (Geo := Geo)
                              C F D hCFD

                          have hDFC : Geo.Between D F C :=
                            hCFDData.2.2.2.2

                          let Dp : PlanePoint Geo tau2 :=
                            Subtype.mk D hDtau2

                          let Op : PlanePoint Geo tau2 :=
                            Subtype.mk O hOtau2

                          let Ap : PlanePoint Geo tau2 :=
                            Subtype.mk A hAtau2

                          let Fp : PlanePoint Geo tau2 :=
                            Subtype.mk F hFtau2

                          let Cp : PlanePoint Geo tau2 :=
                            Subtype.mk C hCtau2

                          have hOFp : Ne Op Fp := by
                            intro h
                            apply hOF
                            exact congrArg Subtype.val h

                          have hACp : Ne Ap Cp := by
                            intro h
                            apply hAC
                            exact congrArg Subtype.val h

                          have hDisjoint2Symm :
                              HilbertLinesDisjoint Geo lOF lAC := by
                            intro hMeet
                            cases hMeet with
                            | intro X hX =>
                                exact
                                  hDisjoint2
                                    (Exists.intro X
                                      (And.intro hX.2 hX.1))

                          have hParallelPlane2 :
                              (PlaneGeo Geo tau2).Parallel
                                Op Fp Ap Cp :=
                            planeGeo_parallel_of_ambient_disjoint_carriers
                              (Geo := Geo)
                              tau2
                              lOF lAC
                              Op Fp Ap Cp
                              hOFp hACp
                              hlOFtau2 hlACtau2
                              hOlOF hFlOF
                              hAlAC hClAC
                              hDisjoint2Symm

                          have hDOAp :
                              (PlaneGeo Geo tau2).Between
                                Dp Op Ap := by
                            exact hDOA

                          have hDFCp :
                              (PlaneGeo Geo tau2).Between
                                Dp Fp Cp := by
                            exact hDFC

                          have hSecondReciprocal :
                              HilbertSegmentProportionRaw
                                (PlaneGeo Geo tau2)
                                Op Ap
                                Dp Op
                                Fp Cp
                                Dp Fp :=
                            ((hVI2 tau2)
                              Dp Op Ap Fp Cp
                              hDOAp hDFCp
                              hParallelPlane2).2

                          have hSecondPlane :
                              HilbertSegmentProportionRaw
                                (PlaneGeo Geo tau2)
                                Ap Op
                                Op Dp
                                Cp Fp
                                Fp Dp :=
                            hilbertSegmentProportionRaw_reverse_all
                              (Geo := PlaneGeo Geo tau2)
                              Op Ap
                              Dp Op
                              Fp Cp
                              Dp Fp
                              hSecondReciprocal

                          have hSecondSpace :
                              HilbertSpaceSegmentProportionRaw
                                Geo
                                A O
                                O D
                                C F
                                F D := by

                            have hTransport :=
                              hilbertSegmentProportionRaw_to_space
                                (Geo := Geo)
                                tau2
                                Ap Op
                                Op Dp
                                Cp Fp
                                Fp Dp
                                hSecondPlane

                            simpa [Ap, Op, Dp, Cp, Fp] using hTransport

                          ------------------------------------------------
                          -- V.11.
                          ------------------------------------------------

                          exact
                            hilbertSpaceSegmentProportionRaw_trans
                              (Geo := Geo)
                              A E
                              E B
                              A O
                              O D
                              C F
                              F D
                              hFirstSpace
                              hSecondSpace


theorem euclid_proposition_11_17_with_O
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (hVI2 :
      forall tau : S.Plane,
        HilbertVI2Raw (PlaneGeo Geo tau))
    (pi0 pi1 pi2 : S.Plane)
    (A E B C F D O : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallelIncidence Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi2)
    (hApi0 : S.OnPlane A pi0)
    (hCpi0 : S.OnPlane C pi0)
    (hEpi1 : S.OnPlane E pi1)
    (hFpi1 : S.OnPlane F pi1)
    (hOpi1 : S.OnPlane O pi1)
    (hBpi2 : S.OnPlane B pi2)
    (hDpi2 : S.OnPlane D pi2)
    (hAEB : Geo.Between A E B)
    (hCFD : Geo.Between C F D)
    (hAOD : Geo.Between A O D)
    (hBD : Ne B D)
    (hAC : Ne A C) :
    HilbertSpaceSegmentProportionRaw
      Geo
      A E
      E B
      C F
      F D := by

  have hAEBData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A E B hAEB

  have hCFDData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C F D hCFD

  have hAODData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O D hAOD

  have hAE : Ne A E :=
    hAEBData.1

  have hFD : Ne F D :=
    hCFDData.2.1

  have hAEBcol :
      PrimCollinear Geo A E B :=
    hAEBData.2.2.2.1

  have hCFDcol :
      PrimCollinear Geo C F D :=
    hCFDData.2.2.2.1

  have hAODcol :
      PrimCollinear Geo A O D :=
    hAODData.2.2.2.1

  ----------------------------------------------------------------------
  -- A is not on the second outer plane.
  ----------------------------------------------------------------------

  have hAnotPi2 :
      Not (S.OnPlane A pi2) := by
    intro hApi2
    apply hParallel02
    exact
      Exists.intro A
        (And.intro hApi0 hApi2)

  ----------------------------------------------------------------------
  -- D is not on the first outer plane.
  ----------------------------------------------------------------------

  have hDnotPi0 :
      Not (S.OnPlane D pi0) := by
    intro hDpi0
    apply hParallel02
    exact
      Exists.intro D
        (And.intro hDpi0 hDpi2)

  ----------------------------------------------------------------------
  -- E != O.
  --
  -- Otherwise AB and AD meet at the two distinct points A,E, hence
  -- B,D,A are collinear. Since B,D lie in pi2 and B != D, A would lie
  -- in pi2, contradicting pi0 || pi2.
  ----------------------------------------------------------------------

  have hEO :
      Ne E O := by
    intro hEq
    subst O

    cases hAEBcol with
    | intro q hq =>

        have hAq := hq.1
        have hEq := hq.2.1
        have hBq := hq.2.2

        have hDq :
            H.OnLine D q :=
          hilbert_collinear_on_line
            Geo
            A E D
            q
            hAE
            hAq hEq
            hAODcol

        have hBED :
            PrimCollinear Geo B D A :=
          Exists.intro q
            (And.intro hBq
              (And.intro hDq hAq))

        apply hAnotPi2

        exact
          hilbert_onPlane_of_primCollinear_with_two_on_plane
            (Geo := Geo)
            pi2
            B D A
            hBD
            hBpi2 hDpi2
            hBED

  ----------------------------------------------------------------------
  -- O != F.
  --
  -- Otherwise AD and CD meet at the two distinct points F,D, hence
  -- A,C,D are collinear. Since A,C lie in pi0 and A != C, D would lie
  -- in pi0, contradicting pi0 || pi2.
  ----------------------------------------------------------------------

  have hOF :
      Ne O F := by
    intro hEq
    subst O

    cases hCFDcol with
    | intro q hq =>

        have hCq := hq.1
        have hFq := hq.2.1
        have hDq := hq.2.2

        have hFDA :
            PrimCollinear Geo F D A :=
          PrimCollinearCycle
            Geo A F D hAODcol

        have hAq :
            H.OnLine A q :=
          hilbert_collinear_on_line
            Geo
            F D A
            q
            hFD
            hFq hDq
            hFDA

        have hACD :
            PrimCollinear Geo A C D :=
          Exists.intro q
            (And.intro hAq
              (And.intro hCq hDq))

        apply hDnotPi0

        exact
          hilbert_onPlane_of_primCollinear_with_two_on_plane
            (Geo := Geo)
            pi0
            A C D
            hAC
            hApi0 hCpi0
            hACD

  exact
    euclid_proposition_11_17_with_O_core
      (Geo := Geo)
      hVI2
      pi0 pi1 pi2
      A E B C F D O
      hParallel01
      hParallel12
      hParallel02
      hApi0 hCpi0
      hEpi1 hFpi1 hOpi1
      hBpi2 hDpi2
      hAEB hCFD hAOD
      hEO hBD hOF hAC


theorem euclid_proposition_11_17_construct_O
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi0 pi1 pi2 : S.Plane)
    (A E B D : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallelIncidence Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi2)
    (hApi0 : S.OnPlane A pi0)
    (hEpi1 : S.OnPlane E pi1)
    (hBpi2 : S.OnPlane B pi2)
    (hDpi2 : S.OnPlane D pi2)
    (hAEB : Geo.Between A E B)
    (hBD : Ne B D) :
    exists O : Geo.Point,
      Geo.Between A O D /\
      S.OnPlane O pi1 := by

  have hAEBData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A E B hAEB

  have hAB : Ne A B :=
    hAEBData.2.2.1

  have hAEBcol :
      PrimCollinear Geo A E B :=
    hAEBData.2.2.2.1

  ----------------------------------------------------------------------
  -- A is outside pi2, so A,B,D are noncollinear.
  ----------------------------------------------------------------------

  have hAnotPi2 :
      Not (S.OnPlane A pi2) := by
    intro hApi2
    apply hParallel02
    exact
      Exists.intro A
        (And.intro hApi0 hApi2)

  have hABD :
      Not (PrimCollinear Geo A B D) := by
    intro hCol
    apply hAnotPi2
    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi2
        B D A
        hBD
        hBpi2 hDpi2
        (PrimCollinearCycle Geo A B D hCol)

  ----------------------------------------------------------------------
  -- sigma = plane(A,B,D), and E lies in sigma because A-E-B.
  ----------------------------------------------------------------------

  cases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B D hABD with
  | intro sigma hSigma =>

      have hAsigma : S.OnPlane A sigma :=
        hSigma.1

      have hBsigma : S.OnPlane B sigma :=
        hSigma.2.1

      have hDsigma : S.OnPlane D sigma :=
        hSigma.2.2

      have hABEcol :
          PrimCollinear Geo A B E :=
        PrimCollinearRotate
          Geo A E B hAEBcol

      have hEsigma :
          S.OnPlane E sigma :=
        hilbert_onPlane_of_primCollinear_with_two_on_plane
          (Geo := Geo)
          sigma
          A B E
          hAB
          hAsigma hBsigma
          hABEcol

      ------------------------------------------------------------------
      -- XI.16 for pi1 || pi2 cut by sigma.
      ------------------------------------------------------------------

      cases
          euclid_proposition_11_16
            (Geo := Geo)
            pi1 pi2 sigma
            E B
            hParallel12
            hEpi1 hEsigma
            hBpi2 hBsigma with
      | intro lE hFirst =>
          cases hFirst with
          | intro lBD hData =>

              have hElE : H.OnLine E lE :=
                hData.1

              have hBlBD : H.OnLine B lBD :=
                hData.2.1

              have hMeetE :=
                hData.2.2.1

              have hMeetBD :=
                hData.2.2.2.1

              have hParallelLines :=
                hData.2.2.2.2

              ----------------------------------------------------------------
              -- Both XI.16 section lines really lie in sigma.
              ----------------------------------------------------------------

              have hlEsigma :
                  HilbertLineInPlane Geo lE sigma := by
                intro X hXlE
                exact ((hMeetE X).mpr hXlE).2

              have hlBDsigma :
                  HilbertLineInPlane Geo lBD sigma := by
                intro X hXlBD
                exact ((hMeetBD X).mpr hXlBD).2

              have hlEpi1 :
                  HilbertLineInPlane Geo lE pi1 := by
                intro X hXlE
                exact ((hMeetE X).mpr hXlE).1

              ----------------------------------------------------------------
              -- D also lies on the second section line.
              ----------------------------------------------------------------

              have hDlBD :
                  H.OnLine D lBD := by
                exact
                  (hMeetBD D).mp
                    (And.intro hDpi2 hDsigma)

              ----------------------------------------------------------------
              -- The first section line is disjoint from the BD section line.
              ----------------------------------------------------------------

              have hDisjoint :
                  HilbertLinesDisjoint Geo lE lBD := by
                cases hParallelLines with
                | intro tau hTau =>
                    exact hTau.2.2

              ----------------------------------------------------------------
              -- The three triangle vertices are off lE.
              ----------------------------------------------------------------

              have hAnotPi1 :
                  Not (S.OnPlane A pi1) := by
                intro hApi1
                apply hParallel01
                exact
                  Exists.intro A
                    (And.intro hApi0 hApi1)

              have hBnotPi1 :
                  Not (S.OnPlane B pi1) := by
                intro hBpi1
                apply hParallel12
                exact
                  Exists.intro B
                    (And.intro hBpi1 hBpi2)

              have hDnotPi1 :
                  Not (S.OnPlane D pi1) := by
                intro hDpi1
                apply hParallel12
                exact
                  Exists.intro D
                    (And.intro hDpi1 hDpi2)

              have hAnotL :
                  Not (H.OnLine A lE) := by
                intro hAlE
                exact hAnotPi1 (hlEpi1 A hAlE)

              have hBnotL :
                  Not (H.OnLine B lE) := by
                intro hBlE
                exact hBnotPi1 (hlEpi1 B hBlE)

              have hDnotL :
                  Not (H.OnLine D lE) := by
                intro hDlE
                exact hDnotPi1 (hlEpi1 D hDlE)

              ----------------------------------------------------------------
              -- lE meets the open side AB at E.
              ----------------------------------------------------------------

              have hMeetAB :
                  HilbertSegmentMeetsLine Geo A B lE :=
                Exists.intro E
                  (And.intro hAEB hElE)

              ----------------------------------------------------------------
              -- Ambient Pasch in sigma.
              ----------------------------------------------------------------

              have hPasch :=
                HilbertSpaceOrder.pasch_in_plane
                  (Geo := Geo)
                  sigma
                  A B D
                  hAsigma hBsigma hDsigma
                  hABD
                  lE
                  hlEsigma
                  hAnotL hBnotL hDnotL
                  hMeetAB

              have hMeetAD :
                  HilbertSegmentMeetsLine Geo A D lE := by

                cases hPasch with
                | inl hAD =>
                    exact hAD

                | inr hBDMeet =>

                    cases hBDMeet with
                    | intro X hX =>

                        have hBXD :
                            Geo.Between B X D :=
                          hX.1

                        have hXlE :
                            H.OnLine X lE :=
                          hX.2

                        have hBXDData :=
                          HilbertSpaceOrder.between_incidence
                            (Geo := Geo)
                            B X D hBXD

                        have hBXDcol :
                            PrimCollinear Geo B X D :=
                          hBXDData.2.2.2.1

                        have hBDXcol :
                            PrimCollinear Geo B D X :=
                          PrimCollinearRotate
                            Geo B X D hBXDcol

                        have hXlBD :
                            H.OnLine X lBD :=
                          hilbert_on_line_of_primCollinear_with_two_on_line
                            (Geo := Geo)
                            hBD
                            hBlBD hDlBD
                            hBDXcol

                        exact
                          False.elim
                            (hDisjoint
                              (Exists.intro X
                                (And.intro hXlE hXlBD)))

              ----------------------------------------------------------------
              -- The Pasch intersection point is the required O.
              ----------------------------------------------------------------

              cases hMeetAD with
              | intro O hO =>

                  have hAOD :
                      Geo.Between A O D :=
                    hO.1

                  have hOlE :
                      H.OnLine O lE :=
                    hO.2

                  have hOpi1 :
                      S.OnPlane O pi1 :=
                    hlEpi1 O hOlE

                  exact
                    Exists.intro O
                      (And.intro hAOD hOpi1)


theorem euclid_proposition_11_17
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (hVI2 :
      forall tau : S.Plane,
        HilbertVI2Raw (PlaneGeo Geo tau))
    (pi0 pi1 pi2 : S.Plane)
    (A E B C F D : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallelIncidence Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallelIncidence Geo pi0 pi2)
    (hApi0 : S.OnPlane A pi0)
    (hCpi0 : S.OnPlane C pi0)
    (hEpi1 : S.OnPlane E pi1)
    (hFpi1 : S.OnPlane F pi1)
    (hBpi2 : S.OnPlane B pi2)
    (hDpi2 : S.OnPlane D pi2)
    (hAEB : Geo.Between A E B)
    (hCFD : Geo.Between C F D)
    (hBD : Ne B D)
    (hAC : Ne A C) :
    HilbertSpaceSegmentProportionRaw
      Geo
      A E
      E B
      C F
      F D := by

  ----------------------------------------------------------------------
  -- Construct Euclid's auxiliary point O on AD in the middle plane.
  ----------------------------------------------------------------------

  cases
      euclid_proposition_11_17_construct_O
        (Geo := Geo)
        pi0 pi1 pi2
        A E B D
        hParallel01
        hParallel12
        hParallel02
        hApi0
        hEpi1
        hBpi2
        hDpi2
        hAEB
        hBD with
  | intro O hO =>

      have hAOD :
          Geo.Between A O D :=
        hO.1

      have hOpi1 :
          S.OnPlane O pi1 :=
        hO.2

      ------------------------------------------------------------------
      -- Apply the complete core with O.
      ------------------------------------------------------------------

      exact
        euclid_proposition_11_17_with_O
          (Geo := Geo)
          hVI2
          pi0 pi1 pi2
          A E B C F D O
          hParallel01
          hParallel12
          hParallel02
          hApi0 hCpi0
          hEpi1 hFpi1 hOpi1
          hBpi2 hDpi2
          hAEB hCFD hAOD
          hBD hAC

end Geometry

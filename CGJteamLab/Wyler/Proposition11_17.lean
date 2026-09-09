import CGJteamLab.Wyler.Proposition11_16
import CGJteamLab.Wyler.HilbertWylerProportion
import CGJteamLab.Hilbert3DProportion

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.17 - Wyler path

Production reconstruction of Euclid XI.17 in the Wyler flat/carrier path.

Architecture:

1. construct the two section planes and identify their section lines by
   exact carrier meet equalities;
2. obtain the two parallel section-line pairs from Wyler XI.16;
3. isolate the planar intercept-ratio step in one reusable bridge;
4. construct Euclid's auxiliary point O by Pasch;
5. compose the two proportions by spatial V.11.

The spatial geometry is carried by the Wyler flat/carrier calculus.
The primary Wyler conclusion is the affine relation
`HilbertWylerSameDivision`: it is obtained from two parallel-section
steps, reversal, and transitivity, with no metric ratio or VI.2.

For compatibility with the canonical Book XI API, this module also keeps
the previously established synthetic `HilbertSpaceSegmentProportionRaw`
result.  That compatibility theorem remains logically separate from the
affine Wyler theorem.

This module uses names ending in `_wyler` where needed to coexist with
the canonical synthetic Book XI development.
-/

theorem euclid_XI17_wyler_first_sections
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi0 pi1 pi2 : S.Plane)
    (A E B D O : Geo.Point)
    (hParallel12 :
      HilbertSpacePlanesParallel Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallel Geo pi0 pi2)
    (hApi0 : S.OnPlane A pi0)
    (hEpi1 : S.OnPlane E pi1)
    (hOpi1 : S.OnPlane O pi1)
    (hBpi2 : S.OnPlane B pi2)
    (hDpi2 : S.OnPlane D pi2)
    (hAEB : Geo.Between A E B)
    (hAOD : Geo.Between A O D)
    (hBD : Ne B D) :
    exists sigma1 : S.Plane,
    exists lEO lBD : Geo.Line,
      S.OnPlane A sigma1 /\
      S.OnPlane B sigma1 /\
      S.OnPlane D sigma1 /\
      S.OnPlane E sigma1 /\
      S.OnPlane O sigma1 /\
      H.OnLine E lEO /\
      H.OnLine O lEO /\
      H.OnLine B lBD /\
      H.OnLine D lBD /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi1)
          (HilbertPlaneCarrier3D Geo sigma1) =
        HilbertLineCarrier3D Geo lEO /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi2)
          (HilbertPlaneCarrier3D Geo sigma1) =
        HilbertLineCarrier3D Geo lBD /\
      HilbertSpaceLinesParallel Geo lEO lBD := by

  ----------------------------------------------------------------------
  -- Order data used only to recover the two transversal collinearities.
  ----------------------------------------------------------------------

  have hAEBData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A E B hAEB

  have hAODData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O D hAOD

  have hAB : Ne A B :=
    hAEBData.2.2.1

  have hAD : Ne A D :=
    hAODData.2.2.1

  have hAEBcol :
      PrimCollinear Geo A E B :=
    hAEBData.2.2.2.1

  have hAODcol :
      PrimCollinear Geo A O D :=
    hAODData.2.2.2.1

  have hABEcol :
      PrimCollinear Geo A B E :=
    PrimCollinearRotate
      Geo A E B hAEBcol

  have hADOcol :
      PrimCollinear Geo A D O :=
    PrimCollinearRotate
      Geo A O D hAODcol

  ----------------------------------------------------------------------
  -- Since pi0 and pi2 are parallel and A lies in pi0, A is not in pi2.
  ----------------------------------------------------------------------

  have hAnotPi2 :
      Not (S.OnPlane A pi2) := by
    intro hApi2
    apply hParallel02
    exact
      Exists.intro A
        (And.intro hApi0 hApi2)

  ----------------------------------------------------------------------
  -- A,B,D are noncollinear, so they determine sigma1.
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

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B D hABD
    with
    ⟨sigma1, hAsigma1, hBsigma1, hDsigma1⟩

  ----------------------------------------------------------------------
  -- E lies on AB and O lies on AD, hence both lie in sigma1.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Wyler XI.16:
  --
  --   pi1 meet sigma1 = lEO,
  --   pi2 meet sigma1 = lBD,
  --   lEO || lBD.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_16_wyler
        (Geo := Geo)
        pi1 pi2 sigma1
        E B
        hParallel12
        hEpi1 hEsigma1
        hBpi2 hBsigma1
    with
    ⟨lEO, lBD,
     hElEO, hBlBD,
     hMeetEO, hMeetBD,
     hParallelEOBD⟩

  ----------------------------------------------------------------------
  -- Recover O and D on the two section lines directly from the
  -- carrier equalities.  This is the Wyler-style use of XI.16.
  ----------------------------------------------------------------------

  have hOlEO :
      H.OnLine O lEO := by
    change HilbertLineCarrier3D Geo lEO O
    rw [← hMeetEO]
    exact And.intro hOpi1 hOsigma1

  have hDlBD :
      H.OnLine D lBD := by
    change HilbertLineCarrier3D Geo lBD D
    rw [← hMeetBD]
    exact And.intro hDpi2 hDsigma1

  exact
    ⟨sigma1, lEO, lBD,
     hAsigma1,
     hBsigma1,
     hDsigma1,
     hEsigma1,
     hOsigma1,
     hElEO,
     hOlEO,
     hBlBD,
     hDlBD,
     hMeetEO,
     hMeetBD,
     hParallelEOBD⟩


theorem euclid_XI17_wyler_sections
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi0 pi1 pi2 : S.Plane)
    (A E B C F D O : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallel Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallel Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallel Geo pi0 pi2)
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
    exists sigma1 sigma2 : S.Plane,
    exists lEO lBD lAC lOF : Geo.Line,
      S.OnPlane A sigma1 /\
      S.OnPlane B sigma1 /\
      S.OnPlane D sigma1 /\
      S.OnPlane E sigma1 /\
      S.OnPlane O sigma1 /\
      S.OnPlane A sigma2 /\
      S.OnPlane C sigma2 /\
      S.OnPlane D sigma2 /\
      S.OnPlane F sigma2 /\
      S.OnPlane O sigma2 /\
      H.OnLine E lEO /\
      H.OnLine O lEO /\
      H.OnLine B lBD /\
      H.OnLine D lBD /\
      H.OnLine A lAC /\
      H.OnLine C lAC /\
      H.OnLine O lOF /\
      H.OnLine F lOF /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi1)
          (HilbertPlaneCarrier3D Geo sigma1) =
        HilbertLineCarrier3D Geo lEO /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi2)
          (HilbertPlaneCarrier3D Geo sigma1) =
        HilbertLineCarrier3D Geo lBD /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi0)
          (HilbertPlaneCarrier3D Geo sigma2) =
        HilbertLineCarrier3D Geo lAC /\
      Set.inter
          (HilbertPlaneCarrier3D Geo pi1)
          (HilbertPlaneCarrier3D Geo sigma2) =
        HilbertLineCarrier3D Geo lOF /\
      HilbertSpaceLinesParallel Geo lEO lBD /\
      HilbertSpaceLinesParallel Geo lAC lOF := by

  ----------------------------------------------------------------------
  -- First section plane and first parallel pair.
  ----------------------------------------------------------------------

  rcases
      euclid_XI17_wyler_first_sections
        (Geo := Geo)
        pi0 pi1 pi2
        A E B D O
        hParallel12
        hParallel02
        hApi0
        hEpi1
        hOpi1
        hBpi2
        hDpi2
        hAEB
        hAOD
        hBD
    with
    ⟨sigma1, lEO, lBD,
     hAsigma1,
     hBsigma1,
     hDsigma1,
     hEsigma1,
     hOsigma1,
     hElEO,
     hOlEO,
     hBlBD,
     hDlBD,
     hMeetEO,
     hMeetBD,
     hParallelEOBD⟩

  ----------------------------------------------------------------------
  -- Order data for the second transversal C-F-D and the diagonal A-O-D.
  ----------------------------------------------------------------------

  have hCFDData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C F D hCFD

  have hAODData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O D hAOD

  have hCD : Ne C D :=
    hCFDData.2.2.1

  have hAD : Ne A D :=
    hAODData.2.2.1

  have hCFDcol :
      PrimCollinear Geo C F D :=
    hCFDData.2.2.2.1

  have hAODcol :
      PrimCollinear Geo A O D :=
    hAODData.2.2.2.1

  have hCDFcol :
      PrimCollinear Geo C D F :=
    PrimCollinearRotate
      Geo C F D hCFDcol

  have hADOcol :
      PrimCollinear Geo A D O :=
    PrimCollinearRotate
      Geo A O D hAODcol

  ----------------------------------------------------------------------
  -- Since pi0 and pi2 are parallel and D lies in pi2, D is not in pi0.
  ----------------------------------------------------------------------

  have hDnotPi0 :
      Not (S.OnPlane D pi0) := by
    intro hDpi0
    apply hParallel02
    exact
      Exists.intro D
        (And.intro hDpi0 hDpi2)

  ----------------------------------------------------------------------
  -- A,C,D are noncollinear, so they determine sigma2.
  ----------------------------------------------------------------------

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

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A C D hACD
    with
    ⟨sigma2, hAsigma2, hCsigma2, hDsigma2⟩

  ----------------------------------------------------------------------
  -- F lies on CD and O lies on AD, hence both lie in sigma2.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Second Wyler XI.16:
  --
  --   pi0 meet sigma2 = lAC,
  --   pi1 meet sigma2 = lOF,
  --   lAC || lOF.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_16_wyler
        (Geo := Geo)
        pi0 pi1 sigma2
        A O
        hParallel01
        hApi0 hAsigma2
        hOpi1 hOsigma2
    with
    ⟨lAC, lOF,
     hAlAC, hOlOF,
     hMeetAC, hMeetOF,
     hParallelACOF⟩

  ----------------------------------------------------------------------
  -- Recover C and F directly from the exact carrier equalities.
  ----------------------------------------------------------------------

  have hClAC :
      H.OnLine C lAC := by
    change HilbertLineCarrier3D Geo lAC C
    rw [← hMeetAC]
    exact And.intro hCpi0 hCsigma2

  have hFlOF :
      H.OnLine F lOF := by
    change HilbertLineCarrier3D Geo lOF F
    rw [← hMeetOF]
    exact And.intro hFpi1 hFsigma2

  exact
    ⟨sigma1, sigma2,
     lEO, lBD, lAC, lOF,
     hAsigma1,
     hBsigma1,
     hDsigma1,
     hEsigma1,
     hOsigma1,
     hAsigma2,
     hCsigma2,
     hDsigma2,
     hFsigma2,
     hOsigma2,
     hElEO,
     hOlEO,
     hBlBD,
     hDlBD,
     hAlAC,
     hClAC,
     hOlOF,
     hFlOF,
     hMeetEO,
     hMeetBD,
     hMeetAC,
     hMeetOF,
     hParallelEOBD,
     hParallelACOF⟩


/--
Wyler section-ratio bridge.

Assume

  X-E-Y,
  X-F-Z,

and assume the section line EF is spatially parallel to the section line
YZ.  Then the two transversals through X have the same division ratio.

We return both orientations needed by XI.17:

  XE : EY = XF : FZ,

and, after reciprocal orientation plus endpoint reversal,

  YE : EX = ZF : FX.
-/
theorem hilbert_wyler_parallel_sections_proportion_raw
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
    (X E Y F Z : Geo.Point)
    (hXEY : Geo.Between X E Y)
    (hXFZ : Geo.Between X F Z)
    (lEF lYZ : Geo.Line)
    (hElEF : H.OnLine E lEF)
    (hFlEF : H.OnLine F lEF)
    (hYlYZ : H.OnLine Y lYZ)
    (hZlYZ : H.OnLine Z lYZ)
    (hEF : Ne E F)
    (hYZ : Ne Y Z)
    (hParallel :
      HilbertSpaceLinesParallel Geo lEF lYZ) :
    HilbertSpaceSegmentProportionRaw
        Geo
        X E
        E Y
        X F
        F Z /\
    HilbertSpaceSegmentProportionRaw
        Geo
        Y E
        E X
        Z F
        F X := by

  ----------------------------------------------------------------------
  -- Spatial parallelism supplies the common section plane tau and
  -- disjointness of the two section carriers.
  ----------------------------------------------------------------------

  rcases hParallel with
    ⟨tau, hlEFTau, hlYZTau, hDisjoint⟩

  have hEtau : S.OnPlane E tau :=
    hlEFTau E hElEF

  have hFtau : S.OnPlane F tau :=
    hlEFTau F hFlEF

  have hYtau : S.OnPlane Y tau :=
    hlYZTau Y hYlYZ

  have hZtau : S.OnPlane Z tau :=
    hlYZTau Z hZlYZ

  ----------------------------------------------------------------------
  -- X belongs to tau because X,E,Y are collinear and E,Y lie in tau.
  ----------------------------------------------------------------------

  have hXEYData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X E Y hXEY

  have hEY : Ne E Y :=
    hXEYData.2.1

  have hXEYcol :
      PrimCollinear Geo X E Y :=
    hXEYData.2.2.2.1

  have hEYXcol :
      PrimCollinear Geo E Y X :=
    PrimCollinearCycle
      Geo X E Y hXEYcol

  have hXtau : S.OnPlane X tau :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      tau
      E Y X
      hEY
      hEtau hYtau
      hEYXcol

  ----------------------------------------------------------------------
  -- Work once in PlaneGeo(tau).
  ----------------------------------------------------------------------

  let Xp : PlanePoint Geo tau :=
    ⟨X, hXtau⟩

  let Ep : PlanePoint Geo tau :=
    ⟨E, hEtau⟩

  let Yp : PlanePoint Geo tau :=
    ⟨Y, hYtau⟩

  let Fp : PlanePoint Geo tau :=
    ⟨F, hFtau⟩

  let Zp : PlanePoint Geo tau :=
    ⟨Z, hZtau⟩

  have hXEYp :
      (PlaneGeo Geo tau).Between Xp Ep Yp := by
    exact hXEY

  have hXFZp :
      (PlaneGeo Geo tau).Between Xp Fp Zp := by
    exact hXFZ

  have hEFp : Ne Ep Fp := by
    intro h
    apply hEF
    exact congrArg Subtype.val h

  have hYZp : Ne Yp Zp := by
    intro h
    apply hYZ
    exact congrArg Subtype.val h

  have hParallelPlane :
      (PlaneGeo Geo tau).Parallel
        Ep Fp Yp Zp :=
    planeGeo_parallel_of_ambient_disjoint_carriers
      (Geo := Geo)
      tau
      lEF lYZ
      Ep Fp Yp Zp
      hEFp hYZp
      hlEFTau hlYZTau
      hElEF hFlEF
      hYlYZ hZlYZ
      hDisjoint

  have hVI2Data :=
    (hVI2 tau)
      Xp Ep Yp Fp Zp
      hXEYp hXFZp
      hParallelPlane

  ----------------------------------------------------------------------
  -- First orientation:
  --
  --   XE : EY = XF : FZ.
  ----------------------------------------------------------------------

  have hForwardPlane :
      HilbertSegmentProportionRaw
        (PlaneGeo Geo tau)
        Xp Ep
        Ep Yp
        Xp Fp
        Fp Zp :=
    hVI2Data.1

  have hForwardSpace :
      HilbertSpaceSegmentProportionRaw
        Geo
        X E
        E Y
        X F
        F Z := by
    have h :=
      hilbertSegmentProportionRaw_to_space
        (Geo := Geo)
        tau
        Xp Ep
        Ep Yp
        Xp Fp
        Fp Zp
        hForwardPlane
    simpa [Xp, Ep, Yp, Fp, Zp] using h

  ----------------------------------------------------------------------
  -- Reciprocal VI.2 orientation:
  --
  --   EY : XE = FZ : XF.
  --
  -- Reverse all four concrete segment orientations:
  --
  --   YE : EX = ZF : FX.
  ----------------------------------------------------------------------

  have hReciprocalPlane :
      HilbertSegmentProportionRaw
        (PlaneGeo Geo tau)
        Ep Yp
        Xp Ep
        Fp Zp
        Xp Fp :=
    hVI2Data.2

  have hReversePlane :
      HilbertSegmentProportionRaw
        (PlaneGeo Geo tau)
        Yp Ep
        Ep Xp
        Zp Fp
        Fp Xp :=
    hilbertSegmentProportionRaw_reverse_all
      (Geo := PlaneGeo Geo tau)
      Ep Yp
      Xp Ep
      Fp Zp
      Xp Fp
      hReciprocalPlane

  have hReverseSpace :
      HilbertSpaceSegmentProportionRaw
        Geo
        Y E
        E X
        Z F
        F X := by
    have h :=
      hilbertSegmentProportionRaw_to_space
        (Geo := Geo)
        tau
        Yp Ep
        Ep Xp
        Zp Fp
        Fp Xp
        hReversePlane
    simpa [Xp, Ep, Yp, Fp, Zp] using h

  exact
    And.intro hForwardSpace hReverseSpace


/--
Euclid XI.17 with the auxiliary point O already given.

All spatial geometry is supplied by the Wyler flat/carrier construction
from the preceding section theorem.  The two ratio comparisons are instances of the generic
parallel-section bridge above.

The result is

  AE : EB = CF : FD.
-/
theorem euclid_proposition_11_17_wyler_with_O
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
      HilbertSpacePlanesParallel Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallel Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallel Geo pi0 pi2)
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
  -- Complete Wyler flat/carrier skeleton.
  ----------------------------------------------------------------------

  rcases
      euclid_XI17_wyler_sections
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
        hBD hAC
    with
    ⟨sigma1, sigma2,
     lEO, lBD, lAC, lOF,
     hAsigma1,
     hBsigma1,
     hDsigma1,
     hEsigma1,
     hOsigma1,
     hAsigma2,
     hCsigma2,
     hDsigma2,
     hFsigma2,
     hOsigma2,
     hElEO,
     hOlEO,
     hBlBD,
     hDlBD,
     hAlAC,
     hClAC,
     hOlOF,
     hFlOF,
     hMeetEO,
     hMeetBD,
     hMeetAC,
     hMeetOF,
     hParallelEOBD,
     hParallelACOF⟩

  ----------------------------------------------------------------------
  -- First intercept comparison in sigma1:
  --
  --   AE : EB = AO : OD.
  ----------------------------------------------------------------------

  have hFirst :
      HilbertSpaceSegmentProportionRaw
        Geo
        A E
        E B
        A O
        O D :=
    (hilbert_wyler_parallel_sections_proportion_raw
      (Geo := Geo)
      hVI2
      A E B O D
      hAEB hAOD
      lEO lBD
      hElEO hOlEO
      hBlBD hDlBD
      hEO hBD
      hParallelEOBD).1

  ----------------------------------------------------------------------
  -- Reverse both transversals for the second section plane:
  --
  --   D-O-A,
  --   D-F-C.
  ----------------------------------------------------------------------

  have hAODData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O D hAOD

  have hCFDData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C F D hCFD

  have hDOA : Geo.Between D O A :=
    hAODData.2.2.2.2

  have hDFC : Geo.Between D F C :=
    hCFDData.2.2.2.2

  ----------------------------------------------------------------------
  -- Reverse the spatial parallelism orientation:
  --
  --   lAC || lOF  ->  lOF || lAC.
  ----------------------------------------------------------------------

  have hParallelOFAC :
      HilbertSpaceLinesParallel Geo lOF lAC := by
    rcases hParallelACOF with
      ⟨tau, hlACTau, hlOFTau, hDisjointACOF⟩
    refine ⟨tau, hlOFTau, hlACTau, ?_⟩
    intro hMeet
    rcases hMeet with ⟨X, hXOF, hXAC⟩
    exact
      hDisjointACOF
        ⟨X, hXAC, hXOF⟩

  ----------------------------------------------------------------------
  -- Second intercept comparison in sigma2.
  --
  -- The reverse-orientation output of the bridge gives directly:
  --
  --   AO : OD = CF : FD.
  ----------------------------------------------------------------------

  have hSecond :
      HilbertSpaceSegmentProportionRaw
        Geo
        A O
        O D
        C F
        F D :=
    (hilbert_wyler_parallel_sections_proportion_raw
      (Geo := Geo)
      hVI2
      D O A F C
      hDOA hDFC
      lOF lAC
      hOlOF hFlOF
      hAlAC hClAC
      hOF hAC
      hParallelOFAC).2

  ----------------------------------------------------------------------
  -- V.11: compose through the common ratio AO : OD.
  ----------------------------------------------------------------------

  exact
    hilbertSpaceSegmentProportionRaw_trans
      (Geo := Geo)
      A E
      E B
      A O
      O D
      C F
      F D
      hFirst
      hSecond


theorem euclid_proposition_11_17_construct_O_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi0 pi1 pi2 : S.Plane)
    (A E B D : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallel Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallel Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallel Geo pi0 pi2)
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
  -- A is outside pi2, hence A,B,D are noncollinear.
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
  -- sigma = plane(A,B,D).
  ----------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B D hABD
    with
    ⟨sigma, hAsigma, hBsigma, hDsigma⟩

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

  ----------------------------------------------------------------------
  -- Wyler XI.16 for pi1 || pi2 cut by sigma:
  --
  --   pi1 meet sigma = lE,
  --   pi2 meet sigma = lBD,
  --   lE || lBD.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_16_wyler
        (Geo := Geo)
        pi1 pi2 sigma
        E B
        hParallel12
        hEpi1 hEsigma
        hBpi2 hBsigma
    with
    ⟨lE, lBD,
     hElE, hBlBD,
     hMeetE, hMeetBD,
     hParallelLines⟩

  ----------------------------------------------------------------------
  -- Recover the carrier containments from the exact meet identities.
  ----------------------------------------------------------------------

  have hlEsigma :
      HilbertLineInPlane Geo lE sigma := by
    intro X hXlE
    have hXMeet :
        Set.inter
          (HilbertPlaneCarrier3D Geo pi1)
          (HilbertPlaneCarrier3D Geo sigma) X := by
      rw [hMeetE]
      exact hXlE
    exact hXMeet.2

  have hlEpi1 :
      HilbertLineInPlane Geo lE pi1 := by
    intro X hXlE
    have hXMeet :
        Set.inter
          (HilbertPlaneCarrier3D Geo pi1)
          (HilbertPlaneCarrier3D Geo sigma) X := by
      rw [hMeetE]
      exact hXlE
    exact hXMeet.1

  have hDlBD :
      H.OnLine D lBD := by
    change HilbertLineCarrier3D Geo lBD D
    rw [← hMeetBD]
    exact And.intro hDpi2 hDsigma

  have hDisjoint :
      HilbertLinesDisjoint Geo lE lBD := by
    rcases hParallelLines with
      ⟨tau, _hlEtau, _hlBDtau, hDisjoint⟩
    exact hDisjoint

  ----------------------------------------------------------------------
  -- A,B,D are all outside the middle plane pi1, hence off lE.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- lE meets the open side AB at E.
  ----------------------------------------------------------------------

  have hMeetAB :
      HilbertSegmentMeetsLine Geo A B lE :=
    Exists.intro E
      (And.intro hAEB hElE)

  ----------------------------------------------------------------------
  -- Pasch in sigma.
  ----------------------------------------------------------------------

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

    rcases hPasch with hAD | hBDMeet

    · exact hAD

    · rcases hBDMeet with
        ⟨X, hBXD, hXlE⟩

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

  ----------------------------------------------------------------------
  -- The Pasch point on AD is the required O.
  ----------------------------------------------------------------------

  rcases hMeetAD with
    ⟨O, hAOD, hOlE⟩

  have hOpi1 :
      S.OnPlane O pi1 :=
    hlEpi1 O hOlE

  exact
    Exists.intro O
      (And.intro hAOD hOpi1)


theorem euclid_proposition_11_17_wyler
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
      HilbertSpacePlanesParallel Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallel Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallel Geo pi0 pi2)
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
  -- Construct O on AD in the middle plane.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_17_construct_O_wyler
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
        hBD
    with
    ⟨O, hAOD, hOpi1⟩

  ----------------------------------------------------------------------
  -- Basic order data.
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
  -- Outer-plane separation.
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
  -- E != O.
  --
  -- Otherwise AB and AD share the two distinct points A,E, so D lies
  -- on AB.  Then A lies in pi2 because B,D lie in pi2, contradicting
  -- pi0 || pi2.
  ----------------------------------------------------------------------

  have hEO :
      Ne E O := by
    intro hEOeq
    subst O

    rcases hAEBcol with
      ⟨q, hAq, hEq, hBq⟩

    have hDq :
        H.OnLine D q :=
      hilbert_collinear_on_line
        Geo
        A E D
        q
        hAE
        hAq hEq
        hAODcol

    have hBDA :
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
        hBDA

  ----------------------------------------------------------------------
  -- O != F.
  --
  -- Otherwise AD and CD share the two distinct points F,D, so A lies
  -- on CD.  Then D lies in pi0 because A,C lie in pi0, contradicting
  -- pi0 || pi2.
  ----------------------------------------------------------------------

  have hOF :
      Ne O F := by
    intro hOFeq
    subst O

    rcases hCFDcol with
      ⟨q, hCq, hFq, hDq⟩

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

  ----------------------------------------------------------------------
  -- Final Wyler XI.17 core.
  ----------------------------------------------------------------------

  exact
    euclid_proposition_11_17_wyler_with_O
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


/--
Euclid XI.17 in the genuinely affine Wyler formulation.

The conclusion says that E and F occupy the same affine division
position on the transversals AB and CD.  The proof uses only the Wyler
carrier/section geometry, the Pasch construction of O, two elementary
parallel-section division steps, simultaneous reversal, and transitivity.

No `HilbertVI2Raw`, `HilbertSpaceCongruence`, metric segment ratio,
coordinates, or real-number parameter is used.
-/
theorem euclid_proposition_11_17_wyler_affine
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi0 pi1 pi2 : S.Plane)
    (A E B C F D : Geo.Point)
    (hParallel01 :
      HilbertSpacePlanesParallel Geo pi0 pi1)
    (hParallel12 :
      HilbertSpacePlanesParallel Geo pi1 pi2)
    (hParallel02 :
      HilbertSpacePlanesParallel Geo pi0 pi2)
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
    HilbertWylerSameDivision
      (Geo := Geo)
      A E B
      C F D := by

  rcases
      euclid_proposition_11_17_construct_O_wyler
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
        hBD
    with
    ⟨O, hAOD, hOpi1⟩

  rcases
      euclid_XI17_wyler_sections
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
        hBD hAC
    with
    ⟨sigma1, sigma2,
     lEO, lBD, lAC, lOF,
     hAsigma1,
     hBsigma1,
     hDsigma1,
     hEsigma1,
     hOsigma1,
     hAsigma2,
     hCsigma2,
     hDsigma2,
     hFsigma2,
     hOsigma2,
     hElEO,
     hOlEO,
     hBlBD,
     hDlBD,
     hAlAC,
     hClAC,
     hOlOF,
     hFlOF,
     hMeetEO,
     hMeetBD,
     hMeetAC,
     hMeetOF,
     hParallelEOBD,
     hParallelACOF⟩

  have hFirst :
      HilbertWylerSameDivision
        (Geo := Geo)
        A E B
        A O D :=
    hilbertWylerSameDivision_of_parallel_sections
      (Geo := Geo)
      A E B O D
      hAEB hAOD
      lEO lBD
      hElEO hOlEO
      hBlBD hDlBD
      hParallelEOBD

  have hAODData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O D hAOD

  have hCFDData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C F D hCFD

  have hDOA :
      Geo.Between D O A :=
    hAODData.2.2.2.2

  have hDFC :
      Geo.Between D F C :=
    hCFDData.2.2.2.2

  have hParallelOFAC :
      HilbertSpaceLinesParallel Geo lOF lAC := by
    rcases hParallelACOF with
      ⟨tau, hlACTau, hlOFTau, hDisjointACOF⟩

    refine
      ⟨tau, hlOFTau, hlACTau, ?_⟩

    intro hMeet

    rcases hMeet with
      ⟨X, hXOF, hXAC⟩

    exact
      hDisjointACOF
        ⟨X, hXAC, hXOF⟩

  have hSecondReversed :
      HilbertWylerSameDivision
        (Geo := Geo)
        D O A
        D F C :=
    hilbertWylerSameDivision_of_parallel_sections
      (Geo := Geo)
      D O A F C
      hDOA hDFC
      lOF lAC
      hOlOF hFlOF
      hAlAC hClAC
      hParallelOFAC

  have hSecond :
      HilbertWylerSameDivision
        (Geo := Geo)
        A O D
        C F D :=
    hilbertWylerSameDivision_reverse
      (Geo := Geo)
      D O A
      D F C
      hSecondReversed

  exact
    hilbertWylerSameDivision_trans
      (Geo := Geo)
      A E B
      A O D
      C F D
      hFirst hSecond

end Geometry

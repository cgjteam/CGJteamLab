import CGJteamLab.Hilbert3DProportion
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.Proposition32
import CGJteamLab.HilbertInterfaceXI
import CGJteamLab.Proposition12
import CGJteamLab.Proposition16
import CGJteamLab.Proposition19
import CGJteamLab.Proposition2_13
import CGJteamLab.Proposition17
import CGJteamLab.HilbertInterfaceVI
import CGJteamLab.Proposition11_25
import CGJteamLab.Proposition11_26
import CGJteamLab.Proposition11_12
import CGJteamLab.Proposition11_15
import CGJteamLab.Proposition11_16
import CGJteamLab.Proposition11_24
import CGJteamLab.HilbertTrihedralAngle
import CGJteamLab.Hilbert3DParallel
import CGJteamLab.Proposition11_10
import CGJteamLab.Proposition34
import CGJteamLab.Proposition5_22

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.27 -- IV/V.22-clean production candidate

This file is generated from the last clean Proposition11_27
by folding only untracked non-Proposition/non-Interface support
modules from its actual dependency closure.
-/




















































































































































/- BEGIN folded support: HilbertParallelepipedShell.lean -/
/-!
# Parallelepiped shell construction

Reusable Book XI support for the Forder VI.36.8 construction.

A proper trihedral corner is completed to the six-plane, eight-vertex
incidence shell represented by `HilbertParallelepipedConfiguration`.

This file consolidates the already tested XI.27 development block:
translated edge directions, one opposite plane, the three opposite
planes, the four remaining vertices, and final shell assembly.

It deliberately contains no `#print axioms` commands.
-/

/--
At one vertex of a proper trihedral corner, the two translated edge
directions used in the Forder VI.36.8 shell construction exist and are
distinct.
-/
theorem hilbert_trihedral_two_distinct_translates_at_A
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (O A B C : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    exists lOB lOC mB mC : Geo.Line,
      H.OnLine O lOB /\
      H.OnLine B lOB /\
      H.OnLine O lOC /\
      H.OnLine C lOC /\
      H.OnLine A mB /\
      H.OnLine A mC /\
      HilbertSpaceLinesParallel Geo lOB mB /\
      HilbertSpaceLinesParallel Geo lOC mC /\
      Ne mB mC := by

  ----------------------------------------------------------------------
  -- Nondegenerate edge lines OB and OC.
  ----------------------------------------------------------------------

  have hOB : Ne O B := by
    exact
      (hilbert_noncollinear_ne_first
        Geo B O C hTri.2.1).symm

  have hOC : Ne O C := by
    exact
      (hilbert_noncollinear_ne_first
        Geo C O A hTri.2.2.1).symm

  rcases
      HilbertPlaneIncidence.line_through
        O B hOB
    with
    ⟨lOB, hOlOB, hBlOB⟩

  rcases
      HilbertPlaneIncidence.line_through
        O C hOC
    with
    ⟨lOC, hOlOC, hClOC⟩

  ----------------------------------------------------------------------
  -- The three face planes AOB, AOC, OBC.
  ----------------------------------------------------------------------

  rcases
      HSI.plane_through
        A O B hTri.1
    with
    ⟨alpha, hAalpha, hOalpha, hBalpha⟩

  rcases
      HSI.plane_through
        C O A hTri.2.2.1
    with
    ⟨beta, hCbeta, hObeta, hAbeta⟩

  have hOBC :
      Not (PrimCollinear Geo O B C) := by
    intro h
    exact
      hTri.2.1
        (PrimCollinearSwap
          Geo O B C h)

  rcases
      HSI.plane_through
        O B C hOBC
    with
    ⟨tau, hOtau, hBtau, hCtau⟩

  have hlOBalpha :
      HilbertLineInPlane Geo lOB alpha :=
    HSI.line_in_plane
      O B hOB
      lOB
      hOlOB hBlOB
      alpha
      hOalpha hBalpha

  have hlOCbeta :
      HilbertLineInPlane Geo lOC beta :=
    HSI.line_in_plane
      O C hOC
      lOC
      hOlOC hClOC
      beta
      hObeta hCbeta

  have hA_not_lOB :
      Not (H.OnLine A lOB) := by
    intro hAlOB
    exact
      hTri.1
        ⟨lOB,
         hAlOB,
         hOlOB,
         hBlOB⟩

  have hA_not_lOC :
      Not (H.OnLine A lOC) := by
    intro hAlOC
    exact
      hTri.2.2.1
        ⟨lOC,
         hClOC,
         hOlOC,
         hAlOC⟩

  ----------------------------------------------------------------------
  -- XI.12 / I.31 inside the two adjacent face planes.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI12_parallel_through_point_in_plane
        (Geo := Geo)
        alpha lOB A
        hlOBalpha
        hAalpha
        hA_not_lOB
    with
    ⟨mB, hAmB, hParOB⟩

  rcases
      hilbert_XI12_parallel_through_point_in_plane
        (Geo := Geo)
        beta lOC A
        hlOCbeta
        hAbeta
        hA_not_lOC
    with
    ⟨mC, hAmC, hParOC⟩

  ----------------------------------------------------------------------
  -- The two translated directions cannot coincide.
  ----------------------------------------------------------------------

  have hmBC : Ne mB mC := by
    intro hEq
    subst mC

    rcases hParOB with
      ⟨sigma1,
       hlOBsigma1,
       hmBsigma1,
       hDisjOB⟩

    rcases hParOC with
      ⟨sigma2,
       hlOCsigma2,
       hmBsigma2,
       hDisjOC⟩

    have hO_not_mB :
        Not (H.OnLine O mB) := by
      intro hOmB
      exact
        hDisjOB
          ⟨O, hOlOB, hOmB⟩

    rcases
        hilbert_other_point_on_line
          (Geo := Geo)
          mB A
      with
      ⟨Q, hQA, hQmB⟩

    have hAQ : Ne A Q :=
      hQA.symm

    have hAQO :
        Not (PrimCollinear Geo A Q O) :=
      hilbert_not_collinear_of_off_line
        Geo
        A Q O
        mB
        hAQ
        hAmB
        hQmB
        hO_not_mB

    have hAsigma1 :
        S.OnPlane A sigma1 :=
      hmBsigma1 A hAmB

    have hQsigma1 :
        S.OnPlane Q sigma1 :=
      hmBsigma1 Q hQmB

    have hOsigma1 :
        S.OnPlane O sigma1 :=
      hlOBsigma1 O hOlOB

    have hAsigma2 :
        S.OnPlane A sigma2 :=
      hmBsigma2 A hAmB

    have hQsigma2 :
        S.OnPlane Q sigma2 :=
      hmBsigma2 Q hQmB

    have hOsigma2 :
        S.OnPlane O sigma2 :=
      hlOCsigma2 O hOlOC

    have hSigma12 :
        sigma1 = sigma2 :=
      HSI.plane_unique
        A Q O
        hAQO
        sigma1 sigma2
        hAsigma1
        hQsigma1
        hOsigma1
        hAsigma2
        hQsigma2
        hOsigma2

    have hBsigma1 :
        S.OnPlane B sigma1 :=
      hlOBsigma1 B hBlOB

    have hCsigma2 :
        S.OnPlane C sigma2 :=
      hlOCsigma2 C hClOC

    have hCsigma1 :
        S.OnPlane C sigma1 := by
      rw [hSigma12]
      exact hCsigma2

    have hSigmaTau :
        sigma1 = tau :=
      HSI.plane_unique
        O B C
        hOBC
        sigma1 tau
        hOsigma1
        hBsigma1
        hCsigma1
        hOtau
        hBtau
        hCtau

    have hAtau :
        S.OnPlane A tau := by
      rw [← hSigmaTau]
      exact hAsigma1

    exact
      hTri.2.2.2
        ⟨tau,
         hOtau,
         hAtau,
         hBtau,
         hCtau⟩

  exact
    ⟨lOB, lOC, mB, mC,
     hOlOB,
     hBlOB,
     hOlOC,
     hClOC,
     hAmB,
     hAmC,
     hParOB,
     hParOC,
     hmBC⟩


/--
For a proper trihedral corner `O; A,B,C`, there is a plane through `A`
parallel, in the incidence sense, to the opposite face plane through
`O,B,C`.
-/
theorem hilbert_trihedral_opposite_plane_through_A
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (O A B C : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    exists tau gamma : S.Plane,
      S.OnPlane O tau /\
      S.OnPlane B tau /\
      S.OnPlane C tau /\
      S.OnPlane A gamma /\
      HilbertSpacePlanesParallelIncidence
        Geo tau gamma := by

  ----------------------------------------------------------------------
  -- Two translated edge directions through A.
  ----------------------------------------------------------------------

  rcases
      hilbert_trihedral_two_distinct_translates_at_A
        (Geo := Geo)
        O A B C
        hTri
    with
    ⟨lOB, lOC, mB, mC,
     hOlOB,
     hBlOB,
     hOlOC,
     hClOC,
     hAmB,
     hAmC,
     hParOB,
     hParOC,
     hmBC⟩

  ----------------------------------------------------------------------
  -- The source face plane tau = plane(O,B,C).
  ----------------------------------------------------------------------

  have hOBC :
      Not (PrimCollinear Geo O B C) := by
    intro hCol
    exact
      hTri.2.1
        (PrimCollinearSwap
          Geo O B C hCol)

  rcases
      HSI.plane_through
        O B C hOBC
    with
    ⟨tau, hOtau, hBtau, hCtau⟩

  have hOB : Ne O B := by
    exact
      (hilbert_noncollinear_ne_first
        Geo B O C hTri.2.1).symm

  have hOC : Ne O C := by
    exact
      (hilbert_noncollinear_ne_first
        Geo C O A hTri.2.2.1).symm

  have hlOBtau :
      HilbertLineInPlane Geo lOB tau :=
    HSI.line_in_plane
      O B hOB
      lOB
      hOlOB hBlOB
      tau
      hOtau hBtau

  have hlOCtau :
      HilbertLineInPlane Geo lOC tau :=
    HSI.line_in_plane
      O C hOC
      lOC
      hOlOC hClOC
      tau
      hOtau hCtau

  have hlOB_lOC :
      Ne lOB lOC := by
    intro hEq

    apply hTri.2.1

    refine
      ⟨lOB,
       hBlOB,
       hOlOB,
       ?_⟩

    rw [hEq]

    exact hClOC

  ----------------------------------------------------------------------
  -- The target plane gamma is determined by mB and mC.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        mB mC
        hmBC
        A
        hAmB
        hAmC
    with
    ⟨gamma,
     hmBgamma,
     hmCgamma,
     _hGammaUnique⟩

  have hAgamma :
      S.OnPlane A gamma :=
    hmBgamma A hAmB

  ----------------------------------------------------------------------
  -- Package the four lines as lines of their carrier planes.
  ----------------------------------------------------------------------

  let l1 : PlaneLine Geo tau :=
    ⟨lOB, hlOBtau⟩

  let l2 : PlaneLine Geo tau :=
    ⟨lOC, hlOCtau⟩

  let m1 : PlaneLine Geo gamma :=
    ⟨mB, hmBgamma⟩

  let m2 : PlaneLine Geo gamma :=
    ⟨mC, hmCgamma⟩

  let Op : PlanePoint Geo tau :=
    ⟨O, hOtau⟩

  have hl12 :
      Ne l1 l2 := by
    intro hEq
    apply hlOB_lOC
    exact congrArg Subtype.val hEq

  ----------------------------------------------------------------------
  -- XI.15 requires that the four displayed lines are not all contained
  -- in one plane.
  --
  -- If such an omega existed, lOB and lOC would force omega = tau.
  -- Since mB contains A, this would put A in tau, contradicting the
  -- noncoplanarity of O,A,B,C.
  ----------------------------------------------------------------------

  have hNoCommonPlane :
      Not
        (exists omega : S.Plane,
          HilbertLineInPlane Geo l1.1 omega /\
          HilbertLineInPlane Geo l2.1 omega /\
          HilbertLineInPlane Geo m1.1 omega /\
          HilbertLineInPlane Geo m2.1 omega) := by

    intro hCommon

    rcases hCommon with
      ⟨omega,
       hl1omega,
       hl2omega,
       hm1omega,
       _hm2omega⟩

    have hOomega :
        S.OnPlane O omega :=
      hl1omega O hOlOB

    have hBomega :
        S.OnPlane B omega :=
      hl1omega B hBlOB

    have hComega :
        S.OnPlane C omega :=
      hl2omega C hClOC

    have hOmegaTau :
        omega = tau :=
      HSI.plane_unique
        O B C
        hOBC
        omega tau
        hOomega
        hBomega
        hComega
        hOtau
        hBtau
        hCtau

    have hAomega :
        S.OnPlane A omega :=
      hm1omega A hAmB

    have hAtau :
        S.OnPlane A tau := by
      rw [← hOmegaTau]
      exact hAomega

    exact
      hTri.2.2.2
        ⟨tau,
         hOtau,
         hAtau,
         hBtau,
         hCtau⟩

  ----------------------------------------------------------------------
  -- Euclid XI.15: the two carrier planes are parallel.
  ----------------------------------------------------------------------

  have hParallel :
      HilbertSpacePlanesParallel
        Geo tau gamma :=
    euclid_proposition_11_15
      (Geo := Geo)
      tau gamma
      l1 l2
      m1 m2
      Op
      (by
        simpa [l1, Op] using hOlOB)
      (by
        simpa [l2, Op] using hOlOC)
      hl12
      (by
        simpa [l1, m1] using hParOB)
      (by
        simpa [l2, m2] using hParOC)
      hNoCommonPlane

  have hParallelIncidence :
      HilbertSpacePlanesParallelIncidence
        Geo tau gamma := by
    simpa
      [HilbertSpacePlanesParallel,
       HilbertSpacePlanesParallelIncidence]
      using hParallel

  exact
    ⟨tau, gamma,
     hOtau,
     hBtau,
     hCtau,
     hAgamma,
     hParallelIncidence⟩


/--
A proper trihedral corner determines the three face planes through `O`
and three corresponding opposite parallel planes through `A`, `B`, `C`.
-/
theorem hilbert_trihedral_three_opposite_planes
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (O A B C : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    exists tauA gammaA tauB gammaB tauC gammaC : S.Plane,
      S.OnPlane O tauA /\
      S.OnPlane B tauA /\
      S.OnPlane C tauA /\
      S.OnPlane A gammaA /\
      HilbertSpacePlanesParallelIncidence Geo tauA gammaA /\
      S.OnPlane O tauB /\
      S.OnPlane C tauB /\
      S.OnPlane A tauB /\
      S.OnPlane B gammaB /\
      HilbertSpacePlanesParallelIncidence Geo tauB gammaB /\
      S.OnPlane O tauC /\
      S.OnPlane A tauC /\
      S.OnPlane B tauC /\
      S.OnPlane C gammaC /\
      HilbertSpacePlanesParallelIncidence Geo tauC gammaC := by

  have hTri_BCA :
      HilbertTrihedralConfiguration
        Geo O B C A := by
    refine
      ⟨hTri.2.1,
       hTri.2.2.1,
       hTri.1,
       ?_⟩
    rintro
      ⟨pi,
       hOpi,
       hBpi,
       hCpi,
       hApi⟩
    exact
      hTri.2.2.2
        ⟨pi,
         hOpi,
         hApi,
         hBpi,
         hCpi⟩

  have hTri_CAB :
      HilbertTrihedralConfiguration
        Geo O C A B := by
    refine
      ⟨hTri.2.2.1,
       hTri.1,
       hTri.2.1,
       ?_⟩
    rintro
      ⟨pi,
       hOpi,
       hCpi,
       hApi,
       hBpi⟩
    exact
      hTri.2.2.2
        ⟨pi,
         hOpi,
         hApi,
         hBpi,
         hCpi⟩

  rcases
      hilbert_trihedral_opposite_plane_through_A
        (Geo := Geo)
        O A B C
        hTri
    with
    ⟨tauA, gammaA,
     hOtauA,
     hBtauA,
     hCtauA,
     hAgammaA,
     hParA⟩

  rcases
      hilbert_trihedral_opposite_plane_through_A
        (Geo := Geo)
        O B C A
        hTri_BCA
    with
    ⟨tauB, gammaB,
     hOtauB,
     hCtauB,
     hAtauB,
     hBgammaB,
     hParB⟩

  rcases
      hilbert_trihedral_opposite_plane_through_A
        (Geo := Geo)
        O C A B
        hTri_CAB
    with
    ⟨tauC, gammaC,
     hOtauC,
     hAtauC,
     hBtauC,
     hCgammaC,
     hParC⟩

  exact
    ⟨tauA, gammaA,
     tauB, gammaB,
     tauC, gammaC,
     hOtauA,
     hBtauA,
     hCtauA,
     hAgammaA,
     hParA,
     hOtauB,
     hCtauB,
     hAtauB,
     hBgammaB,
     hParB,
     hOtauC,
     hAtauC,
     hBtauC,
     hCgammaC,
     hParC⟩


/--
If two distinct intersecting source lines are translated to parallel
target lines, the two target lines are distinct.

This is the strict-parallel version of the elementary affine fact that
two different directions cannot have one and the same translate.
-/
theorem hilbert_XI27_parallel_translates_distinct
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l1 l2 m1 m2 : Geo.Line)
    (P : Geo.Point)
    (hPl1 : H.OnLine P l1)
    (hPl2 : H.OnLine P l2)
    (hL12 : Ne l1 l2)
    (hPar1 : HilbertSpaceLinesParallel Geo l1 m1)
    (hPar2 : HilbertSpaceLinesParallel Geo l2 m2) :
    Ne m1 m2 := by

  intro hEq
  subst m2

  have hM1L2 :
      HilbertSpaceLinesParallel Geo m1 l2 :=
    hilbert_XI15_spaceLinesParallel_symm
      (Geo := Geo)
      l2 m1
      hPar2

  have hL1L2 :
      HilbertSpaceLinesParallel Geo l1 l2 :=
    hilbert_XI15_spaceParallel_transitive_distinct
      (Geo := Geo)
      l1 m1 l2
      hPar1
      hM1L2
      hL12

  rcases hL1L2 with
    ⟨_omega, _hl1, _hl2, hDisjoint⟩

  exact
    hDisjoint
      ⟨P, hPl1, hPl2⟩


/--
If two distinct intersecting source lines are translated to two target
lines lying in one plane, then the two target lines meet.

Otherwise the target lines would themselves be parallel; strict
transitivity would then make the two intersecting source lines parallel.
-/
theorem hilbert_XI27_parallel_translates_meet
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (omega : S.Plane)
    (l1 l2 m1 m2 : Geo.Line)
    (P : Geo.Point)
    (hPl1 : H.OnLine P l1)
    (hPl2 : H.OnLine P l2)
    (hL12 : Ne l1 l2)
    (hm1omega : HilbertLineInPlane Geo m1 omega)
    (hm2omega : HilbertLineInPlane Geo m2 omega)
    (hPar1 : HilbertSpaceLinesParallel Geo l1 m1)
    (hPar2 : HilbertSpaceLinesParallel Geo l2 m2) :
    HilbertLinesMeet Geo m1 m2 := by

  by_contra hNoMeet

  have hM1M2 :
      HilbertSpaceLinesParallel Geo m1 m2 :=
    ⟨omega,
     hm1omega,
     hm2omega,
     hNoMeet⟩

  have hL1M2ne : Ne l1 m2 := by
    intro hEq
    subst m2
    rcases hPar2 with
      ⟨_sigma, _hl2, _hl1, hDisjoint⟩
    exact
      hDisjoint
        ⟨P, hPl2, hPl1⟩

  have hL1M2 :
      HilbertSpaceLinesParallel Geo l1 m2 :=
    hilbert_XI15_spaceParallel_transitive_distinct
      (Geo := Geo)
      l1 m1 m2
      hPar1
      hM1M2
      hL1M2ne

  have hM2L2 :
      HilbertSpaceLinesParallel Geo m2 l2 :=
    hilbert_XI15_spaceLinesParallel_symm
      (Geo := Geo)
      l2 m2
      hPar2

  have hL1L2 :
      HilbertSpaceLinesParallel Geo l1 l2 :=
    hilbert_XI15_spaceParallel_transitive_distinct
      (Geo := Geo)
      l1 m2 l2
      hL1M2
      hM2L2
      hL12

  rcases hL1L2 with
    ⟨_sigma, _hl1, _hl2, hDisjoint⟩

  exact
    hDisjoint
      ⟨P, hPl1, hPl2⟩


------------------------------------------------------------------------
-- Full Forder VI.36.8 shell.
------------------------------------------------------------------------

/--
Forder VI.36.8, in the current Book XI representation.

A proper trihedral corner `O; A,B,C` can be completed to a full
parallelepipedal shell.

The existing arm endpoints become three vertices adjacent to `O`.
The theorem constructs the four remaining vertices and returns exactly
the neutral XI.24 structure `HilbertParallelepipedConfiguration`.
-/
theorem hilbert_parallelepiped_shell_exists_from_trihedral
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (O A B C : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    exists pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane,
    exists D E G Hpt : Geo.Point,
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A O B D E C G Hpt := by

  --------------------------------------------------------------------
  -- Stage 1.  The six planes.
  --------------------------------------------------------------------

  rcases
      hilbert_trihedral_three_opposite_planes
        (Geo := Geo)
        O A B C
        hTri
    with
    ⟨tauA, gammaA,
     tauB, gammaB,
     tauC, gammaC,
     hOtauA,
     hBtauA,
     hCtauA,
     hAgammaA,
     hParA,
     hOtauB,
     hCtauB,
     hAtauB,
     hBgammaB,
     hParB,
     hOtauC,
     hAtauC,
     hBtauC,
     hCgammaC,
     hParC⟩

  --------------------------------------------------------------------
  -- Stage 2.  Vertex D in tauC ∩ gammaB ∩ gammaA.
  --
  -- tauA || gammaA cut by tauC:
  --     OB || AD
  --
  -- tauB || gammaB cut by tauC:
  --     OA || BD
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauA gammaA tauC
        O A
        hParA
        hOtauA hOtauC
        hAgammaA hAtauC
    with
    ⟨lOB, lAD,
     hOlOB, hAlAD,
     hOBiff, hADiff,
     hParOB_AD⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauB gammaB tauC
        O B
        hParB
        hOtauB hOtauC
        hBgammaB hBtauC
    with
    ⟨lOA_D, lBD,
     hOlOA_D, hBlBD,
     hOA_D_iff, hBDiff,
     hParOA_BD⟩

  have hBlOB :
      H.OnLine B lOB :=
    (hOBiff B).mp
      ⟨hBtauA, hBtauC⟩

  have hAlOA_D :
      H.OnLine A lOA_D :=
    (hOA_D_iff A).mp
      ⟨hAtauB, hAtauC⟩

  have hSourceDNe :
      Ne lOB lOA_D := by
    intro hEq
    apply hTri.1
    refine
      ⟨lOB,
       ?_,
       hOlOB,
       hBlOB⟩
    rw [hEq]
    exact hAlOA_D

  have hlADtauC :
      HilbertLineInPlane Geo lAD tauC := by
    intro X hX
    exact (hADiff X).mpr hX |>.2

  have hlBDtauC :
      HilbertLineInPlane Geo lBD tauC := by
    intro X hX
    exact (hBDiff X).mpr hX |>.2

  have hMeetD :
      HilbertLinesMeet Geo lAD lBD :=
    hilbert_XI27_parallel_translates_meet
      (Geo := Geo)
      tauC
      lOB lOA_D
      lAD lBD
      O
      hOlOB
      hOlOA_D
      hSourceDNe
      hlADtauC
      hlBDtauC
      hParOB_AD
      hParOA_BD

  rcases hMeetD with
    ⟨D, hDlAD, hDlBD⟩

  have hDgammaA :
      S.OnPlane D gammaA :=
    (hADiff D).mpr hDlAD |>.1

  have hDtauC :
      S.OnPlane D tauC :=
    (hADiff D).mpr hDlAD |>.2

  have hDgammaB :
      S.OnPlane D gammaB :=
    (hBDiff D).mpr hDlBD |>.1

  --------------------------------------------------------------------
  -- Stage 3.  Vertex E in gammaC ∩ tauB ∩ gammaA.
  --
  -- tauA || gammaA cut by tauB:
  --     OC || AE
  --
  -- tauC || gammaC cut by tauB:
  --     OA || CE
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauA gammaA tauB
        O A
        hParA
        hOtauA hOtauB
        hAgammaA hAtauB
    with
    ⟨lOC, lAE,
     hOlOC, hAlAE,
     hOCiff, hAEiff,
     hParOC_AE⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauC gammaC tauB
        O C
        hParC
        hOtauC hOtauB
        hCgammaC hCtauB
    with
    ⟨lOA_E, lCE,
     hOlOA_E, hClCE,
     hOA_E_iff, hCEiff,
     hParOA_CE⟩

  have hClOC :
      H.OnLine C lOC :=
    (hOCiff C).mp
      ⟨hCtauA, hCtauB⟩

  have hAlOA_E :
      H.OnLine A lOA_E :=
    (hOA_E_iff A).mp
      ⟨hAtauC, hAtauB⟩

  have hSourceENe :
      Ne lOC lOA_E := by
    intro hEq
    apply hTri.2.2.1
    refine
      ⟨lOC,
       hClOC,
       hOlOC,
       ?_⟩
    rw [hEq]
    exact hAlOA_E

  have hlAEtauB :
      HilbertLineInPlane Geo lAE tauB := by
    intro X hX
    exact (hAEiff X).mpr hX |>.2

  have hlCEtauB :
      HilbertLineInPlane Geo lCE tauB := by
    intro X hX
    exact (hCEiff X).mpr hX |>.2

  have hMeetE :
      HilbertLinesMeet Geo lAE lCE :=
    hilbert_XI27_parallel_translates_meet
      (Geo := Geo)
      tauB
      lOC lOA_E
      lAE lCE
      O
      hOlOC
      hOlOA_E
      hSourceENe
      hlAEtauB
      hlCEtauB
      hParOC_AE
      hParOA_CE

  rcases hMeetE with
    ⟨E, hElAE, hElCE⟩

  have hEgammaA :
      S.OnPlane E gammaA :=
    (hAEiff E).mpr hElAE |>.1

  have hEtauB :
      S.OnPlane E tauB :=
    (hAEiff E).mpr hElAE |>.2

  have hEgammaC :
      S.OnPlane E gammaC :=
    (hCEiff E).mpr hElCE |>.1

  --------------------------------------------------------------------
  -- Stage 4.  Vertex G in gammaC ∩ gammaB ∩ tauA.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauB gammaB tauA
        O B
        hParB
        hOtauB hOtauA
        hBgammaB hBtauA
    with
    ⟨lOC_G, lBG,
     hOlOC_G, hBlBG,
     hOC_G_iff, hBGiff,
     hParOC_BG⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauC gammaC tauA
        O C
        hParC
        hOtauC hOtauA
        hCgammaC hCtauA
    with
    ⟨lOB_G, lCG,
     hOlOB_G, hClCG,
     hOB_G_iff, hCGiff,
     hParOB_CG⟩

  have hClOC_G :
      H.OnLine C lOC_G :=
    (hOC_G_iff C).mp
      ⟨hCtauB, hCtauA⟩

  have hBlOB_G :
      H.OnLine B lOB_G :=
    (hOB_G_iff B).mp
      ⟨hBtauC, hBtauA⟩

  have hSourceGNe :
      Ne lOC_G lOB_G := by
    intro hEq
    apply hTri.2.1
    refine
      ⟨lOB_G,
       hBlOB_G,
       hOlOB_G,
       ?_⟩
    rw [← hEq]
    exact hClOC_G

  have hlBGtauA :
      HilbertLineInPlane Geo lBG tauA := by
    intro X hX
    exact (hBGiff X).mpr hX |>.2

  have hlCGtauA :
      HilbertLineInPlane Geo lCG tauA := by
    intro X hX
    exact (hCGiff X).mpr hX |>.2

  have hMeetG :
      HilbertLinesMeet Geo lBG lCG :=
    hilbert_XI27_parallel_translates_meet
      (Geo := Geo)
      tauA
      lOC_G lOB_G
      lBG lCG
      O
      hOlOC_G
      hOlOB_G
      hSourceGNe
      hlBGtauA
      hlCGtauA
      hParOC_BG
      hParOB_CG

  rcases hMeetG with
    ⟨G, hGlBG, hGlCG⟩

  have hGgammaB :
      S.OnPlane G gammaB :=
    (hBGiff G).mpr hGlBG |>.1

  have hGtauA :
      S.OnPlane G tauA :=
    (hBGiff G).mpr hGlBG |>.2

  have hGgammaC :
      S.OnPlane G gammaC :=
    (hCGiff G).mpr hGlCG |>.1

  --------------------------------------------------------------------
  -- Stage 5.  Prepare the two distinct directions AD and AE in gammaA.
  --------------------------------------------------------------------

  have hSourceA_NE :
      Ne lOB lOC := by
    intro hEq
    apply hTri.2.1
    refine
      ⟨lOB,
       hBlOB,
       hOlOB,
       ?_⟩
    rw [hEq]
    exact hClOC

  have hAD_AE :
      Ne lAD lAE :=
    hilbert_XI27_parallel_translates_distinct
      (Geo := Geo)
      lOB lOC
      lAD lAE
      O
      hOlOB
      hOlOC
      hSourceA_NE
      hParOB_AD
      hParOC_AE

  --------------------------------------------------------------------
  -- Stage 6.  Vertex H in gammaC ∩ gammaB ∩ gammaA.
  --
  -- Cut tauB || gammaB by gammaA:
  --     AE || DH
  --
  -- Cut tauC || gammaC by gammaA:
  --     AD || EH
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauB gammaB gammaA
        E D
        hParB
        hEtauB hEgammaA
        hDgammaB hDgammaA
    with
    ⟨sAE, lDH,
     hEsAE, hDlDH,
     hSAEiff, hDHiff,
     hParSAE_DH⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        tauC gammaC gammaA
        D E
        hParC
        hDtauC hDgammaA
        hEgammaC hEgammaA
    with
    ⟨sAD, lEH,
     hDsAD, hElEH,
     hSADiff, hEHiff,
     hParSAD_EH⟩

  have hAsAE :
      H.OnLine A sAE :=
    (hSAEiff A).mp
      ⟨hAtauB, hAgammaA⟩

  have hAsAD :
      H.OnLine A sAD :=
    (hSADiff A).mp
      ⟨hAtauC, hAgammaA⟩

  have hAE_ne : Ne A E := by
    intro hEq
    apply hParC
    refine
      ⟨A, hAtauC, ?_⟩
    rw [hEq]
    exact hEgammaC

  have hAD_ne : Ne A D := by
    intro hEq
    apply hParB
    refine
      ⟨A, hAtauB, ?_⟩
    rw [hEq]
    exact hDgammaB

  have hEsAE' :
      H.OnLine E sAE :=
    hEsAE

  have hElAE' :
      H.OnLine E lAE :=
    hElAE

  have hDsAD' :
      H.OnLine D sAD :=
    hDsAD

  have hDlAD' :
      H.OnLine D lAD :=
    hDlAD

  have hsAE_lAE :
      sAE = lAE :=
    HilbertPlaneIncidence.line_unique
      A E hAE_ne
      sAE lAE
      hAsAE hEsAE'
      hAlAE hElAE'

  have hsAD_lAD :
      sAD = lAD :=
    HilbertPlaneIncidence.line_unique
      A D hAD_ne
      sAD lAD
      hAsAD hDsAD'
      hAlAD hDlAD'

  have hSourceHNe :
      Ne sAE sAD := by
    intro hEq
    apply hAD_AE
    rw [← hsAD_lAD, ← hsAE_lAE]
    exact hEq.symm

  have hlDHgammaA :
      HilbertLineInPlane Geo lDH gammaA := by
    intro X hX
    exact (hDHiff X).mpr hX |>.2

  have hlEHgammaA :
      HilbertLineInPlane Geo lEH gammaA := by
    intro X hX
    exact (hEHiff X).mpr hX |>.2

  have hMeetH :
      HilbertLinesMeet Geo lDH lEH :=
    hilbert_XI27_parallel_translates_meet
      (Geo := Geo)
      gammaA
      sAE sAD
      lDH lEH
      A
      hAsAE
      hAsAD
      hSourceHNe
      hlDHgammaA
      hlEHgammaA
      hParSAE_DH
      hParSAD_EH

  rcases hMeetH with
    ⟨Hpt, hHlDH, hHlEH⟩

  have hHgammaB :
      S.OnPlane Hpt gammaB :=
    (hDHiff Hpt).mpr hHlDH |>.1

  have hHgammaA :
      S.OnPlane Hpt gammaA :=
    (hDHiff Hpt).mpr hHlDH |>.2

  have hHgammaC :
      S.OnPlane Hpt gammaC :=
    (hEHiff Hpt).mpr hHlEH |>.1

  --------------------------------------------------------------------
  -- Stage 7.  Assemble the exact XI.24 configuration.
  --------------------------------------------------------------------

  refine
    ⟨tauC, gammaC,
     tauB, gammaB,
     tauA, gammaA,
     D, E, G, Hpt,
     ?_⟩

  exact
    {
      pi_parallel := hParC
      rho_parallel := hParB
      sigma_parallel := hParA

      A_on :=
        ⟨hAtauC,
         hAtauB,
         hAgammaA⟩

      B_on :=
        ⟨hOtauC,
         hOtauB,
         hOtauA⟩

      C_on :=
        ⟨hBtauC,
         hBgammaB,
         hBtauA⟩

      D_on :=
        ⟨hDtauC,
         hDgammaB,
         hDgammaA⟩

      E_on :=
        ⟨hEgammaC,
         hEtauB,
         hEgammaA⟩

      F_on :=
        ⟨hCgammaC,
         hCtauB,
         hCtauA⟩

      G_on :=
        ⟨hGgammaC,
         hGgammaB,
         hGtauA⟩

      H_on :=
        ⟨hHgammaC,
         hHgammaB,
         hHgammaA⟩
    }
/- END folded support: HilbertParallelepipedShell.lean -/


/- BEGIN folded support: Proposition11_27_scaled_shell_block_clean_v3.lean -/
/-!
# Euclid XI.27 -- scaled-corner and shell block

This file is the next large integration block for XI.27.

It keeps the Book XI spatial discipline:

* no global `HilbertOrder Geo`,
* no global `HilbertCongruence Geo`,
* planar proportion constructions are performed in explicit `PlaneGeo`
  slices,
* their raw ratio statements are then transported back to ambient space.

The one still-open mathematical input is isolated as the proposition

    HilbertSpaceV22Raw_XI27

which is the spatial raw-proportion form of the Hilbert Supplement II /
Euclid V.22 combination rule (ex aequali).  It is an explicit hypothesis,
not a new axiom.

Given that one rule, the main theorem performs in one block:

source parallelepiped
  -> source trihedral corner
  -> XI.26 angle copy on a prescribed target edge
  -> two fourth-proportional constructions on the copied rays
  -> V.22 synchronization
  -> transport of the proper trihedral corner to the scaled endpoints
  -> full Forder VI.36.8 parallelepiped shell.
-/

------------------------------------------------------------------------
-- 1. Plane quotient proportion -> concrete raw proportion.
------------------------------------------------------------------------

/--
A positive-segment proportion between four concrete quotient classes
can be read as a raw proportion between the concrete representatives.

This is only a representation bridge.  The defining right-triangle
witnesses are unchanged; `Quotient.exact` supplies the four concrete
segment congruences.
-/
theorem hilbertPositiveSegmentProportion_to_raw_XI27
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P Q R T U V W X : Geo.Point)
    (_hPQ : Ne P Q)
    (_hRT : Ne R T)
    (_hUV : Ne U V)
    (hWX : Ne W X)
    (h :
      HilbertPositiveSegmentProportion
        Geo
        (hilbertPositiveSegmentClassOf Geo P Q _hPQ)
        (hilbertPositiveSegmentClassOf Geo R T _hRT)
        (hilbertPositiveSegmentClassOf Geo U V _hUV)
        (hilbertPositiveSegmentClassOf Geo W X hWX)) :
    HilbertSegmentProportionRaw
      Geo P Q R T U V W X := by

  rcases h with
    ⟨w1, w2, hAngle⟩

  let r1 :
      HilbertSegmentRatioWitnessRaw
        Geo P Q R T :=
    {
      O := w1.O
      A := w1.A
      B := w1.B
      hOA := w1.hOA
      hOB := w1.hOB
      hNoncol := w1.hNoncol
      hRight := w1.hRight
      hNumerator := Quotient.exact w1.hFirst
      hDenominator := Quotient.exact w1.hSecond
    }

  let r2 :
      HilbertSegmentRatioWitnessRaw
        Geo U V W X :=
    {
      O := w2.O
      A := w2.A
      B := w2.B
      hOA := w2.hOA
      hOB := w2.hOB
      hNoncol := w2.hNoncol
      hRight := w2.hRight
      hNumerator := Quotient.exact w2.hFirst
      hDenominator := Quotient.exact w2.hSecond
    }

  exact
    ⟨r1, r2, hAngle⟩


------------------------------------------------------------------------
-- 2. Congruence transport for the ambient raw proportion.
------------------------------------------------------------------------

/--
Ambient raw proportion depends only on the congruence classes of the
four concrete segments.

This is the spatial analogue of replacing representatives in quotient
segment classes.
-/
theorem hilbertSpaceSegmentProportionRaw_transport_congruent_XI27
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P Q R T U V W X : Geo.Point)
    (P' Q' R' T' U' V' W' X' : Geo.Point)
    (h :
      HilbertSpaceSegmentProportionRaw
        Geo P Q R T U V W X)
    (hPQ :
      Geo.Congruent P Q P' Q')
    (hRT :
      Geo.Congruent R T R' T')
    (hUV :
      Geo.Congruent U V U' V')
    (hWX :
      Geo.Congruent W X W' X') :
    HilbertSpaceSegmentProportionRaw
      Geo P' Q' R' T' U' V' W' X' := by

  rcases h with
    ⟨w1, w2, hAngle⟩

  have hPQ_w1 :
      Geo.Congruent P Q w1.O w1.B :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w1.O w1.B
      P Q
      w1.hOB
      w1.hNumerator

  have hRT_w1 :
      Geo.Congruent R T w1.O w1.A :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w1.O w1.A
      R T
      w1.hOA
      w1.hDenominator

  have hUV_w2 :
      Geo.Congruent U V w2.O w2.B :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w2.O w2.B
      U V
      w2.hOB
      w2.hNumerator

  have hWX_w2 :
      Geo.Congruent W X w2.O w2.A :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      w2.O w2.A
      W X
      w2.hOA
      w2.hDenominator

  have hNum1 :
      Geo.Congruent w1.O w1.B P' Q' :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P Q
      w1.O w1.B
      P' Q'
      hPQ_w1
      hPQ

  have hDen1 :
      Geo.Congruent w1.O w1.A R' T' :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      R T
      w1.O w1.A
      R' T'
      hRT_w1
      hRT

  have hNum2 :
      Geo.Congruent w2.O w2.B U' V' :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      U V
      w2.O w2.B
      U' V'
      hUV_w2
      hUV

  have hDen2 :
      Geo.Congruent w2.O w2.A W' X' :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      W X
      w2.O w2.A
      W' X'
      hWX_w2
      hWX

  let w1' :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo P' Q' R' T' :=
    {
      O := w1.O
      A := w1.A
      B := w1.B
      hOA := w1.hOA
      hOB := w1.hOB
      hNoncol := w1.hNoncol
      hRight := w1.hRight
      hNumerator := hNum1
      hDenominator := hDen1
    }

  let w2' :
      HilbertSpaceSegmentRatioWitnessRaw
        Geo U' V' W' X' :=
    {
      O := w2.O
      A := w2.A
      B := w2.B
      hOA := w2.hOA
      hOB := w2.hOB
      hNoncol := w2.hNoncol
      hRight := w2.hRight
      hNumerator := hNum2
      hDenominator := hDen2
    }

  exact
    ⟨w1', w2', hAngle⟩


------------------------------------------------------------------------
-- 3. Elementary spatial ray/plane helpers.
------------------------------------------------------------------------

/--
A point on the same Hilbert ray remains in any ambient plane containing
the ray origin and the original direction point.
-/
theorem hilbert_XI27_sameRay_target_onPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (O P Q : Geo.Point)
    (hRay : HilbertSameRay Geo O P Q)
    (hOpi : S.OnPlane O pi)
    (hPpi : S.OnPlane P pi) :
    S.OnPlane Q pi := by

  rcases hRay.2.2.1 with
    ⟨l, hOl, hPl, hQl⟩

  have hOP : Ne O P :=
    hRay.1.symm

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HSI.line_in_plane
      O P hOP
      l
      hOl hPl
      pi
      hOpi hPpi

  exact hlpi Q hQl


/--
Conversely, if the origin and a new representative of the ray are in a
plane, then the original direction point is in that plane as well.
-/
theorem hilbert_XI27_sameRay_source_onPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (O P Q : Geo.Point)
    (hRay : HilbertSameRay Geo O P Q)
    (hOpi : S.OnPlane O pi)
    (hQpi : S.OnPlane Q pi) :
    S.OnPlane P pi := by

  rcases hRay.2.2.1 with
    ⟨l, hOl, hPl, hQl⟩

  have hOQ : Ne O Q :=
    hRay.2.1.symm

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HSI.line_in_plane
      O Q hOQ
      l
      hOl hQl
      pi
      hOpi hQpi

  exact hlpi P hPl


/--
Reflexivity of a spatial Hilbert ray, derived directly from the spatial
order interface rather than by installing an ambient `HilbertOrder`.
-/
theorem hilbert_XI27_sameRay_refl_space
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O P : Geo.Point)
    (hOP : Ne O P) :
    HilbertSameRay Geo O P P := by

  rcases
      HilbertPlaneIncidence.line_through
        O P hOP
    with
    ⟨l, hOl, hPl⟩

  refine
    ⟨hOP.symm,
     hOP.symm,
     ⟨l, hOl, hPl, hPl⟩,
     ?_⟩

  intro hPOP

  exact
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      P O P hPOP).2.2.1 rfl


/--
Incidence-only preservation of noncollinearity when the two arms of an
angle are replaced by points on the same rays.

The usual planar theorem needs `HilbertOrder`; this version is suitable
for ambient Book XI space and uses only line uniqueness.
-/
theorem hilbert_XI27_noncollinear_of_sameRays_space
    [H : HilbertIncidence Geo]
    [HPI : HilbertPlaneIncidence Geo]
    (A O B X Y : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hAX : HilbertSameRay Geo O A X)
    (hBY : HilbertSameRay Geo O B Y) :
    Not (PrimCollinear Geo X O Y) := by

  intro hXOY

  rcases hAX.2.2.1 with
    ⟨l1, hOl1, hAl1, hXl1⟩

  rcases hBY.2.2.1 with
    ⟨l2, hOl2, hBl2, hYl2⟩

  rcases hXOY with
    ⟨l3, hXl3, hOl3, hYl3⟩

  have hOX : Ne O X :=
    hAX.2.1.symm

  have hOY : Ne O Y :=
    hBY.2.1.symm

  have h13 : l1 = l3 :=
    HilbertPlaneIncidence.line_unique
      O X hOX
      l1 l3
      hOl1 hXl1
      hOl3 hXl3

  have h32 : l3 = l2 :=
    HilbertPlaneIncidence.line_unique
      O Y hOY
      l3 l2
      hOl3 hYl3
      hOl2 hYl2

  have hAl3 : H.OnLine A l3 := by
    rw [← h13]
    exact hAl1

  have hBl3 : H.OnLine B l3 := by
    rw [h32]
    exact hBl2

  exact
    hAOB
      ⟨l3, hAl3, hOl3, hBl3⟩


/--
A proper trihedral corner stays proper when each arm endpoint is moved
along its original ray.
-/
theorem hilbert_XI27_trihedral_transport_sameRays
    [H : HilbertIncidence Geo]
    [HPI : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (O A B C A' B' C' : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo O A B C)
    (hA :
      HilbertSameRay Geo O A A')
    (hB :
      HilbertSameRay Geo O B B')
    (hC :
      HilbertSameRay Geo O C C') :
    HilbertTrihedralConfiguration
      Geo O A' B' C' := by

  have hAOB :
      Not (PrimCollinear Geo A' O B') :=
    hilbert_XI27_noncollinear_of_sameRays_space
      (Geo := Geo)
      A O B A' B'
      hTri.1
      hA hB

  have hBOC :
      Not (PrimCollinear Geo B' O C') :=
    hilbert_XI27_noncollinear_of_sameRays_space
      (Geo := Geo)
      B O C B' C'
      hTri.2.1
      hB hC

  have hCOA :
      Not (PrimCollinear Geo C' O A') :=
    hilbert_XI27_noncollinear_of_sameRays_space
      (Geo := Geo)
      C O A C' A'
      hTri.2.2.1
      hC hA

  have hNoncop :
      Not
        (exists pi : S.Plane,
          S.OnPlane O pi /\
          S.OnPlane A' pi /\
          S.OnPlane B' pi /\
          S.OnPlane C' pi) := by

    rintro
      ⟨pi,
       hOpi,
       hA'pi,
       hB'pi,
       hC'pi⟩

    have hApi :
        S.OnPlane A pi :=
      hilbert_XI27_sameRay_source_onPlane
        (Geo := Geo)
        pi O A A'
        hA
        hOpi hA'pi

    have hBpi :
        S.OnPlane B pi :=
      hilbert_XI27_sameRay_source_onPlane
        (Geo := Geo)
        pi O B B'
        hB
        hOpi hB'pi

    have hCpi :
        S.OnPlane C pi :=
      hilbert_XI27_sameRay_source_onPlane
        (Geo := Geo)
        pi O C C'
        hC
        hOpi hC'pi

    exact
      hTri.2.2.2
        ⟨pi,
         hOpi,
         hApi,
         hBpi,
         hCpi⟩

  exact
    ⟨hAOB,
     hBOC,
     hCOA,
     hNoncop⟩


/--
Transport an ambient angle when its two arms are replaced by points on
the same rays.  The proof creates the explicit carrier plane and uses
the established `PlaneGeo` bridge.
-/
theorem hilbert_XI27_angleCongruent_sameRays_space
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A O B A' B' : Geo.Point)
    (hAOB :
      Not (PrimCollinear Geo A O B))
    (hA :
      HilbertSameRay Geo O A A')
    (hB :
      HilbertSameRay Geo O B B') :
    Geo.AngleCongruent
      A O B A' O B' := by

  rcases
      HSI.plane_through
        A O B hAOB
    with
    ⟨pi, hApi, hOpi, hBpi⟩

  have hA'pi :
      S.OnPlane A' pi :=
    hilbert_XI27_sameRay_target_onPlane
      (Geo := Geo)
      pi O A A'
      hA
      hOpi hApi

  have hB'pi :
      S.OnPlane B' pi :=
    hilbert_XI27_sameRay_target_onPlane
      (Geo := Geo)
      pi O B B'
      hB
      hOpi hBpi

  exact
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      pi
      A O B
      A' B'
      hApi hOpi hBpi
      hA'pi hB'pi
      hAOB
      hA hB


------------------------------------------------------------------------
-- 4. Spatial fourth proportional on a prescribed ray.
------------------------------------------------------------------------

/--
Spatial form of the Hilbert/VI.12 fourth-proportional construction.

The three given concrete segments may lie anywhere in ambient space.
They are copied into one explicit plane containing the prescribed ray;
the planar quotient-class theorem constructs the fourth class there;
that class is realized on the prescribed ray; finally the raw proportion
is transported back to the original three ambient segments.

No global planar structure is installed on ambient `Geo`.
-/
theorem hilbertSpaceSegmentProportionRaw_fourth_on_ray_XI27
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P Q R T U V O W : Geo.Point)
    (_hPQ : Ne P Q)
    (_hRT : Ne R T)
    (_hUV : Ne U V)
    (hOW : Ne O W)
    (hOpi : S.OnPlane O pi)
    (hWpi : S.OnPlane W pi) :
    exists X : Geo.Point,
      HilbertSameRay Geo O W X /\
      Ne O X /\
      HilbertSpaceSegmentProportionRaw
        Geo P Q R T U V O X := by

  --------------------------------------------------------------------
  -- Copy the three input lengths onto the fixed ray OW.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        P Q O W hOW
    with
    ⟨X1, hRay1, hOX1_PQ⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        R T O W hOW
    with
    ⟨X2, hRay2, hOX2_RT⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        U V O W hOW
    with
    ⟨X3, hRay3, hOX3_UV⟩

  have hX1pi :
      S.OnPlane X1 pi :=
    hilbert_XI27_sameRay_target_onPlane
      (Geo := Geo)
      pi O W X1
      hRay1
      hOpi hWpi

  have hX2pi :
      S.OnPlane X2 pi :=
    hilbert_XI27_sameRay_target_onPlane
      (Geo := Geo)
      pi O W X2
      hRay2
      hOpi hWpi

  have hX3pi :
      S.OnPlane X3 pi :=
    hilbert_XI27_sameRay_target_onPlane
      (Geo := Geo)
      pi O W X3
      hRay3
      hOpi hWpi

  have hOX1 : Ne O X1 :=
    hRay1.2.1.symm

  have hOX2 : Ne O X2 :=
    hRay2.2.1.symm

  have hOX3 : Ne O X3 :=
    hRay3.2.1.symm

  --------------------------------------------------------------------
  -- Move to PlaneGeo(pi).
  --------------------------------------------------------------------

  let Op : PlanePoint Geo pi :=
    ⟨O, hOpi⟩

  let Wp : PlanePoint Geo pi :=
    ⟨W, hWpi⟩

  let X1p : PlanePoint Geo pi :=
    ⟨X1, hX1pi⟩

  let X2p : PlanePoint Geo pi :=
    ⟨X2, hX2pi⟩

  let X3p : PlanePoint Geo pi :=
    ⟨X3, hX3pi⟩

  have hOpWp : Ne Op Wp := by
    intro hEq
    apply hOW
    exact congrArg Subtype.val hEq

  have hOpX1p : Ne Op X1p := by
    intro hEq
    apply hOX1
    exact congrArg Subtype.val hEq

  have hOpX2p : Ne Op X2p := by
    intro hEq
    apply hOX2
    exact congrArg Subtype.val hEq

  have hOpX3p : Ne Op X3p := by
    intro hEq
    apply hOX3
    exact congrArg Subtype.val hEq

  rcases
      hilbertPositiveSegmentProportion_fourth_exists
        (Geo := PlaneGeo Geo pi)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X1p hOpX1p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X2p hOpX2p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X3p hOpX3p)
    with
    ⟨d, hFourthClass⟩

  rcases
      hilbertPositiveSegmentRayPointData_exists
        (Geo := PlaneGeo Geo pi)
        Op Wp hOpWp d
    with
    ⟨data⟩

  let Xp : PlanePoint Geo pi :=
    data.point

  have hFourthConcrete :
      HilbertPositiveSegmentProportion
        (PlaneGeo Geo pi)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X1p hOpX1p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X2p hOpX2p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X3p hOpX3p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op Xp data.ne_origin) := by
    change
      HilbertPositiveSegmentProportion
        (PlaneGeo Geo pi)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X1p hOpX1p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X2p hOpX2p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op X3p hOpX3p)
        (hilbertPositiveSegmentClassOf
          (PlaneGeo Geo pi)
          Op data.point data.ne_origin)

    rw [data.class_eq]

    exact hFourthClass

  have hRawPlane :
      HilbertSegmentProportionRaw
        (PlaneGeo Geo pi)
        Op X1p
        Op X2p
        Op X3p
        Op Xp :=
    hilbertPositiveSegmentProportion_to_raw_XI27
      (Geo := PlaneGeo Geo pi)
      Op X1p
      Op X2p
      Op X3p
      Op Xp
      hOpX1p
      hOpX2p
      hOpX3p
      data.ne_origin
      hFourthConcrete

  have hRawCopies0 :=
    hilbertSegmentProportionRaw_to_space
      (Geo := Geo)
      pi
      Op X1p
      Op X2p
      Op X3p
      Op Xp
      hRawPlane

  have hRawCopies :
      HilbertSpaceSegmentProportionRaw
        Geo
        O X1
        O X2
        O X3
        O Xp.1 := by
    simpa [Op, X1p, X2p, X3p, Xp] using hRawCopies0

  have hRayX :
      HilbertSameRay Geo O W Xp.1 := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi
        Op Wp Xp).mp data.sameRay

    simpa [Op, Wp, Xp] using hAmbient

  have hOX : Ne O Xp.1 := by
    intro hEq
    apply data.ne_origin
    apply Subtype.ext
    exact hEq

  have hOXX :
      Geo.Congruent O Xp.1 O Xp.1 :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      O Xp.1 hOX

  have hFinal :
      HilbertSpaceSegmentProportionRaw
        Geo P Q R T U V O Xp.1 :=
    hilbertSpaceSegmentProportionRaw_transport_congruent_XI27
      (Geo := Geo)
      O X1
      O X2
      O X3
      O Xp.1
      P Q
      R T
      U V
      O Xp.1
      hRawCopies
      hOX1_PQ
      hOX2_RT
      hOX3_UV
      hOXX

  exact
    ⟨Xp.1,
     hRayX,
     hOX,
     hFinal⟩


------------------------------------------------------------------------
-- 5. The one still-open Book V rule, stated in ambient raw language.
------------------------------------------------------------------------

/--
Spatial raw form of the first Hilbert combination rule / Euclid V.22:

    a : b = a' : b'
    b : c = b' : c'
    -----------------
    a : c = a' : c'

This is the exact proportion theorem still to be discharged from
Hilbert Supplement II.  It is deliberately a `Prop` interface here,
not an axiom declaration.
-/
def HilbertSpaceV22Raw_XI27
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)] : Prop :=
  forall
    A B C D E F
    A' B' C' D' E' F' : Geo.Point,
      HilbertSpaceSegmentProportionRaw
        Geo
        A B C D
        A' B' C' D' ->
      HilbertSpaceSegmentProportionRaw
        Geo
        C D E F
        C' D' E' F' ->
      HilbertSpaceSegmentProportionRaw
        Geo
        A B E F
        A' B' E' F'


------------------------------------------------------------------------
-- 6. Main XI.27 scaled-corner + shell integration theorem.
------------------------------------------------------------------------

/--
XI.27 construction block up to the final similarity packaging.

Starting from a source parallelepiped and a prescribed nondegenerate
target edge A0B0:

1. extract the source corner at B from XI.24;
2. copy its three angles at A0 by XI.26;
3. use spatialized VI.12 twice to choose K on ray A0L and J on ray A0H;
4. combine the two proportions by the raw V.22 rule;
5. transport the proper trihedral corner from B0,L,H to B0,K,J;
6. transport the three copied angles to the scaled rays;
7. complete the full target parallelepiped shell by Forder VI.36.8.

The theorem returns the three target edge proportions explicitly.
The remaining XI.27 work after this block is the face-similarity /
XI.Def.9 packaging.
-/
theorem hilbert_XI27_scaled_shell_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (hV22 :
      HilbertSpaceV22Raw_XI27
        (Geo := Geo))
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)
    (A0 B0 : Geo.Point)
    (hA0B0 : Ne A0 B0) :
    exists K J : Geo.Point,
    exists _hA0K : Ne A0 K,
    exists _hA0J : Ne A0 J,
      HilbertTrihedralConfiguration
        Geo A0 B0 K J /\
      Geo.AngleCongruent
        B0 A0 K
        A B C /\
      Geo.AngleCongruent
        K A0 J
        C B F /\
      Geo.AngleCongruent
        J A0 B0
        F B A /\
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B C
        A0 B0 A0 K /\
      HilbertSpaceSegmentProportionRaw
        Geo
        B C B F
        A0 K A0 J /\
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B F
        A0 B0 A0 J /\
      exists
        tpi0 tpi1 trho0 trho1 tsigma0 tsigma1 : S.Plane,
      exists TD TE TG TH : Geo.Point,
        HilbertParallelepipedConfiguration
          (Geo := Geo)
          tpi0 tpi1 trho0 trho1 tsigma0 tsigma1
          B0 A0 K TD TE J TG TH := by

  --------------------------------------------------------------------
  -- Source corner B; A,C,F from XI.24.
  --------------------------------------------------------------------

  have hSourceTri :
      HilbertTrihedralConfiguration
        Geo B A C F :=
    hilbertParallelepipedConfiguration_trihedral_at_B
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hBA : Ne B A := by
    exact
      (hilbert_noncollinear_ne_first
        Geo A B C hSourceTri.1).symm

  have hCBA :
      Not (PrimCollinear Geo C B A) := by
    intro hCol
    exact
      hSourceTri.1
        (PrimCollinearSymm
          Geo C B A hCol)

  have hBC : Ne B C := by
    exact
      (hilbert_noncollinear_ne_first
        Geo C B A hCBA).symm

  have hBF : Ne B F := by
    exact
      (hilbert_noncollinear_ne_first
        Geo F B A hSourceTri.2.2.1).symm

  --------------------------------------------------------------------
  -- XI.26: copy the source trihedral angles onto edge A0B0.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_26
        (Geo := Geo)
        B A C F
        A0 B0
        hSourceTri
        hA0B0
    with
    ⟨L, H1, hRealizes⟩

  have hTargetTri :
      HilbertTrihedralConfiguration
        Geo A0 B0 L H1 :=
    hRealizes.1

  have hA0L : Ne A0 L := by
    exact
      (hilbert_noncollinear_ne_first
        Geo L A0 H1 hTargetTri.2.1).symm

  have hA0H : Ne A0 H1 := by
    exact
      (hilbert_noncollinear_ne_first
        Geo H1 A0 B0 hTargetTri.2.2.1).symm

  --------------------------------------------------------------------
  -- First target face: BA:BC = A0B0:A0K, with K on ray A0L.
  --------------------------------------------------------------------

  rcases
      HSI.plane_through
        B0 A0 L hTargetTri.1
    with
    ⟨tau1,
     hB0tau1,
     hA0tau1,
     hLtau1⟩

  rcases
      hilbertSpaceSegmentProportionRaw_fourth_on_ray_XI27
        (Geo := Geo)
        tau1
        B A
        B C
        A0 B0
        A0 L
        hBA
        hBC
        hA0B0
        hA0L
        hA0tau1
        hLtau1
    with
    ⟨K,
     hRayK,
     hA0K,
     hProp1⟩

  --------------------------------------------------------------------
  -- Second target face: BC:BF = A0K:A0J, with J on ray A0H.
  --------------------------------------------------------------------

  rcases
      HSI.plane_through
        L A0 H1 hTargetTri.2.1
    with
    ⟨tau2,
     hLtau2,
     hA0tau2,
     hHtau2⟩

  rcases
      hilbertSpaceSegmentProportionRaw_fourth_on_ray_XI27
        (Geo := Geo)
        tau2
        B C
        B F
        A0 K
        A0 H1
        hBC
        hBF
        hA0K
        hA0H
        hA0tau2
        hHtau2
    with
    ⟨J,
     hRayJ,
     hA0J,
     hProp2⟩

  --------------------------------------------------------------------
  -- V.22 / Hilbert combination rule:
  --
  --   BA:BC = A0B0:A0K
  --   BC:BF = A0K:A0J
  --   -----------------
  --   BA:BF = A0B0:A0J.
  --------------------------------------------------------------------

  have hProp3 :
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B F
        A0 B0 A0 J :=
    hV22
      B A
      B C
      B F
      A0 B0
      A0 K
      A0 J
      hProp1
      hProp2

  --------------------------------------------------------------------
  -- Move the proper target corner from B0,L,H to B0,K,J.
  --------------------------------------------------------------------

  have hRayB0 :
      HilbertSameRay Geo A0 B0 B0 :=
    hilbert_XI27_sameRay_refl_space
      (Geo := Geo)
      A0 B0 hA0B0

  have hScaledTri :
      HilbertTrihedralConfiguration
        Geo A0 B0 K J :=
    hilbert_XI27_trihedral_transport_sameRays
      (Geo := Geo)
      A0
      B0 L H1
      B0 K J
      hTargetTri
      hRayB0
      hRayK
      hRayJ

  --------------------------------------------------------------------
  -- Transport the three XI.26 angle equalities onto the scaled rays.
  --------------------------------------------------------------------

  have hMove1 :
      Geo.AngleCongruent
        B0 A0 L
        B0 A0 K :=
    hilbert_XI27_angleCongruent_sameRays_space
      (Geo := Geo)
      B0 A0 L
      B0 K
      hTargetTri.1
      hRayB0
      hRayK

  have hMove2 :
      Geo.AngleCongruent
        L A0 H1
        K A0 J :=
    hilbert_XI27_angleCongruent_sameRays_space
      (Geo := Geo)
      L A0 H1
      K J
      hTargetTri.2.1
      hRayK
      hRayJ

  have hMove3 :
      Geo.AngleCongruent
        H1 A0 B0
        J A0 B0 :=
    hilbert_XI27_angleCongruent_sameRays_space
      (Geo := Geo)
      H1 A0 B0
      J B0
      hTargetTri.2.2.1
      hRayJ
      hRayB0

  have hAngle1 :
      Geo.AngleCongruent
        B0 A0 K
        A B C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B0 A0 K
      B0 A0 L
      A B C
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B0 A0 L
        B0 A0 K
        hMove1)
      hRealizes.2.1

  have hAngle2 :
      Geo.AngleCongruent
        K A0 J
        C B F :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K A0 J
      L A0 H1
      C B F
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        L A0 H1
        K A0 J
        hMove2)
      hRealizes.2.2.1

  have hAngle3 :
      Geo.AngleCongruent
        J A0 B0
        F B A :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      J A0 B0
      H1 A0 B0
      F B A
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        H1 A0 B0
        J A0 B0
        hMove3)
      hRealizes.2.2.2

  --------------------------------------------------------------------
  -- Complete the full target shell.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelepiped_shell_exists_from_trihedral
        (Geo := Geo)
        A0 B0 K J
        hScaledTri
    with
    ⟨tpi0, tpi1,
     trho0, trho1,
     tsigma0, tsigma1,
     TD, TE, TG, TH,
     hTargetCfg⟩

  exact
    ⟨K, J,
     hA0K,
     hA0J,
     hScaledTri,
     hAngle1,
     hAngle2,
     hAngle3,
     hProp1,
     hProp2,
     hProp3,
     tpi0, tpi1,
     trho0, trho1,
     tsigma0, tsigma1,
     TD, TE, TG, TH,
     hTargetCfg⟩
/- END folded support: Proposition11_27_scaled_shell_block_clean_v3.lean -/


/- BEGIN folded support: XI27_v22_integrated_v1.lean -/
/-!
# XI.27 integration after spatial V.22

This file removes the abstract `HilbertSpaceV22Raw_XI27` input from the
scaled-shell theorem.  The only remaining open mathematical kernel is the
plane-wise Hilbert crossing-rays theorem.

No new axiom is declared.
-/

------------------------------------------------------------------------
-- 1. Discharge the XI.27 V.22 interface from spatial raw V.22.
------------------------------------------------------------------------

theorem hilbertSpaceV22Raw_XI27_of_crossing
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo] :
    HilbertSpaceV22Raw_XI27
      (Geo := Geo) := by

  have hCross :
      HilbertSpaceCrossingRaysTransfer
        (Geo := Geo) := by
    intro pi
    exact
      hilbert_crossing_rays_transfer
        (PlaneGeo Geo pi)

  intro
    A B C D E F
    Ap Bp Cp Dp Ep Fp
    h1 h2

  exact
    hilbertSpaceSegmentProportionRaw_V22_of_crossing
      (Geo := Geo)
      hCross
      A B C D E F
      Ap Bp Cp Dp Ep Fp
      h1 h2


------------------------------------------------------------------------
-- 2. XI.27 scaled shell with V.22 no longer an external hypothesis.
------------------------------------------------------------------------

/--
XI.27 scaled-corner plus complete parallelepiped shell, with the raw V.22
obligation discharged internally.

The only still-open input is `HilbertSpaceCrossingRaysTransfer`, i.e. the
plane-wise Hilbert Supplement II crossing-rays theorem.
-/
theorem hilbert_XI27_scaled_shell_exists_of_crossing
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)
    (A0 B0 : Geo.Point)
    (hA0B0 : Ne A0 B0) :
    exists K J : Geo.Point,
    exists _hA0K : Ne A0 K,
    exists _hA0J : Ne A0 J,
      HilbertTrihedralConfiguration
        Geo A0 B0 K J /\
      Geo.AngleCongruent
        B0 A0 K
        A B C /\
      Geo.AngleCongruent
        K A0 J
        C B F /\
      Geo.AngleCongruent
        J A0 B0
        F B A /\
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B C
        A0 B0 A0 K /\
      HilbertSpaceSegmentProportionRaw
        Geo
        B C B F
        A0 K A0 J /\
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B F
        A0 B0 A0 J /\
      exists
        tpi0 tpi1 trho0 trho1 tsigma0 tsigma1 : S.Plane,
      exists TD TE TG TH : Geo.Point,
        HilbertParallelepipedConfiguration
          (Geo := Geo)
          tpi0 tpi1 trho0 trho1 tsigma0 tsigma1
          B0 A0 K TD TE J TG TH := by

  have hV22 :
      HilbertSpaceV22Raw_XI27
        (Geo := Geo) :=
    hilbertSpaceV22Raw_XI27_of_crossing
      (Geo := Geo)

  exact
    hilbert_XI27_scaled_shell_exists
      (Geo := Geo)
      hV22
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg
      A0 B0
      hA0B0
/- END folded support: XI27_v22_integrated_v1.lean -/


/- BEGIN final XI.27 proposition -/
/-!
# Euclid XI.27

Production consolidation candidate.

This file contains the complete XI.27 chain:
* scaled trihedral corner and target shell;
* similarity of the three adjacent faces;
* plane-local recovery of opposite-edge congruences;
* XI.10 transport of opposite-face angles;
* similarity of the three opposite faces;
* packaging by Euclid XI.Def.9.

No global ambient `HilbertOrder Geo` is assumed.
-/


def HilbertSpaceFaceCornerSimilar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C A' B' C' : Geo.Point) : Prop :=
  HilbertSpaceSegmentProportionRaw
      Geo
      B A B C
      B' A' B' C' /\
    Geo.AngleCongruent
      A B C
      A' B' C'

theorem hilbert_XI27_three_adjacent_face_corners_similar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C F A0 B0 K J : Geo.Point)
    (hAngPi :
      Geo.AngleCongruent
        B0 A0 K
        A B C)
    (hAngSigma :
      Geo.AngleCongruent
        K A0 J
        C B F)
    (hAngRho :
      Geo.AngleCongruent
        J A0 B0
        F B A)
    (hPropPi :
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B C
        A0 B0 A0 K)
    (hPropSigma :
      HilbertSpaceSegmentProportionRaw
        Geo
        B C B F
        A0 K A0 J)
    (hPropRho :
      HilbertSpaceSegmentProportionRaw
        Geo
        B A B F
        A0 B0 A0 J) :
    HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B C
        B0 A0 K /\
    HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        C B F
        K A0 J /\
    HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B F
        B0 A0 J := by

  constructor

  · constructor
    · exact hPropPi
    · exact
        Geometry.Geo.angle_congruent_symmetry
          Geo
          B0 A0 K
          A B C
          hAngPi

  constructor

  · constructor
    · exact hPropSigma
    · exact
        Geometry.Geo.angle_congruent_symmetry
          Geo
          K A0 J
          C B F
          hAngSigma

  · constructor
    · exact hPropRho
    · have h1 :
          Geo.AngleCongruent
            F B A
            J A0 B0 :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          J A0 B0
          F B A
          hAngRho

      have h2 :
          Geo.AngleCongruent
            A B F
            J A0 B0 := by
        exact
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            F B A
            J A0 B0).mp
            h1

      exact
        (Geometry.Geo.angle_congruent_reverse_second
          Geo
          A B F
          J A0 B0).mp
          h2


/--
Transport an ambient-space face-corner similarity through congruent
replacements of its four incident sides and through congruent replacement
of the included angles.
-/
theorem hilbertSpaceFaceCornerSimilar_transport
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C A' B' C' : Geo.Point)
    (D E F D' E' F' : Geo.Point)
    (hSim :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B C
        A' B' C')
    (hBA_ED :
      Geo.Congruent B A E D)
    (hBC_EF :
      Geo.Congruent B C E F)
    (hB'A'_E'D' :
      Geo.Congruent B' A' E' D')
    (hB'C'_E'F' :
      Geo.Congruent B' C' E' F')
    (hLeftAngle :
      Geo.AngleCongruent
        D E F
        A B C)
    (hRightAngle :
      Geo.AngleCongruent
        A' B' C'
        D' E' F') :
    HilbertSpaceFaceCornerSimilar
      (Geo := Geo)
      D E F
      D' E' F' := by

  rcases hSim with
    ⟨hProp, hAngle⟩

  constructor

  · exact
      hilbertSpaceSegmentProportionRaw_transport_congruent_XI27
        (Geo := Geo)
        B A
        B C
        B' A'
        B' C'
        E D
        E F
        E' D'
        E' F'
        hProp
        hBA_ED
        hBC_EF
        hB'A'_E'D'
        hB'C'_E'F'

  · exact
      Geometry.Geo.angle_congruent_transitivity
        Geo
        D E F
        A B C
        D' E' F'
        hLeftAngle
        (Geometry.Geo.angle_congruent_transitivity
          Geo
          A B C
          A' B' C'
          D' E' F'
          hAngle
          hRightAngle)


/--
One parallelepiped face: derive congruence of opposite sides without
installing a global ambient `HilbertOrder Geo`.

The parallelogram is constructed only inside `PlaneGeo pi`.
-/
theorem hilbert_XI27_face_opposite_sides_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D : Geo.Point)
    (hRho :
      HilbertSpacePlanesParallelIncidence Geo rho0 rho1)
    (hSigma :
      HilbertSpacePlanesParallelIncidence Geo sigma0 sigma1)
    (hApi : S.OnPlane A pi)
    (hArho0 : S.OnPlane A rho0)
    (hAsigma1 : S.OnPlane A sigma1)
    (hBpi : S.OnPlane B pi)
    (hBrho0 : S.OnPlane B rho0)
    (hBsigma0 : S.OnPlane B sigma0)
    (hCpi : S.OnPlane C pi)
    (hCrho1 : S.OnPlane C rho1)
    (hCsigma0 : S.OnPlane C sigma0)
    (hDpi : S.OnPlane D pi)
    (hDrho1 : S.OnPlane D rho1)
    (hDsigma1 : S.OnPlane D sigma1) :
    OppositeSidesCongruent Geo A B C D := by

  have hAB : Ne A B := by
    intro hEq
    subst B
    exact hSigma
      ⟨A, hBsigma0, hAsigma1⟩

  have hCD : Ne C D := by
    intro hEq
    subst D
    exact hSigma
      ⟨C, hCsigma0, hDsigma1⟩

  have hBC : Ne B C := by
    intro hEq
    subst C
    exact hRho
      ⟨B, hBrho0, hCrho1⟩

  have hDA : Ne D A := by
    intro hEq
    subst A
    exact hRho
      ⟨D, hArho0, hDrho1⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        rho0 rho1 pi
        A D
        hRho
        hArho0 hApi
        hDrho1 hDpi
    with
    ⟨l, m, hAl, hDm, hRho0Iff, hRho1Iff, hLMparallel⟩

  have hBl : H.OnLine B l :=
    (hRho0Iff B).mp ⟨hBrho0, hBpi⟩

  have hCm : H.OnLine C m :=
    (hRho1Iff C).mp ⟨hCrho1, hCpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HSI.line_in_plane
      A B hAB
      l hAl hBl
      pi hApi hBpi

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    HSI.line_in_plane
      C D hCD
      m hCm hDm
      pi hCpi hDpi

  have hLMdisjoint :
      HilbertLinesDisjoint Geo l m := by
    rcases hLMparallel with
      ⟨_omega, _hlomega, _hmomega, hDisjoint⟩
    exact hDisjoint

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        sigma0 sigma1 pi
        B A
        hSigma
        hBsigma0 hBpi
        hAsigma1 hApi
    with
    ⟨n, q, hBn, hAq, hSigma0Iff, hSigma1Iff, hNQparallel⟩

  have hCn : H.OnLine C n :=
    (hSigma0Iff C).mp ⟨hCsigma0, hCpi⟩

  have hDq : H.OnLine D q :=
    (hSigma1Iff D).mp ⟨hDsigma1, hDpi⟩

  have hnpi :
      HilbertLineInPlane Geo n pi :=
    HSI.line_in_plane
      B C hBC
      n hBn hCn
      pi hBpi hCpi

  have hqpi :
      HilbertLineInPlane Geo q pi :=
    HSI.line_in_plane
      D A hDA
      q hDq hAq
      pi hDpi hApi

  have hNQdisjoint :
      HilbertLinesDisjoint Geo n q := by
    rcases hNQparallel with
      ⟨_omega, _hnowega, _hqomega, hDisjoint⟩
    exact hDisjoint

  let Ap : PlanePoint Geo pi := ⟨A, hApi⟩
  let Bp : PlanePoint Geo pi := ⟨B, hBpi⟩
  let Cp : PlanePoint Geo pi := ⟨C, hCpi⟩
  let Dp : PlanePoint Geo pi := ⟨D, hDpi⟩

  let lp : PlaneLine Geo pi := ⟨l, hlpi⟩
  let mp : PlaneLine Geo pi := ⟨m, hmpi⟩
  let np : PlaneLine Geo pi := ⟨n, hnpi⟩
  let qp : PlaneLine Geo pi := ⟨q, hqpi⟩

  have hABp : Ne Ap Bp := by
    intro hEq
    apply hAB
    exact congrArg Subtype.val hEq

  have hCDp : Ne Cp Dp := by
    intro hEq
    apply hCD
    exact congrArg Subtype.val hEq

  have hBCp : Ne Bp Cp := by
    intro hEq
    apply hBC
    exact congrArg Subtype.val hEq

  have hDAp : Ne Dp Ap := by
    intro hEq
    apply hDA
    exact congrArg Subtype.val hEq

  have hAlp : (PlaneGeo Geo pi).OnLine Ap lp := hAl
  have hBlp : (PlaneGeo Geo pi).OnLine Bp lp := hBl
  have hCmp : (PlaneGeo Geo pi).OnLine Cp mp := hCm
  have hDmp : (PlaneGeo Geo pi).OnLine Dp mp := hDm

  have hBnp : (PlaneGeo Geo pi).OnLine Bp np := hBn
  have hCnp : (PlaneGeo Geo pi).OnLine Cp np := hCn
  have hDqp : (PlaneGeo Geo pi).OnLine Dp qp := hDq
  have hAqp : (PlaneGeo Geo pi).OnLine Ap qp := hAq

  have hABCDp :
      (PlaneGeo Geo pi).Parallel Ap Bp Cp Dp := by
    refine ⟨hABp, hCDp, ?_⟩
    apply Set.disjoint_left.mpr
    intro Xp hXAB hXCD

    have hXl :
        (PlaneGeo Geo pi).OnLine Xp lp :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo pi)
        Ap Bp Xp lp
        hABp hAlp hBlp).mp hXAB

    have hXm :
        (PlaneGeo Geo pi).OnLine Xp mp :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo pi)
        Cp Dp Xp mp
        hCDp hCmp hDmp).mp hXCD

    exact hLMdisjoint ⟨Xp.1, hXl, hXm⟩

  have hBCDAP :
      (PlaneGeo Geo pi).Parallel Bp Cp Dp Ap := by
    refine ⟨hBCp, hDAp, ?_⟩
    apply Set.disjoint_left.mpr
    intro Xp hXBC hXDA

    have hXn :
        (PlaneGeo Geo pi).OnLine Xp np :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo pi)
        Bp Cp Xp np
        hBCp hBnp hCnp).mp hXBC

    have hXq :
        (PlaneGeo Geo pi).OnLine Xp qp :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo pi)
        Dp Ap Xp qp
        hDAp hDqp hAqp).mp hXDA

    exact hNQdisjoint ⟨Xp.1, hXn, hXq⟩

  have hParPlane :
      IsParallelogram
        (PlaneGeo Geo pi)
        Ap Bp Cp Dp :=
    ⟨hABCDp, hBCDAP⟩

  have hI34 :=
    euclid_proposition_34
      (Geo := PlaneGeo Geo pi)
      Ap Bp Cp Dp
      hParPlane

  have hSidesPlane :
      OppositeSidesCongruent
        (PlaneGeo Geo pi)
        Ap Bp Cp Dp :=
    hI34.1

  constructor

  · have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi Ap Bp Cp Dp).mp
        hSidesPlane.1
    simpa [Ap, Bp, Cp, Dp] using h

  · have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi Bp Cp Dp Ap).mp
        hSidesPlane.2
    simpa [Ap, Bp, Cp, Dp] using h


/--
For a parallelepipedal configuration, extract the six edge congruences
needed to compare the three faces at B with their three opposite faces.

No global ambient `HilbertOrder Geo` is assumed.
-/
theorem hilbert_XI27_opposite_face_edge_congruences
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt) :
    Geo.Congruent B A F E /\
    Geo.Congruent B C F G /\
    Geo.Congruent B A C D /\
    Geo.Congruent B F C G /\
    Geo.Congruent B C A D /\
    Geo.Congruent B F A E := by

  have hRho0 :
      OppositeSidesCongruent Geo A B F E :=
    hilbert_XI27_face_opposite_sides_congruent
      (Geo := Geo)
      rho0 pi0 pi1 sigma0 sigma1
      A B F E
      hCfg.pi_parallel
      hCfg.sigma_parallel
      hCfg.A_on.2.1
      hCfg.A_on.1
      hCfg.A_on.2.2
      hCfg.B_on.2.1
      hCfg.B_on.1
      hCfg.B_on.2.2
      hCfg.F_on.2.1
      hCfg.F_on.1
      hCfg.F_on.2.2
      hCfg.E_on.2.1
      hCfg.E_on.1
      hCfg.E_on.2.2

  have hSigma0 :
      OppositeSidesCongruent Geo C B F G :=
    hilbert_XI27_face_opposite_sides_congruent
      (Geo := Geo)
      sigma0 pi0 pi1 rho0 rho1
      C B F G
      hCfg.pi_parallel
      hCfg.rho_parallel
      hCfg.C_on.2.2
      hCfg.C_on.1
      hCfg.C_on.2.1
      hCfg.B_on.2.2
      hCfg.B_on.1
      hCfg.B_on.2.1
      hCfg.F_on.2.2
      hCfg.F_on.1
      hCfg.F_on.2.1
      hCfg.G_on.2.2
      hCfg.G_on.1
      hCfg.G_on.2.1

  have hPi0 :
      OppositeSidesCongruent Geo A B C D :=
    hilbert_XI27_face_opposite_sides_congruent
      (Geo := Geo)
      pi0 rho0 rho1 sigma0 sigma1
      A B C D
      hCfg.rho_parallel
      hCfg.sigma_parallel
      hCfg.A_on.1
      hCfg.A_on.2.1
      hCfg.A_on.2.2
      hCfg.B_on.1
      hCfg.B_on.2.1
      hCfg.B_on.2.2
      hCfg.C_on.1
      hCfg.C_on.2.1
      hCfg.C_on.2.2
      hCfg.D_on.1
      hCfg.D_on.2.1
      hCfg.D_on.2.2

  have hBA_FE :
      Geo.Congruent B A F E :=
    CongruentReverseFirst
      Geo A B F E
      hRho0.1

  have hBC_FG :
      Geo.Congruent B C F G :=
    CongruentReverseFirst
      Geo C B F G
      hSigma0.1

  have hBA_CD :
      Geo.Congruent B A C D :=
    CongruentReverseFirst
      Geo A B C D
      hPi0.1

  have hBF_CG :
      Geo.Congruent B F C G := by
    exact
      (Geometry.Geo.congruent_reverse_second
        Geo
        B F
        G C).mp
        hSigma0.2

  have hBC_AD :
      Geo.Congruent B C A D := by
    exact
      (Geometry.Geo.congruent_reverse_second
        Geo
        B C
        D A).mp
        hPi0.2

  have hBF_AE :
      Geo.Congruent B F A E := by
    exact
      (Geometry.Geo.congruent_reverse_second
        Geo
        B F
        E A).mp
        hRho0.2

  exact
    ⟨hBA_FE,
     hBC_FG,
     hBA_CD,
     hBF_CG,
     hBC_AD,
     hBF_AE⟩


/--
A parallelogram proved inside a carrier plane supplies the directed
spatial parallel data for one pair of opposite sides.

No global ambient `HilbertOrder Geo` is used.
-/
theorem hilbert_XI27_plane_parallelogram_directed_opposite_sides
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hCpi : S.OnPlane C pi)
    (hDpi : S.OnPlane D pi)
    (hPar :
      IsParallelogram
        (PlaneGeo Geo pi)
        (show PlanePoint Geo pi from ⟨A, hApi⟩)
        (show PlanePoint Geo pi from ⟨B, hBpi⟩)
        (show PlanePoint Geo pi from ⟨C, hCpi⟩)
        (show PlanePoint Geo pi from ⟨D, hDpi⟩)) :
    HilbertSpaceDirectedParallelSegments Geo A B D C := by

  let Ap : PlanePoint Geo pi := ⟨A, hApi⟩
  let Bp : PlanePoint Geo pi := ⟨B, hBpi⟩
  let Cp : PlanePoint Geo pi := ⟨C, hCpi⟩
  let Dp : PlanePoint Geo pi := ⟨D, hDpi⟩

  have hPar' :
      IsParallelogram (PlaneGeo Geo pi) Ap Bp Cp Dp := by
    simpa [Ap, Bp, Cp, Dp] using hPar

  have hAB_DC :
      (PlaneGeo Geo pi).Parallel Ap Bp Dp Cp :=
    ParallelSwapSecondLine
      (PlaneGeo Geo pi)
      Ap Bp Cp Dp
      hPar'.1

  have hDA_BC :
      (PlaneGeo Geo pi).Parallel Dp Ap Bp Cp :=
    ParallelSymmetry
      (PlaneGeo Geo pi)
      Bp Cp Dp Ap
      hPar'.2

  have hABp : Ne Ap Bp := hAB_DC.1
  have hDCp : Ne Dp Cp := hAB_DC.2.1
  have hDAp : Ne Dp Ap := hDA_BC.1
  have hBCp : Ne Bp Cp := hDA_BC.2.1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo pi)
        Ap Bp hABp
    with
    ⟨lp, hAlp, hBlp⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo pi)
        Dp Cp hDCp
    with
    ⟨mp, hDmp, hCmp⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo pi)
        Bp Cp hBCp
    with
    ⟨tp, hBtp, hCtp⟩

  have hDisLMplane :
      HilbertLinesDisjoint (PlaneGeo Geo pi) lp mp := by
    intro hMeet
    rcases hMeet with ⟨Xp, hXlp, hXmp⟩

    have hXAB :
        Xp ∈ (PlaneGeo Geo pi).PointLine Ap Bp :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo pi)
        Ap Bp Xp lp
        hABp hAlp hBlp).mpr
        hXlp

    have hXDC :
        Xp ∈ (PlaneGeo Geo pi).PointLine Dp Cp :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo pi)
        Dp Cp Xp mp
        hDCp hDmp hCmp).mpr
        hXmp

    exact
      Set.disjoint_left.mp
        hAB_DC.2.2
        hXAB hXDC

  have hDisLM :
      HilbertLinesDisjoint Geo lp.1 mp.1 := by
    intro hMeet
    rcases hMeet with ⟨X, hXl, hXm⟩

    have hXpi :
        S.OnPlane X pi :=
      lp.2 X hXl

    let Xp : PlanePoint Geo pi := ⟨X, hXpi⟩

    exact
      hDisLMplane
        ⟨Xp, hXl, hXm⟩

  have hSameADplane :
      HilbertSameSide
        (PlaneGeo Geo pi)
        Ap Dp tp := by

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Dp Ap hDAp
      with
      ⟨rp, hDrp, hArp⟩

    have hAoffT :
        Not ((PlaneGeo Geo pi).OnLine Ap tp) := by
      intro hAt

      have hADA :
          Ap ∈ (PlaneGeo Geo pi).PointLine Dp Ap :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Dp Ap Ap rp
          hDAp hDrp hArp).mpr
          hArp

      have hABC :
          Ap ∈ (PlaneGeo Geo pi).PointLine Bp Cp :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Bp Cp Ap tp
          hBCp hBtp hCtp).mpr
          hAt

      exact
        Set.disjoint_left.mp
          hDA_BC.2.2
          hADA hABC

    have hDoffT :
        Not ((PlaneGeo Geo pi).OnLine Dp tp) := by
      intro hDt

      have hDDA :
          Dp ∈ (PlaneGeo Geo pi).PointLine Dp Ap :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Dp Ap Dp rp
          hDAp hDrp hArp).mpr
          hDrp

      have hDBC :
          Dp ∈ (PlaneGeo Geo pi).PointLine Bp Cp :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Bp Cp Dp tp
          hBCp hBtp hCtp).mpr
          hDt

      exact
        Set.disjoint_left.mp
          hDA_BC.2.2
          hDDA hDBC

    have hNoMeet :
        Not
          (HilbertSegmentMeetsLine
            (PlaneGeo Geo pi)
            Ap Dp tp) := by
      intro hMeet
      rcases hMeet with ⟨Xp, hAXD, hXt⟩

      have hXr :
          (PlaneGeo Geo pi).OnLine Xp rp :=
        hilbert_between_on_line
          (PlaneGeo Geo pi)
          Ap Xp Dp rp
          hArp hDrp hAXD

      have hXDA :
          Xp ∈ (PlaneGeo Geo pi).PointLine Dp Ap :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Dp Ap Xp rp
          hDAp hDrp hArp).mpr
          hXr

      have hXBC :
          Xp ∈ (PlaneGeo Geo pi).PointLine Bp Cp :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Bp Cp Xp tp
          hBCp hBtp hCtp).mpr
          hXt

      exact
        Set.disjoint_left.mp
          hDA_BC.2.2
          hXDA hXBC

    exact
      ⟨hAoffT,
       hDoffT,
       Relation.ReflTransGen.single
         ⟨hAoffT, hDoffT, hNoMeet⟩⟩

  have hSameADspace :
      HilbertSameSideInPlane
        Geo A D tp.1 pi := by
    have h :=
      (planeGeo_sameSide_iff_space
        (Geo := Geo)
        pi Ap Dp tp).mp
        hSameADplane
    simpa [Ap, Dp] using h

  exact
    ⟨pi,
     lp.1,
     mp.1,
     tp.1,
     hAlp,
     hBlp,
     hDmp,
     hCmp,
     lp.2,
     mp.2,
     hDisLM,
     hBtp,
     hCtp,
     tp.2,
     hSameADspace⟩


/--
One opposite-face angle comparison for XI.27, obtained without a global
ambient `HilbertOrder Geo`.

For the opposite faces pi0 = ABCD and pi1 = EFGH, prove

    angle ABC ~= angle EFG.

The directed-parallel data are extracted from the side faces rho0 and sigma0,
with all planar order confined to their PlaneGeo slices.
-/
theorem hilbert_XI27_opposite_pi_face_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt) :
    Geo.AngleCongruent A B C E F G := by

  ------------------------------------------------------------
  -- Side face rho0 = A B F E as a PlaneGeo parallelogram.
  ------------------------------------------------------------

  have hRho0Sides :
      OppositeSidesCongruent Geo A B F E :=
    hilbert_XI27_face_opposite_sides_congruent
      (Geo := Geo)
      rho0 pi0 pi1 sigma0 sigma1
      A B F E
      hCfg.pi_parallel
      hCfg.sigma_parallel
      hCfg.A_on.2.1
      hCfg.A_on.1
      hCfg.A_on.2.2
      hCfg.B_on.2.1
      hCfg.B_on.1
      hCfg.B_on.2.2
      hCfg.F_on.2.1
      hCfg.F_on.1
      hCfg.F_on.2.2
      hCfg.E_on.2.1
      hCfg.E_on.1
      hCfg.E_on.2.2

  -- Rebuild the rho0 parallelogram in PlaneGeo by using the same helper
  -- pattern through opposite-side congruence's geometric source.
  let Ar : PlanePoint Geo rho0 := ⟨A, hCfg.A_on.2.1⟩
  let Br : PlanePoint Geo rho0 := ⟨B, hCfg.B_on.2.1⟩
  let Fr : PlanePoint Geo rho0 := ⟨F, hCfg.F_on.2.1⟩
  let Er : PlanePoint Geo rho0 := ⟨E, hCfg.E_on.2.1⟩

  -- Obtain rho0 parallel side pairs directly from XI.16.
  have hAB : Ne A B := by
    intro hEq
    subst B
    exact hCfg.sigma_parallel
      ⟨A, hCfg.B_on.2.2, hCfg.A_on.2.2⟩

  have hFE : Ne F E := by
    intro hEq
    subst E
    exact hCfg.sigma_parallel
      ⟨F, hCfg.F_on.2.2, hCfg.E_on.2.2⟩

  have hBF : Ne B F := by
    intro hEq
    subst F
    exact hCfg.pi_parallel
      ⟨B, hCfg.B_on.1, hCfg.F_on.1⟩

  have hEA : Ne E A := by
    intro hEq
    subst A
    exact hCfg.pi_parallel
      ⟨E, hCfg.A_on.1, hCfg.E_on.1⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        pi0 pi1 rho0
        A E
        hCfg.pi_parallel
        hCfg.A_on.1 hCfg.A_on.2.1
        hCfg.E_on.1 hCfg.E_on.2.1
    with
    ⟨lAB, lEF, hAlAB, hElEF, hPi0Iff, hPi1Iff, hParAB_EF⟩

  have hBlAB : H.OnLine B lAB :=
    (hPi0Iff B).mp ⟨hCfg.B_on.1, hCfg.B_on.2.1⟩

  have hFlEF : H.OnLine F lEF :=
    (hPi1Iff F).mp ⟨hCfg.F_on.1, hCfg.F_on.2.1⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        sigma0 sigma1 rho0
        B A
        hCfg.sigma_parallel
        hCfg.B_on.2.2 hCfg.B_on.2.1
        hCfg.A_on.2.2 hCfg.A_on.2.1
    with
    ⟨lBF, lEA, hBlBF, hAlEA, hSigma0Iff, hSigma1Iff, hParBF_EA⟩

  have hFlBF : H.OnLine F lBF :=
    (hSigma0Iff F).mp ⟨hCfg.F_on.2.2, hCfg.F_on.2.1⟩

  have hElEA : H.OnLine E lEA :=
    (hSigma1Iff E).mp ⟨hCfg.E_on.2.2, hCfg.E_on.2.1⟩

  have hABr : Ne Ar Br := by
    intro h
    apply hAB
    exact congrArg Subtype.val h

  have hFEr : Ne Fr Er := by
    intro h
    apply hFE
    exact congrArg Subtype.val h

  have hBFr : Ne Br Fr := by
    intro h
    apply hBF
    exact congrArg Subtype.val h

  have hEAr : Ne Er Ar := by
    intro h
    apply hEA
    exact congrArg Subtype.val h

  let lpAB : PlaneLine Geo rho0 :=
    ⟨lAB,
     HSI.line_in_plane
       A B hAB
       lAB hAlAB hBlAB
       rho0 hCfg.A_on.2.1 hCfg.B_on.2.1⟩

  let lpEF : PlaneLine Geo rho0 :=
    ⟨lEF,
     HSI.line_in_plane
       E F hFE.symm
       lEF hElEF hFlEF
       rho0 hCfg.E_on.2.1 hCfg.F_on.2.1⟩

  let lpBF : PlaneLine Geo rho0 :=
    ⟨lBF,
     HSI.line_in_plane
       B F hBF
       lBF hBlBF hFlBF
       rho0 hCfg.B_on.2.1 hCfg.F_on.2.1⟩

  let lpEA : PlaneLine Geo rho0 :=
    ⟨lEA,
     HSI.line_in_plane
       E A hEA
       lEA hElEA hAlEA
       rho0 hCfg.E_on.2.1 hCfg.A_on.2.1⟩

  have hParAB_EF_plane :
      (PlaneGeo Geo rho0).Parallel Ar Br Er Fr := by
    refine ⟨hABr, ?_⟩
    refine ⟨?_, ?_⟩
    · exact hFEr.symm
    · apply Set.disjoint_left.mpr
      intro X hXAB hXEF

      have hXlAB :
          (PlaneGeo Geo rho0).OnLine X lpAB :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo rho0)
          Ar Br X lpAB
          hABr hAlAB hBlAB).mp hXAB

      have hXlEF :
          (PlaneGeo Geo rho0).OnLine X lpEF :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo rho0)
          Er Fr X lpEF
          hFEr.symm hElEF hFlEF).mp hXEF

      rcases hParAB_EF with
        ⟨_omega, _hl, _hm, hDis⟩

      exact hDis ⟨X.1, hXlAB, hXlEF⟩

  have hParBF_EA_plane :
      (PlaneGeo Geo rho0).Parallel Br Fr Er Ar := by
    refine ⟨hBFr, hEAr, ?_⟩
    apply Set.disjoint_left.mpr
    intro X hXBF hXEA

    have hXlBF :
        (PlaneGeo Geo rho0).OnLine X lpBF :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo rho0)
        Br Fr X lpBF
        hBFr hBlBF hFlBF).mp hXBF

    have hXlEA :
        (PlaneGeo Geo rho0).OnLine X lpEA :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo rho0)
        Er Ar X lpEA
        hEAr hElEA hAlEA).mp hXEA

    rcases hParBF_EA with
      ⟨_omega, _hl, _hm, hDis⟩

    exact hDis ⟨X.1, hXlBF, hXlEA⟩

  have hParAB_FE_plane :
      (PlaneGeo Geo rho0).Parallel Ar Br Fr Er :=
    ParallelSwapSecondLine
      (PlaneGeo Geo rho0)
      Ar Br Er Fr
      hParAB_EF_plane

  have hRho0Par :
      IsParallelogram
        (PlaneGeo Geo rho0)
        Ar Br Fr Er :=
    ⟨hParAB_FE_plane, hParBF_EA_plane⟩

  have hDirAB_EF :
      HilbertSpaceDirectedParallelSegments
        Geo A B E F :=
    hilbert_XI27_plane_parallelogram_directed_opposite_sides
      (Geo := Geo)
      rho0
      A B F E
      hCfg.A_on.2.1
      hCfg.B_on.2.1
      hCfg.F_on.2.1
      hCfg.E_on.2.1
      hRho0Par

  ------------------------------------------------------------
  -- Side face sigma0 = C B F G.
  ------------------------------------------------------------

  have hCB : Ne C B := hAB |> fun _ => by
    intro hEq
    subst C
    exact hCfg.rho_parallel
      ⟨B, hCfg.B_on.2.1, hCfg.C_on.2.1⟩

  have hGF : Ne G F := by
    intro hEq
    subst G
    exact hCfg.rho_parallel
      ⟨F, hCfg.F_on.2.1, hCfg.G_on.2.1⟩

  have hCG : Ne C G := by
    intro hEq
    subst G
    exact hCfg.pi_parallel
      ⟨C, hCfg.C_on.1, hCfg.G_on.1⟩

  let Cs : PlanePoint Geo sigma0 := ⟨C, hCfg.C_on.2.2⟩
  let Bs : PlanePoint Geo sigma0 := ⟨B, hCfg.B_on.2.2⟩
  let Fs : PlanePoint Geo sigma0 := ⟨F, hCfg.F_on.2.2⟩
  let Gs : PlanePoint Geo sigma0 := ⟨G, hCfg.G_on.2.2⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        pi0 pi1 sigma0
        C G
        hCfg.pi_parallel
        hCfg.C_on.1 hCfg.C_on.2.2
        hCfg.G_on.1 hCfg.G_on.2.2
    with
    ⟨lCB, lGF, hClCB, hGlGF, hPi0Iff2, hPi1Iff2, hParCB_GF⟩

  have hBlCB : H.OnLine B lCB :=
    (hPi0Iff2 B).mp ⟨hCfg.B_on.1, hCfg.B_on.2.2⟩

  have hFlGF : H.OnLine F lGF :=
    (hPi1Iff2 F).mp ⟨hCfg.F_on.1, hCfg.F_on.2.2⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        rho0 rho1 sigma0
        B C
        hCfg.rho_parallel
        hCfg.B_on.2.1 hCfg.B_on.2.2
        hCfg.C_on.2.1 hCfg.C_on.2.2
    with
    ⟨lBF2, lCG, hBlBF2, hClCG, hRho0Iff2, hRho1Iff2, hParBF_CG⟩

  have hFlBF2 : H.OnLine F lBF2 :=
    (hRho0Iff2 F).mp ⟨hCfg.F_on.2.1, hCfg.F_on.2.2⟩

  have hGlCG : H.OnLine G lCG :=
    (hRho1Iff2 G).mp ⟨hCfg.G_on.2.1, hCfg.G_on.2.2⟩

  let lpCB : PlaneLine Geo sigma0 :=
    ⟨lCB,
     HSI.line_in_plane
       C B hCB
       lCB hClCB hBlCB
       sigma0 hCfg.C_on.2.2 hCfg.B_on.2.2⟩

  let lpGF : PlaneLine Geo sigma0 :=
    ⟨lGF,
     HSI.line_in_plane
       G F hGF
       lGF hGlGF hFlGF
       sigma0 hCfg.G_on.2.2 hCfg.F_on.2.2⟩

  let lpBF2 : PlaneLine Geo sigma0 :=
    ⟨lBF2,
     HSI.line_in_plane
       B F hBF
       lBF2 hBlBF2 hFlBF2
       sigma0 hCfg.B_on.2.2 hCfg.F_on.2.2⟩

  let lpCG : PlaneLine Geo sigma0 :=
    ⟨lCG,
     HSI.line_in_plane
       C G hCG
       lCG hClCG hGlCG
       sigma0 hCfg.C_on.2.2 hCfg.G_on.2.2⟩

  have hCBs : Ne Cs Bs := by
    intro h
    apply hCB
    exact congrArg Subtype.val h

  have hGFs : Ne Gs Fs := by
    intro h
    apply hGF
    exact congrArg Subtype.val h

  have hBFs : Ne Bs Fs := by
    intro h
    apply hBF
    exact congrArg Subtype.val h

  have hCGs : Ne Cs Gs := by
    intro h
    apply hCG
    exact congrArg Subtype.val h

  have hParCB_GF_plane :
      (PlaneGeo Geo sigma0).Parallel Cs Bs Gs Fs := by
    refine ⟨hCBs, hGFs, ?_⟩
    apply Set.disjoint_left.mpr
    intro X hXCB hXGF
    have hX1 :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo sigma0)
        Cs Bs X lpCB hCBs hClCB hBlCB).mp hXCB
    have hX2 :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo sigma0)
        Gs Fs X lpGF hGFs hGlGF hFlGF).mp hXGF
    rcases hParCB_GF with ⟨_o, _h1, _h2, hDis⟩
    exact hDis ⟨X.1, hX1, hX2⟩

  have hParBF_CG_plane :
      (PlaneGeo Geo sigma0).Parallel Bs Fs Gs Cs := by
    refine ⟨hBFs, hCGs.symm, ?_⟩
    apply Set.disjoint_left.mpr
    intro X hXBF hXGC
    have hX1 :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo sigma0)
        Bs Fs X lpBF2 hBFs hBlBF2 hFlBF2).mp hXBF
    have hX2 :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo sigma0)
        Gs Cs X lpCG hCGs.symm hGlCG hClCG).mp hXGC
    rcases hParBF_CG with ⟨_o, _h1, _h2, hDis⟩
    exact hDis ⟨X.1, hX1, hX2⟩

  have hParCB_FG_plane :
      (PlaneGeo Geo sigma0).Parallel Cs Bs Fs Gs :=
    ParallelSwapSecondLine
      (PlaneGeo Geo sigma0)
      Cs Bs Gs Fs
      hParCB_GF_plane

  have hSigma0Par :
      IsParallelogram
        (PlaneGeo Geo sigma0)
        Cs Bs Fs Gs :=
    ⟨hParCB_FG_plane, hParBF_CG_plane⟩

  have hDirCB_GF :
      HilbertSpaceDirectedParallelSegments
        Geo C B G F :=
    hilbert_XI27_plane_parallelogram_directed_opposite_sides
      (Geo := Geo)
      sigma0
      C B F G
      hCfg.C_on.2.2
      hCfg.B_on.2.2
      hCfg.F_on.2.2
      hCfg.G_on.2.2
      hSigma0Par

  ------------------------------------------------------------
  -- XI.10 side conditions.
  ------------------------------------------------------------

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    (hilbertParallelepipedConfiguration_trihedral_at_B
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt hCfg).1

  have hEFG :
      Not (PrimCollinear Geo E F G) := by
    have hTriF :=
      hilbertParallelepipedConfiguration_trihedral_at_B
        (Geo := Geo)
        pi1 pi0 rho0 rho1 sigma0 sigma1
        E F G Hpt A B C D
        {
          pi_parallel := by
            intro h
            exact hCfg.pi_parallel ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩
          rho_parallel := hCfg.rho_parallel
          sigma_parallel := hCfg.sigma_parallel
          A_on := hCfg.E_on
          B_on := hCfg.F_on
          C_on := hCfg.G_on
          D_on := hCfg.H_on
          E_on := hCfg.A_on
          F_on := hCfg.B_on
          G_on := hCfg.C_on
          H_on := hCfg.D_on
        }
    exact hTriF.1

  have hNoCommonPlane :
      Not (exists omega : S.Plane,
        S.OnPlane A omega /\
        S.OnPlane B omega /\
        S.OnPlane C omega /\
        S.OnPlane E omega /\
        S.OnPlane F omega /\
        S.OnPlane G omega) := by
    intro h
    rcases h with
      ⟨omega, hA, hB, hC, hE, hF, hG⟩

    have hABC' :
        Not (PrimCollinear Geo A B C) :=
      hABC

    have hOmegaPi0 :
        omega = pi0 :=
      HSI.plane_unique
        A B C
        hABC'
        omega pi0
        hA hB hC
        hCfg.A_on.1
        hCfg.B_on.1
        hCfg.C_on.1

    have hEpi0 :
        S.OnPlane E pi0 := by
      exact hOmegaPi0 ▸ hE

    exact hCfg.pi_parallel
      ⟨E, hEpi0, hCfg.E_on.1⟩

  exact
    euclid_proposition_11_10
      (Geo := Geo)
      A B C
      E F G
      hDirAB_EF
      hDirCB_GF
      hABC
      hEFG
      hNoCommonPlane


/--
All three opposite-face included-angle congruences for a parallelepipedal
configuration, obtained by reusing the pi-face theorem under cyclic
permutations of the three plane directions.
-/
theorem hilbert_XI27_all_opposite_face_angles
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt) :
    Geo.AngleCongruent A B C E F G /\
    Geo.AngleCongruent A B F D C G /\
    Geo.AngleCongruent C B F D A E := by

  have hPi :
      Geo.AngleCongruent A B C E F G :=
    hilbert_XI27_opposite_pi_face_angle
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hCfgRho :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        rho0 rho1
        pi0 pi1
        sigma0 sigma1
        A B F E
        D C G Hpt := by
    exact
      {
        pi_parallel := hCfg.rho_parallel
        rho_parallel := hCfg.pi_parallel
        sigma_parallel := hCfg.sigma_parallel

        A_on := ⟨hCfg.A_on.2.1,
                 hCfg.A_on.1,
                 hCfg.A_on.2.2⟩

        B_on := ⟨hCfg.B_on.2.1,
                 hCfg.B_on.1,
                 hCfg.B_on.2.2⟩

        C_on := ⟨hCfg.F_on.2.1,
                 hCfg.F_on.1,
                 hCfg.F_on.2.2⟩

        D_on := ⟨hCfg.E_on.2.1,
                 hCfg.E_on.1,
                 hCfg.E_on.2.2⟩

        E_on := ⟨hCfg.D_on.2.1,
                 hCfg.D_on.1,
                 hCfg.D_on.2.2⟩

        F_on := ⟨hCfg.C_on.2.1,
                 hCfg.C_on.1,
                 hCfg.C_on.2.2⟩

        G_on := ⟨hCfg.G_on.2.1,
                 hCfg.G_on.1,
                 hCfg.G_on.2.2⟩

        H_on := ⟨hCfg.H_on.2.1,
                 hCfg.H_on.1,
                 hCfg.H_on.2.2⟩
      }

  have hRho :
      Geo.AngleCongruent A B F D C G :=
    hilbert_XI27_opposite_pi_face_angle
      (Geo := Geo)
      rho0 rho1
      pi0 pi1
      sigma0 sigma1
      A B F E
      D C G Hpt
      hCfgRho

  have hCfgSigma :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        sigma0 sigma1
        pi0 pi1
        rho0 rho1
        C B F G
        D A E Hpt := by
    exact
      {
        pi_parallel := hCfg.sigma_parallel
        rho_parallel := hCfg.pi_parallel
        sigma_parallel := hCfg.rho_parallel

        A_on := ⟨hCfg.C_on.2.2,
                 hCfg.C_on.1,
                 hCfg.C_on.2.1⟩

        B_on := ⟨hCfg.B_on.2.2,
                 hCfg.B_on.1,
                 hCfg.B_on.2.1⟩

        C_on := ⟨hCfg.F_on.2.2,
                 hCfg.F_on.1,
                 hCfg.F_on.2.1⟩

        D_on := ⟨hCfg.G_on.2.2,
                 hCfg.G_on.1,
                 hCfg.G_on.2.1⟩

        E_on := ⟨hCfg.D_on.2.2,
                 hCfg.D_on.1,
                 hCfg.D_on.2.1⟩

        F_on := ⟨hCfg.A_on.2.2,
                 hCfg.A_on.1,
                 hCfg.A_on.2.1⟩

        G_on := ⟨hCfg.E_on.2.2,
                 hCfg.E_on.1,
                 hCfg.E_on.2.1⟩

        H_on := ⟨hCfg.H_on.2.2,
                 hCfg.H_on.1,
                 hCfg.H_on.2.1⟩
      }

  have hSigma :
      Geo.AngleCongruent C B F D A E :=
    hilbert_XI27_opposite_pi_face_angle
      (Geo := Geo)
      sigma0 sigma1
      pi0 pi1
      rho0 rho1
      C B F G
      D A E Hpt
      hCfgSigma

  exact ⟨hPi, hRho, hSigma⟩


/--
If the three faces adjacent to the distinguished corner of two
parallelepipeds are similar, then the three opposite faces are similar.

The proof uses only:
* opposite-edge congruences in each solid;
* opposite-face angle congruences in each solid;
* transport of `HilbertSpaceFaceCornerSimilar`.
-/
theorem hilbert_XI27_three_opposite_faces_similar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)

    (pi0' pi1' rho0' rho1' sigma0' sigma1' : S.Plane)
    (A' B' C' D' E' F' G' H' : Geo.Point)
    (hCfg' :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0' pi1' rho0' rho1' sigma0' sigma1'
        A' B' C' D' E' F' G' H')

    (hPi0 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B C
        A' B' C')
    (hRho0 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B F
        A' B' F')
    (hSigma0 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        C B F
        C' B' F') :
    HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        E F G
        E' F' G' /\
    HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        D C G
        D' C' G' /\
    HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        D A E
        D' A' E' := by

  have hEdges :=
    hilbert_XI27_opposite_face_edge_congruences
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hEdges' :=
    hilbert_XI27_opposite_face_edge_congruences
      (Geo := Geo)
      pi0' pi1' rho0' rho1' sigma0' sigma1'
      A' B' C' D' E' F' G' H'
      hCfg'

  have hAngles :=
    hilbert_XI27_all_opposite_face_angles
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hAngles' :=
    hilbert_XI27_all_opposite_face_angles
      (Geo := Geo)
      pi0' pi1' rho0' rho1' sigma0' sigma1'
      A' B' C' D' E' F' G' H'
      hCfg'

  have hPi1 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        E F G
        E' F' G' := by
    exact
      hilbertSpaceFaceCornerSimilar_transport
        (Geo := Geo)
        A B C
        A' B' C'
        E F G
        E' F' G'
        hPi0
        hEdges.1
        hEdges.2.1
        hEdges'.1
        hEdges'.2.1
        (Geometry.Geo.angle_congruent_symmetry
          Geo
          A B C
          E F G
          hAngles.1)
        hAngles'.1

  have hRho1 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        D C G
        D' C' G' := by
    exact
      hilbertSpaceFaceCornerSimilar_transport
        (Geo := Geo)
        A B F
        A' B' F'
        D C G
        D' C' G'
        hRho0
        hEdges.2.2.1
        hEdges.2.2.2.1
        hEdges'.2.2.1
        hEdges'.2.2.2.1
        (Geometry.Geo.angle_congruent_symmetry
          Geo
          A B F
          D C G
          hAngles.2.1)
        hAngles'.2.1

  have hSigma1 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        D A E
        D' A' E' := by
    exact
      hilbertSpaceFaceCornerSimilar_transport
        (Geo := Geo)
        C B F
        C' B' F'
        D A E
        D' A' E'
        hSigma0
        hEdges.2.2.2.2.1
        hEdges.2.2.2.2.2
        hEdges'.2.2.2.2.1
        hEdges'.2.2.2.2.2
        (Geometry.Geo.angle_congruent_symmetry
          Geo
          C B F
          D A E
          hAngles.2.2)
        hAngles'.2.2

  exact
    ⟨hPi1,
     hRho1,
     hSigma1⟩


/--
A face represented by one distinguished corner and its two adjacent
vertices.  This is the exact face data consumed by the XI.27 similarity
criterion.
-/
structure HilbertSpaceFaceCorner
    (Geo : Geometry.Geo) where
  a : Geo.Point
  b : Geo.Point
  c : Geo.Point

/--
Similarity relation on corner-represented faces.
-/
def HilbertSpaceFaceCornerSimilarFace
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P Q : HilbertSpaceFaceCorner Geo) : Prop :=
  HilbertSpaceFaceCornerSimilar
    (Geo := Geo)
    P.a P.b P.c
    Q.a Q.b Q.c

/--
The six canonically indexed face corners of a parallelepiped.

The selected corners agree with the face order used throughout XI.24/XI.27:
  pi0    : A-B-C
  pi1    : E-F-G
  rho0   : A-B-F
  rho1   : D-C-G
  sigma0 : C-B-F
  sigma1 : D-A-E
-/
def hilbertXI27FaceCorners
    (A B C D E F G _Hpt : Geo.Point) :
    HilbertParallelepipedFaces
      (HilbertSpaceFaceCorner Geo) :=
  {
    pi0 := ⟨A, B, C⟩
    pi1 := ⟨E, F, G⟩
    rho0 := ⟨A, B, F⟩
    rho1 := ⟨D, C, G⟩
    sigma0 := ⟨C, B, F⟩
    sigma1 := ⟨D, A, E⟩
  }

/--
XI.Def.9 packaging theorem for two parallelepipedal configurations.

Three adjacent face-corner similarities imply similarity of all six
corresponding faces.
-/
theorem hilbert_XI27_XI9_packaging
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]

    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)

    (pi0' pi1' rho0' rho1' sigma0' sigma1' : S.Plane)
    (A' B' C' D' E' F' G' H' : Geo.Point)
    (hCfg' :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0' pi1' rho0' rho1' sigma0' sigma1'
        A' B' C' D' E' F' G' H')

    (hPi0 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B C
        A' B' C')
    (hRho0 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        A B F
        A' B' F')
    (hSigma0 :
      HilbertSpaceFaceCornerSimilar
        (Geo := Geo)
        C B F
        C' B' F') :
    HilbertXI9SimilarParallelepiped
      (HilbertSpaceFaceCornerSimilarFace
        (Geo := Geo))
      (hilbertXI27FaceCorners
        (Geo := Geo)
        A B C D E F G Hpt)
      (hilbertXI27FaceCorners
        (Geo := Geo)
        A' B' C' D' E' F' G' H') := by

  have hOpp :=
    hilbert_XI27_three_opposite_faces_similar
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt hCfg
      pi0' pi1' rho0' rho1' sigma0' sigma1'
      A' B' C' D' E' F' G' H' hCfg'
      hPi0 hRho0 hSigma0

  apply
    hilbertXI9SimilarParallelepiped_intro
      (HilbertSpaceFaceCornerSimilarFace
        (Geo := Geo))
      (hilbertXI27FaceCorners
        (Geo := Geo)
        A B C D E F G Hpt)
      (hilbertXI27FaceCorners
        (Geo := Geo)
        A' B' C' D' E' F' G' H')

  · exact hPi0
  · exact hOpp.1
  · exact hRho0
  · exact hOpp.2.1
  · exact hSigma0
  · exact hOpp.2.2


/--
Euclid XI.27, production-shaped integration test.

Given a source parallelepiped and a prescribed nondegenerate target edge
A0B0, construct a target parallelepiped whose six corresponding faces are
similar in the sense of Euclid XI.Def.9, represented by the checked
face-corner similarity relation.
-/
theorem euclid_proposition_11_27
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)
    (A0 B0 : Geo.Point)
    (hA0B0 : Ne A0 B0) :
    exists K J : Geo.Point,
    exists tpi0 tpi1 trho0 trho1 tsigma0 tsigma1 : S.Plane,
    exists TD TE TG TH : Geo.Point,
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        tpi0 tpi1 trho0 trho1 tsigma0 tsigma1
        B0 A0 K TD TE J TG TH /\
      HilbertXI9SimilarParallelepiped
        (HilbertSpaceFaceCornerSimilarFace
          (Geo := Geo))
        (hilbertXI27FaceCorners
          (Geo := Geo)
          A B C D E F G Hpt)
        (hilbertXI27FaceCorners
          (Geo := Geo)
          B0 A0 K TD TE J TG TH) := by

  rcases
      hilbert_XI27_scaled_shell_exists_of_crossing
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt
        hCfg
        A0 B0
        hA0B0
    with
    ⟨K, J, hA0K, hA0J,
     hTri,
     hAngPi,
     hAngSigma,
     hAngRho,
     hPropPi,
     hPropSigma,
     hPropRho,
     tpi0, tpi1, trho0, trho1, tsigma0, tsigma1,
     TD, TE, TG, TH,
     hTargetCfg⟩

  have hThree :
      HilbertSpaceFaceCornerSimilar
          (Geo := Geo)
          A B C
          B0 A0 K /\
      HilbertSpaceFaceCornerSimilar
          (Geo := Geo)
          C B F
          K A0 J /\
      HilbertSpaceFaceCornerSimilar
          (Geo := Geo)
          A B F
          B0 A0 J :=
    hilbert_XI27_three_adjacent_face_corners_similar
      (Geo := Geo)
      A B C F
      A0 B0 K J
      hAngPi
      hAngSigma
      hAngRho
      hPropPi
      hPropSigma
      hPropRho

  have hXI9 :
      HilbertXI9SimilarParallelepiped
        (HilbertSpaceFaceCornerSimilarFace
          (Geo := Geo))
        (hilbertXI27FaceCorners
          (Geo := Geo)
          A B C D E F G Hpt)
        (hilbertXI27FaceCorners
          (Geo := Geo)
          B0 A0 K TD TE J TG TH) :=
    hilbert_XI27_XI9_packaging
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg
      tpi0 tpi1 trho0 trho1 tsigma0 tsigma1
      B0 A0 K TD TE J TG TH
      hTargetCfg
      hThree.1
      hThree.2.2
      hThree.2.1

  exact
    ⟨K, J,
     tpi0, tpi1, trho0, trho1, tsigma0, tsigma1,
     TD, TE, TG, TH,
     hTargetCfg,
     hXI9⟩
/- END final XI.27 proposition -/

end Geometry

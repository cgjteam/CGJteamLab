import CGJteamLab.Proposition11_24
import CGJteamLab.Wyler.Proposition11_16
import CGJteamLab.Hilbert3DRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.24 - Hilbert-Wyler route

Production Hilbert-Wyler realization of Euclid XI.24.

Architecture:

1. The neutral parallelepiped configuration and final conclusion are
   shared with the canonical XI.24 development.
2. Each face is proved to be a parallelogram through
   `euclid_proposition_11_16_wyler`.
3. The Wyler XI.16 carrier equalities are used explicitly to recover the
   remaining endpoint incidences on the section lines.
4. Once the six face parallelograms have been obtained, the metric part
   is shared with the direct proof:
   I.34, the directed-opposite-side bridge, XI.10, and spatial SAS.
5. The three pairs of opposite faces are obtained from one pair by
   permutation of the three parallel-plane directions.

Thus the Wyler path differs genuinely in the incidence construction,
while reusing proposition-independent metric infrastructure.

No E4 structure is used.
-/

/-!
# Euclid XI.24 - Wyler face lemma

One face of a parallelepiped from two Wyler XI.16 section arguments.

The carrier plane is `pi`. The four vertices are

    A : pi, rho0, sigma1
    B : pi, rho0, sigma0
    C : pi, rho1, sigma0
    D : pi, rho1, sigma1

with

    rho0   || rho1
    sigma0 || sigma1.

Wyler XI.16 gives exact carrier identities for the two pairs of section
lines. These identities are then used to recover all four endpoint
incidences, after which the two opposite line pairs are converted to the
project's `Geo.Parallel` representation.
-/

theorem hilbert_XI24_face_parallelogram_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D : Geo.Point)
    (hRho :
      HilbertSpacePlanesParallel Geo rho0 rho1)
    (hSigma :
      HilbertSpacePlanesParallel Geo sigma0 sigma1)
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
    IsParallelogram Geo A B C D := by

  have hAB : Ne A B := by
    intro hEq
    subst B
    exact
      hSigma
        (Exists.intro A
          (And.intro hBsigma0 hAsigma1))

  have hCD : Ne C D := by
    intro hEq
    subst D
    exact
      hSigma
        (Exists.intro C
          (And.intro hCsigma0 hDsigma1))

  have hBC : Ne B C := by
    intro hEq
    subst C
    exact
      hRho
        (Exists.intro B
          (And.intro hBrho0 hCrho1))

  have hDA : Ne D A := by
    intro hEq
    subst A
    exact
      hRho
        (Exists.intro D
          (And.intro hArho0 hDrho1))

  have hSec1 :=
    euclid_proposition_11_16_wyler
      (Geo := Geo)
      rho0 rho1 pi
      A C
      hRho
      hArho0 hApi
      hCrho1 hCpi

  choose lAB lCD hAlAB hClCD
    hMeetRho0Pi hMeetRho1Pi hParLines1 using hSec1

  have hBlAB :
      H.OnLine B lAB := by
    change HilbertLineCarrier3D Geo lAB B
    rw [<- hMeetRho0Pi]
    exact And.intro hBrho0 hBpi

  have hDlCD :
      H.OnLine D lCD := by
    change HilbertLineCarrier3D Geo lCD D
    rw [<- hMeetRho1Pi]
    exact And.intro hDrho1 hDpi

  have hAB_CD :
      Geo.Parallel A B C D := by

    choose tau hlABtau hlCDtau hDisjoint using hParLines1

    refine And.intro hAB ?_
    refine And.intro hCD ?_

    apply Set.disjoint_left.mpr
    intro X hXAB hXCD

    have hXlAB :
        H.OnLine X lAB :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B X
        lAB
        hAB
        hAlAB hBlAB).mp
        hXAB

    have hXlCD :
        H.OnLine X lCD :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D X
        lCD
        hCD
        hClCD hDlCD).mp
        hXCD

    exact
      hDisjoint
        (Exists.intro X
          (And.intro hXlAB hXlCD))

  have hSec2 :=
    euclid_proposition_11_16_wyler
      (Geo := Geo)
      sigma0 sigma1 pi
      B A
      hSigma
      hBsigma0 hBpi
      hAsigma1 hApi

  choose lBC lDA hBlBC hAlDA
    hMeetSigma0Pi hMeetSigma1Pi hParLines2 using hSec2

  have hClBC :
      H.OnLine C lBC := by
    change HilbertLineCarrier3D Geo lBC C
    rw [<- hMeetSigma0Pi]
    exact And.intro hCsigma0 hCpi

  have hDlDA :
      H.OnLine D lDA := by
    change HilbertLineCarrier3D Geo lDA D
    rw [<- hMeetSigma1Pi]
    exact And.intro hDsigma1 hDpi

  have hBC_DA :
      Geo.Parallel B C D A := by

    choose tau hlBCtau hlDAtau hDisjoint using hParLines2

    refine And.intro hBC ?_
    refine And.intro hDA ?_

    apply Set.disjoint_left.mpr
    intro X hXBC hXDA

    have hXlBC :
        H.OnLine X lBC :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X
        lBC
        hBC
        hBlBC hClBC).mp
        hXBC

    have hXlDA :
        H.OnLine X lDA :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D A X
        lDA
        hDA
        hDlDA hAlDA).mp
        hXDA

    exact
      hDisjoint
        (Exists.intro X
          (And.intro hXlBC hXlDA))

  exact
    And.intro hAB_CD hBC_DA


/-!
# Euclid XI.24 - Wyler six-face theorem

All six faces are parallelograms, now derived through the Wyler XI.16
carrier proof from test01.

The neutral configuration is reused from the production direct XI.24
file.  Only the proof route to the six face parallelograms is replaced.
-/

theorem hilbert_XI24_all_faces_parallelograms_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt) :
    IsParallelogram Geo A B C D /\
    IsParallelogram Geo E F G Hpt /\
    IsParallelogram Geo A B F E /\
    IsParallelogram Geo D C G Hpt /\
    IsParallelogram Geo C B F G /\
    IsParallelogram Geo D A E Hpt := by

  have hFacePi0 :
      IsParallelogram Geo A B C D :=
    hilbert_XI24_face_parallelogram_wyler
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

  have hFacePi1 :
      IsParallelogram Geo E F G Hpt :=
    hilbert_XI24_face_parallelogram_wyler
      (Geo := Geo)
      pi1 rho0 rho1 sigma0 sigma1
      E F G Hpt
      hCfg.rho_parallel
      hCfg.sigma_parallel
      hCfg.E_on.1
      hCfg.E_on.2.1
      hCfg.E_on.2.2
      hCfg.F_on.1
      hCfg.F_on.2.1
      hCfg.F_on.2.2
      hCfg.G_on.1
      hCfg.G_on.2.1
      hCfg.G_on.2.2
      hCfg.H_on.1
      hCfg.H_on.2.1
      hCfg.H_on.2.2

  have hFaceRho0 :
      IsParallelogram Geo A B F E :=
    hilbert_XI24_face_parallelogram_wyler
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

  have hFaceRho1 :
      IsParallelogram Geo D C G Hpt :=
    hilbert_XI24_face_parallelogram_wyler
      (Geo := Geo)
      rho1 pi0 pi1 sigma0 sigma1
      D C G Hpt
      hCfg.pi_parallel
      hCfg.sigma_parallel
      hCfg.D_on.2.1
      hCfg.D_on.1
      hCfg.D_on.2.2
      hCfg.C_on.2.1
      hCfg.C_on.1
      hCfg.C_on.2.2
      hCfg.G_on.2.1
      hCfg.G_on.1
      hCfg.G_on.2.2
      hCfg.H_on.2.1
      hCfg.H_on.1
      hCfg.H_on.2.2

  have hFaceSigma0 :
      IsParallelogram Geo C B F G :=
    hilbert_XI24_face_parallelogram_wyler
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

  have hFaceSigma1 :
      IsParallelogram Geo D A E Hpt :=
    hilbert_XI24_face_parallelogram_wyler
      (Geo := Geo)
      sigma1 pi0 pi1 rho0 rho1
      D A E Hpt
      hCfg.pi_parallel
      hCfg.rho_parallel
      hCfg.D_on.2.2
      hCfg.D_on.1
      hCfg.D_on.2.1
      hCfg.A_on.2.2
      hCfg.A_on.1
      hCfg.A_on.2.1
      hCfg.E_on.2.2
      hCfg.E_on.1
      hCfg.E_on.2.1
      hCfg.H_on.2.2
      hCfg.H_on.1
      hCfg.H_on.2.1

  exact
    And.intro hFacePi0
      (And.intro hFacePi1
        (And.intro hFaceRho0
          (And.intro hFaceRho1
            (And.intro hFaceSigma0 hFaceSigma1))))


/-!
# Euclid XI.24 - Wyler opposite-face theorem

One pair of opposite faces.

The six face parallelograms come from the Wyler XI.16 carrier route.
The metric part is shared with the direct development:

* I.34 on the two side faces gives the two side congruences;
* the generic parallelogram orientation bridge supplies XI.10 data;
* XI.10 gives the included angle congruence;
* spatial Hilbert SAS gives the diagonal-triangle congruence.

Thus the direct and Wyler proofs share only proposition-independent
metric infrastructure after their distinct incidence constructions.
-/

theorem hilbert_XI24_opposite_pi_faces_triangle_congruent_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
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
    TriangleCongruenceResult
      Geo B A C F E G := by

  have hFaces :=
    hilbert_XI24_all_faces_parallelograms_wyler
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hFacePi0 :
      IsParallelogram Geo A B C D :=
    hFaces.1

  have hFacePi1 :
      IsParallelogram Geo E F G Hpt :=
    hFaces.2.1

  have hFaceRho0 :
      IsParallelogram Geo A B F E :=
    hFaces.2.2.1

  have hFaceSigma0 :
      IsParallelogram Geo C B F G :=
    hFaces.2.2.2.2.1

  --------------------------------------------------------------------
  -- I.34 on the two side faces.
  --------------------------------------------------------------------

  have hSidesRho0 :=
    hilbert_XI24_face_opposite_sides_congruent
      (Geo := Geo)
      rho0
      A B F E
      hCfg.A_on.2.1
      hCfg.B_on.2.1
      hCfg.F_on.2.1
      hCfg.E_on.2.1
      hFaceRho0

  have hSidesSigma0 :=
    hilbert_XI24_face_opposite_sides_congruent
      (Geo := Geo)
      sigma0
      C B F G
      hCfg.C_on.2.2
      hCfg.B_on.2.2
      hCfg.F_on.2.2
      hCfg.G_on.2.2
      hFaceSigma0

  have hBA_FE :
      Geo.Congruent B A F E :=
    CongruentReverseFirst
      Geo A B F E
      hSidesRho0.1

  have hBC_FG :
      Geo.Congruent B C F G :=
    CongruentReverseFirst
      Geo C B F G
      hSidesSigma0.1

  --------------------------------------------------------------------
  -- Directed opposite-side data for XI.10.
  --------------------------------------------------------------------

  have hDirAB_EF :
      HilbertSpaceDirectedParallelSegments
        Geo A B E F :=
    hilbert_XI24_parallelogram_directed_opposite_sides
      (Geo := Geo)
      rho0
      A B F E
      hCfg.A_on.2.1
      hCfg.B_on.2.1
      hCfg.F_on.2.1
      hCfg.E_on.2.1
      hFaceRho0

  have hDirCB_GF :
      HilbertSpaceDirectedParallelSegments
        Geo C B G F :=
    hilbert_XI24_parallelogram_directed_opposite_sides
      (Geo := Geo)
      sigma0
      C B F G
      hCfg.C_on.2.2
      hCfg.B_on.2.2
      hCfg.F_on.2.2
      hCfg.G_on.2.2
      hFaceSigma0

  --------------------------------------------------------------------
  -- Nondegeneracy of the two opposite face triangles.
  --------------------------------------------------------------------

  have hNC0 :=
    parallelogram_vertices_noncollinear
      Geo A B C D hFacePi0

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hNC0.2.1

  have hNC1 :=
    parallelogram_vertices_noncollinear
      Geo E F G Hpt hFacePi1

  have hEFG :
      Not (PrimCollinear Geo E F G) :=
    hNC1.2.1

  --------------------------------------------------------------------
  -- The two opposite carrier planes exclude common coplanarity.
  --------------------------------------------------------------------

  have hNoCommonPlane :
      Not
        (exists omega : S.Plane,
          S.OnPlane A omega /\
          S.OnPlane B omega /\
          S.OnPlane C omega /\
          S.OnPlane E omega /\
          S.OnPlane F omega /\
          S.OnPlane G omega) := by

    intro hPlane
    cases hPlane with
    | intro omega hData =>

        have hAomega := hData.1
        have hBomega := hData.2.1
        have hComega := hData.2.2.1
        have hEomega := hData.2.2.2.1
        have hFomega := hData.2.2.2.2.1
        have hGomega := hData.2.2.2.2.2

        have hPi0Omega :
            pi0 = omega :=
          HilbertSpaceIncidence.plane_unique
            (Geo := Geo)
            A B C hABC
            pi0 omega
            hCfg.A_on.1
            hCfg.B_on.1
            hCfg.C_on.1
            hAomega
            hBomega
            hComega

        have hPi1Omega :
            pi1 = omega :=
          HilbertSpaceIncidence.plane_unique
            (Geo := Geo)
            E F G hEFG
            pi1 omega
            hCfg.E_on.1
            hCfg.F_on.1
            hCfg.G_on.1
            hEomega
            hFomega
            hGomega

        have hPiEq :
            pi0 = pi1 :=
          hPi0Omega.trans hPi1Omega.symm

        have hApi1 :
            S.OnPlane A pi1 := by
          rw [<- hPiEq]
          exact hCfg.A_on.1

        exact
          hCfg.pi_parallel
            (Exists.intro A
              (And.intro
                hCfg.A_on.1
                hApi1))

  --------------------------------------------------------------------
  -- XI.10.
  --------------------------------------------------------------------

  have hAngle :
      Geo.AngleCongruent
        A B C
        E F G :=
    euclid_proposition_11_10
      (Geo := Geo)
      A B C
      E F G
      hDirAB_EF
      hDirCB_GF
      hABC
      hEFG
      hNoCommonPlane

  --------------------------------------------------------------------
  -- Spatial SAS.
  --------------------------------------------------------------------

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap Geo B A C h)

  have hFEG :
      Not (PrimCollinear Geo F E G) := by
    intro h
    exact
      hEFG
        (PrimCollinearSwap Geo F E G h)

  have hThirdSide :
      Geo.Congruent A C E G :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      B A C
      F E G
      hBAC
      hFEG
      hBA_FE
      hBC_FG
      hAngle

  have hRemainingAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      B A C
      F E G
      hBAC
      hFEG
      hBA_FE
      hBC_FG
      hAngle

  exact
    {
      sideAB := hBA_FE
      sideBC := hThirdSide
      sideAC := hBC_FG
      angleA := hAngle
      angleB := hRemainingAngles.1
      angleC := hRemainingAngles.2
    }


/-!
# Euclid XI.24 - Wyler three-pair theorem

All three pairs of opposite faces.

The one-pair Wyler proof from test03 is reused by permuting the three
parallel-plane directions.  No second or third copy of the
XI.16-carrier + I.34 + XI.10 + SAS argument is written.
-/

theorem hilbert_XI24_all_opposite_faces_triangle_congruent_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
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
    TriangleCongruenceResult Geo B A C F E G /\
    TriangleCongruenceResult Geo B A F C D G /\
    TriangleCongruenceResult Geo B C F A D E := by

  have hPi :
      TriangleCongruenceResult Geo B A C F E G :=
    hilbert_XI24_opposite_pi_faces_triangle_congruent_wyler
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
        A_on :=
          And.intro hCfg.A_on.2.1
            (And.intro hCfg.A_on.1
              hCfg.A_on.2.2)
        B_on :=
          And.intro hCfg.B_on.2.1
            (And.intro hCfg.B_on.1
              hCfg.B_on.2.2)
        C_on :=
          And.intro hCfg.F_on.2.1
            (And.intro hCfg.F_on.1
              hCfg.F_on.2.2)
        D_on :=
          And.intro hCfg.E_on.2.1
            (And.intro hCfg.E_on.1
              hCfg.E_on.2.2)
        E_on :=
          And.intro hCfg.D_on.2.1
            (And.intro hCfg.D_on.1
              hCfg.D_on.2.2)
        F_on :=
          And.intro hCfg.C_on.2.1
            (And.intro hCfg.C_on.1
              hCfg.C_on.2.2)
        G_on :=
          And.intro hCfg.G_on.2.1
            (And.intro hCfg.G_on.1
              hCfg.G_on.2.2)
        H_on :=
          And.intro hCfg.H_on.2.1
            (And.intro hCfg.H_on.1
              hCfg.H_on.2.2)
      }

  have hRho :
      TriangleCongruenceResult Geo B A F C D G :=
    hilbert_XI24_opposite_pi_faces_triangle_congruent_wyler
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
        A_on :=
          And.intro hCfg.C_on.2.2
            (And.intro hCfg.C_on.1
              hCfg.C_on.2.1)
        B_on :=
          And.intro hCfg.B_on.2.2
            (And.intro hCfg.B_on.1
              hCfg.B_on.2.1)
        C_on :=
          And.intro hCfg.F_on.2.2
            (And.intro hCfg.F_on.1
              hCfg.F_on.2.1)
        D_on :=
          And.intro hCfg.G_on.2.2
            (And.intro hCfg.G_on.1
              hCfg.G_on.2.1)
        E_on :=
          And.intro hCfg.D_on.2.2
            (And.intro hCfg.D_on.1
              hCfg.D_on.2.1)
        F_on :=
          And.intro hCfg.A_on.2.2
            (And.intro hCfg.A_on.1
              hCfg.A_on.2.1)
        G_on :=
          And.intro hCfg.E_on.2.2
            (And.intro hCfg.E_on.1
              hCfg.E_on.2.1)
        H_on :=
          And.intro hCfg.H_on.2.2
            (And.intro hCfg.H_on.1
              hCfg.H_on.2.1)
      }

  have hSigma :
      TriangleCongruenceResult Geo B C F A D E :=
    hilbert_XI24_opposite_pi_faces_triangle_congruent_wyler
      (Geo := Geo)
      sigma0 sigma1
      pi0 pi1
      rho0 rho1
      C B F G
      D A E Hpt
      hCfgSigma

  exact
    And.intro hPi
      (And.intro hRho hSigma)


/--
Euclid XI.24 through the Hilbert-Wyler carrier route.

The conclusion is the same neutral `HilbertXI24Conclusion` used by the
direct theorem.  The difference is the proof path: the six face
parallelograms are obtained from Wyler XI.16 and exact carrier
intersections.
-/
theorem euclid_proposition_11_24_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
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
    HilbertXI24Conclusion
      Geo A B C D E F G Hpt := by

  have hFaces :=
    hilbert_XI24_all_faces_parallelograms_wyler
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hOpp :=
    hilbert_XI24_all_opposite_faces_triangle_congruent_wyler
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  exact
    {
      face_pi0 := hFaces.1
      face_pi1 := hFaces.2.1
      face_rho0 := hFaces.2.2.1
      face_rho1 := hFaces.2.2.2.1
      face_sigma0 := hFaces.2.2.2.2.1
      face_sigma1 := hFaces.2.2.2.2.2
      opposite_pi := hOpp.1
      opposite_rho := hOpp.2.1
      opposite_sigma := hOpp.2.2
    }

end Geometry

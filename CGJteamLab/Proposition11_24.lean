import CGJteamLab.Proposition11_16
import CGJteamLab.Proposition11_10
import CGJteamLab.Proposition34
import CGJteamLab.Hilbert3DRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.24

Production formalization of Euclid, Book XI, Proposition 24.

A parallelepipedal solid is represented by three pairs of parallel
planes.  The eight vertices are the eight triple intersections of
those plane pairs.

The proposition is split according to Euclid's proof:

1. XI.16 is applied twice on each carrier plane, proving that all six
   faces are parallelograms.
2. I.34 gives equality of the corresponding side pairs on the side
   faces.
3. XI.10 gives equality of the included spatial angles.
4. Spatial Hilbert SAS, the ambient form of I.4, gives congruence of
   the corresponding diagonal triangles of each pair of opposite
   parallelogram faces.

No area theory and no general primitive notion of equality of plane
figures is introduced.  The three `TriangleCongruenceResult` fields in
the final conclusion are the explicit synthetic witnesses for Euclid's
claim that opposite parallelogram faces are equal.
-/

/-!
# Euclid XI.24 - face parallelogram lemma

We do not yet formalize equality of opposite faces.
The purpose of this file is to verify the first source dependency of XI.24:

    two pairs of parallel planes + one cutting plane
        -> the four section vertices form a parallelogram.

This is the exact XI.16 part of Euclid XI.24.
-/

/--
One face of a parallelepipedal configuration.

The cutting plane is `pi`.

The two opposite plane pairs are

    rho0 || rho1,
    sigma0 || sigma1.

The four vertices are arranged cyclically as

    A = pi cap rho0 cap sigma1
    B = pi cap rho0 cap sigma0
    C = pi cap rho1 cap sigma0
    D = pi cap rho1 cap sigma1.

Then `ABCD` is a parallelogram.
-/
theorem hilbert_XI24_face_parallelogram
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
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
    IsParallelogram Geo A B C D := by

  have hAB : Ne A B := by
    intro hEq
    subst B
    exact hSigma
      (Exists.intro A
        (And.intro hBsigma0 hAsigma1))

  have hCD : Ne C D := by
    intro hEq
    subst D
    exact hSigma
      (Exists.intro C
        (And.intro hCsigma0 hDsigma1))

  have hBC : Ne B C := by
    intro hEq
    subst C
    exact hRho
      (Exists.intro B
        (And.intro hBrho0 hCrho1))

  have hDA : Ne D A := by
    intro hEq
    subst A
    exact hRho
      (Exists.intro D
        (And.intro hArho0 hDrho1))

  cases
      euclid_proposition_11_16
        (Geo := Geo)
        rho0 rho1 pi
        A D
        hRho
        hArho0 hApi
        hDrho1 hDpi with
  | intro l h1 =>
      cases h1 with
      | intro m hDataRho =>

          have hAl : H.OnLine A l :=
            hDataRho.1

          have hDm : H.OnLine D m :=
            hDataRho.2.1

          have hRho0Iff :=
            hDataRho.2.2.1

          have hRho1Iff :=
            hDataRho.2.2.2.1

          have hLMparallel :=
            hDataRho.2.2.2.2

          have hBl : H.OnLine B l :=
            (hRho0Iff B).mp
              (And.intro hBrho0 hBpi)

          have hCm : H.OnLine C m :=
            (hRho1Iff C).mp
              (And.intro hCrho1 hCpi)

          have hLMdisjoint :
              HilbertLinesDisjoint Geo l m := by
            cases hLMparallel with
            | intro omega hOmega =>
                exact hOmega.2.2

          have hAB_CD :
              Geo.Parallel A B C D := by
            refine And.intro hAB ?_
            refine And.intro hCD ?_
            apply Set.disjoint_left.mpr
            intro X hXAB hXCD

            have hXl : H.OnLine X l :=
              (hilbert_mem_pointLine_iff_onLine
                Geo A B X l
                hAB hAl hBl).mp
                hXAB

            have hXm : H.OnLine X m :=
              (hilbert_mem_pointLine_iff_onLine
                Geo C D X m
                hCD hCm hDm).mp
                hXCD

            exact
              hLMdisjoint
                (Exists.intro X
                  (And.intro hXl hXm))

          cases
              euclid_proposition_11_16
                (Geo := Geo)
                sigma0 sigma1 pi
                B A
                hSigma
                hBsigma0 hBpi
                hAsigma1 hApi with
          | intro n h2 =>
              cases h2 with
              | intro q hDataSigma =>

                  have hBn : H.OnLine B n :=
                    hDataSigma.1

                  have hAq : H.OnLine A q :=
                    hDataSigma.2.1

                  have hSigma0Iff :=
                    hDataSigma.2.2.1

                  have hSigma1Iff :=
                    hDataSigma.2.2.2.1

                  have hNQparallel :=
                    hDataSigma.2.2.2.2

                  have hCn : H.OnLine C n :=
                    (hSigma0Iff C).mp
                      (And.intro hCsigma0 hCpi)

                  have hDq : H.OnLine D q :=
                    (hSigma1Iff D).mp
                      (And.intro hDsigma1 hDpi)

                  have hNQdisjoint :
                      HilbertLinesDisjoint Geo n q := by
                    cases hNQparallel with
                    | intro omega hOmega =>
                        exact hOmega.2.2

                  have hBC_DA :
                      Geo.Parallel B C D A := by
                    refine And.intro hBC ?_
                    refine And.intro hDA ?_
                    apply Set.disjoint_left.mpr
                    intro X hXBC hXDA

                    have hXn : H.OnLine X n :=
                      (hilbert_mem_pointLine_iff_onLine
                        Geo B C X n
                        hBC hBn hCn).mp
                        hXBC

                    have hXq : H.OnLine X q :=
                      (hilbert_mem_pointLine_iff_onLine
                        Geo D A X q
                        hDA hDq hAq).mp
                        hXDA

                    exact
                      hNQdisjoint
                        (Exists.intro X
                          (And.intro hXn hXq))

                  exact
                    And.intro hAB_CD hBC_DA


/-!
# Euclid XI.24 - parallelepiped configuration

Neutral parallelepipedal configuration and the first half of XI.24.

The six planes occur in three opposite parallel pairs:

    pi0    || pi1,
    rho0   || rho1,
    sigma0 || sigma1.

The eight vertices are the eight triple intersections:

    A : pi0, rho0, sigma1
    B : pi0, rho0, sigma0
    C : pi0, rho1, sigma0
    D : pi0, rho1, sigma1

    E : pi1, rho0, sigma1
    F : pi1, rho0, sigma0
    G : pi1, rho1, sigma0
    H : pi1, rho1, sigma1.

No metric data are included in the configuration.
-/

structure HilbertParallelepipedConfiguration
    [S : HilbertSpacePrimitive Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point) : Prop where
  pi_parallel :
    HilbertSpacePlanesParallelIncidence Geo pi0 pi1
  rho_parallel :
    HilbertSpacePlanesParallelIncidence Geo rho0 rho1
  sigma_parallel :
    HilbertSpacePlanesParallelIncidence Geo sigma0 sigma1

  A_on :
    S.OnPlane A pi0 /\
    S.OnPlane A rho0 /\
    S.OnPlane A sigma1

  B_on :
    S.OnPlane B pi0 /\
    S.OnPlane B rho0 /\
    S.OnPlane B sigma0

  C_on :
    S.OnPlane C pi0 /\
    S.OnPlane C rho1 /\
    S.OnPlane C sigma0

  D_on :
    S.OnPlane D pi0 /\
    S.OnPlane D rho1 /\
    S.OnPlane D sigma1

  E_on :
    S.OnPlane E pi1 /\
    S.OnPlane E rho0 /\
    S.OnPlane E sigma1

  F_on :
    S.OnPlane F pi1 /\
    S.OnPlane F rho0 /\
    S.OnPlane F sigma0

  G_on :
    S.OnPlane G pi1 /\
    S.OnPlane G rho1 /\
    S.OnPlane G sigma0

  H_on :
    S.OnPlane Hpt pi1 /\
    S.OnPlane Hpt rho1 /\
    S.OnPlane Hpt sigma1


/--
The six faces of a parallelepipedal configuration are parallelograms.

Face order:

    pi0    : A B C D
    pi1    : E F G H
    rho0   : A B F E
    rho1   : D C G H
    sigma0 : C B F G
    sigma1 : D A E H

Each face is obtained from the same XI.16 helper.
-/
theorem hilbert_XI24_all_faces_parallelograms
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
    hilbert_XI24_face_parallelogram
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
    hilbert_XI24_face_parallelogram
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
    hilbert_XI24_face_parallelogram
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
    hilbert_XI24_face_parallelogram
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
    hilbert_XI24_face_parallelogram
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
    hilbert_XI24_face_parallelogram
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
# Euclid XI.24 - directed opposite sides

Orientation bridge for XI.10.

For a parallelogram `ABCD`, the opposite sides with corresponding
directions are

    AB -> DC.

The directed spatial predicate used by XI.10 additionally records that
the starting points `A,D` lie on the same side of the connector `BC`.
This helper extracts exactly that data from the parallelogram.
-/

theorem hilbert_XI24_parallelogram_directed_opposite_sides
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A B C D : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hCpi : S.OnPlane C pi)
    (hDpi : S.OnPlane D pi)
    (hPar : IsParallelogram Geo A B C D) :
    HilbertSpaceDirectedParallelSegments Geo A B D C := by

  have hAB_DC :
      Geo.Parallel A B D C :=
    ParallelSwapSecondLine
      Geo A B C D hPar.1

  have hAB : Ne A B :=
    hAB_DC.1

  have hDC : Ne D C :=
    hAB_DC.2.1

  cases HilbertPlaneIncidence.line_through A B hAB with
  | intro l hL =>
      have hAl : H.OnLine A l := hL.1
      have hBl : H.OnLine B l := hL.2

      cases HilbertPlaneIncidence.line_through D C hDC with
      | intro m hM =>
          have hDm : H.OnLine D m := hM.1
          have hCm : H.OnLine C m := hM.2

          have hlpi :
              HilbertLineInPlane Geo l pi :=
            HilbertSpaceIncidence.line_in_plane
              (Geo := Geo)
              A B hAB
              l hAl hBl
              pi hApi hBpi

          have hmpi :
              HilbertLineInPlane Geo m pi :=
            HilbertSpaceIncidence.line_in_plane
              (Geo := Geo)
              D C hDC
              m hDm hCm
              pi hDpi hCpi

          have hDisLM :
              HilbertLinesDisjoint Geo l m := by
            intro hMeet
            cases hMeet with
            | intro X hX =>
                have hXl : H.OnLine X l := hX.1
                have hXm : H.OnLine X m := hX.2

                have hXAB :
                    Geo.PointLine A B X :=
                  (hilbert_mem_pointLine_iff_onLine
                    Geo A B X l
                    hAB hAl hBl).mpr
                    hXl

                have hXDC :
                    Geo.PointLine D C X :=
                  (hilbert_mem_pointLine_iff_onLine
                    Geo D C X m
                    hDC hDm hCm).mpr
                    hXm

                exact
                  Set.disjoint_left.mp
                    hAB_DC.2.2
                    hXAB hXDC

          have hDA_BC :
              Geo.Parallel D A B C :=
            ParallelSymmetry
              Geo B C D A hPar.2

          have hDA : Ne D A :=
            hDA_BC.1

          have hBC : Ne B C :=
            hDA_BC.2.1

          cases HilbertPlaneIncidence.line_through B C hBC with
          | intro t hT =>
              have hBt : H.OnLine B t := hT.1
              have hCt : H.OnLine C t := hT.2

              have htpi :
                  HilbertLineInPlane Geo t pi :=
                HilbertSpaceIncidence.line_in_plane
                  (Geo := Geo)
                  B C hBC
                  t hBt hCt
                  pi hBpi hCpi

              cases HilbertPlaneIncidence.line_through D A hDA with
              | intro r hR =>
                  have hDr : H.OnLine D r := hR.1
                  have hAr : H.OnLine A r := hR.2

                  have hAoffT :
                      Not (H.OnLine A t) := by
                    intro hAt

                    have hADA :
                        Geo.PointLine D A A :=
                      (hilbert_mem_pointLine_iff_onLine
                        Geo D A A r
                        hDA hDr hAr).mpr
                        hAr

                    have hABC :
                        Geo.PointLine B C A :=
                      (hilbert_mem_pointLine_iff_onLine
                        Geo B C A t
                        hBC hBt hCt).mpr
                        hAt

                    exact
                      Set.disjoint_left.mp
                        hDA_BC.2.2
                        hADA hABC

                  have hDoffT :
                      Not (H.OnLine D t) := by
                    intro hDt

                    have hDDA :
                        Geo.PointLine D A D :=
                      (hilbert_mem_pointLine_iff_onLine
                        Geo D A D r
                        hDA hDr hAr).mpr
                        hDr

                    have hDBC :
                        Geo.PointLine B C D :=
                      (hilbert_mem_pointLine_iff_onLine
                        Geo B C D t
                        hBC hBt hCt).mpr
                        hDt

                    exact
                      Set.disjoint_left.mp
                        hDA_BC.2.2
                        hDDA hDBC

                  have hNoMeet :
                      Not
                        (HilbertSegmentMeetsLine
                          Geo A D t) := by
                    intro hMeet
                    cases hMeet with
                    | intro X hX =>
                        have hAXD := hX.1
                        have hXt := hX.2

                        have hXr :
                            H.OnLine X r :=
                          hilbert_between_on_line
                            Geo A X D r
                            hAr hDr hAXD

                        have hXDA :
                            Geo.PointLine D A X :=
                          (hilbert_mem_pointLine_iff_onLine
                            Geo D A X r
                            hDA hDr hAr).mpr
                            hXr

                        have hXBC :
                            Geo.PointLine B C X :=
                          (hilbert_mem_pointLine_iff_onLine
                            Geo B C X t
                            hBC hBt hCt).mpr
                            hXt

                        exact
                          Set.disjoint_left.mp
                            hDA_BC.2.2
                            hXDA hXBC

                  have hSameAD :
                      HilbertSameSideInPlane
                        Geo A D t pi := by
                    refine And.intro hApi ?_
                    refine And.intro hDpi ?_
                    refine And.intro hAoffT ?_
                    refine And.intro hDoffT ?_
                    exact
                      Relation.ReflTransGen.single
                        (And.intro hApi
                          (And.intro hDpi
                            (And.intro hAoffT
                              (And.intro hDoffT hNoMeet))))

                  refine Exists.intro pi ?_
                  refine Exists.intro l ?_
                  refine Exists.intro m ?_
                  refine Exists.intro t ?_

                  refine And.intro hAl ?_
                  refine And.intro hBl ?_
                  refine And.intro hDm ?_
                  refine And.intro hCm ?_
                  refine And.intro hlpi ?_
                  refine And.intro hmpi ?_
                  refine And.intro hDisLM ?_
                  refine And.intro hBt ?_
                  refine And.intro hCt ?_
                  refine And.intro htpi ?_
                  exact hSameAD


/-!
# Euclid XI.24 - opposite sides of one face

Apply Euclid I.34 to one ambient face.

An ambient face is first viewed inside its carrier `PlaneGeo pi`.
The ambient parallelogram data are transported to that induced plane,
I.34 gives congruence of opposite sides there, and segment congruence is
then transported back to the ambient geometry.
-/

theorem hilbert_XI24_face_opposite_sides_congruent
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A B C D : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hCpi : S.OnPlane C pi)
    (hDpi : S.OnPlane D pi)
    (hPar : IsParallelogram Geo A B C D) :
    OppositeSidesCongruent Geo A B C D := by

  let Ap : PlanePoint Geo pi :=
    { val := A, property := hApi }

  let Bp : PlanePoint Geo pi :=
    { val := B, property := hBpi }

  let Cp : PlanePoint Geo pi :=
    { val := C, property := hCpi }

  let Dp : PlanePoint Geo pi :=
    { val := D, property := hDpi }

  have hAB : Ne A B :=
    hPar.1.1

  have hCD : Ne C D :=
    hPar.1.2.1

  have hBC : Ne B C :=
    hPar.2.1

  have hDA : Ne D A :=
    hPar.2.2.1

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

  --------------------------------------------------------------------
  -- First opposite side pair in PlaneGeo pi: AB || CD.
  --------------------------------------------------------------------

  have hABCDp :
      (PlaneGeo Geo pi).Parallel Ap Bp Cp Dp := by

    refine And.intro hABp ?_
    refine And.intro hCDp ?_

    apply Set.disjoint_left.mpr
    intro Xp hXABp hXCDp

    cases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Ap Bp hABp with
    | intro lp hL =>
        have hAlp := hL.1
        have hBlp := hL.2

        cases
            HilbertPlaneIncidence.line_through
              (Geo := PlaneGeo Geo pi)
              Cp Dp hCDp with
        | intro mp hM =>
            have hCmp := hM.1
            have hDmp := hM.2

            have hXlp :
                (PlaneGeo Geo pi).OnLine Xp lp :=
              (hilbert_mem_pointLine_iff_onLine
                (PlaneGeo Geo pi)
                Ap Bp Xp lp
                hABp hAlp hBlp).mp
                hXABp

            have hXmp :
                (PlaneGeo Geo pi).OnLine Xp mp :=
              (hilbert_mem_pointLine_iff_onLine
                (PlaneGeo Geo pi)
                Cp Dp Xp mp
                hCDp hCmp hDmp).mp
                hXCDp

            have hXAB :
                Geo.PointLine A B Xp.1 :=
              (hilbert_mem_pointLine_iff_onLine
                Geo A B Xp.1 lp.1
                hAB hAlp hBlp).mpr
                hXlp

            have hXCD :
                Geo.PointLine C D Xp.1 :=
              (hilbert_mem_pointLine_iff_onLine
                Geo C D Xp.1 mp.1
                hCD hCmp hDmp).mpr
                hXmp

            exact
              Set.disjoint_left.mp
                hPar.1.2.2
                hXAB hXCD

  --------------------------------------------------------------------
  -- Second opposite side pair in PlaneGeo pi: BC || DA.
  --------------------------------------------------------------------

  have hBCDAP :
      (PlaneGeo Geo pi).Parallel Bp Cp Dp Ap := by

    refine And.intro hBCp ?_
    refine And.intro hDAp ?_

    apply Set.disjoint_left.mpr
    intro Xp hXBCp hXDAp

    cases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Bp Cp hBCp with
    | intro lp hL =>
        have hBlp := hL.1
        have hClp := hL.2

        cases
            HilbertPlaneIncidence.line_through
              (Geo := PlaneGeo Geo pi)
              Dp Ap hDAp with
        | intro mp hM =>
            have hDmp := hM.1
            have hAmp := hM.2

            have hXlp :
                (PlaneGeo Geo pi).OnLine Xp lp :=
              (hilbert_mem_pointLine_iff_onLine
                (PlaneGeo Geo pi)
                Bp Cp Xp lp
                hBCp hBlp hClp).mp
                hXBCp

            have hXmp :
                (PlaneGeo Geo pi).OnLine Xp mp :=
              (hilbert_mem_pointLine_iff_onLine
                (PlaneGeo Geo pi)
                Dp Ap Xp mp
                hDAp hDmp hAmp).mp
                hXDAp

            have hXBC :
                Geo.PointLine B C Xp.1 :=
              (hilbert_mem_pointLine_iff_onLine
                Geo B C Xp.1 lp.1
                hBC hBlp hClp).mpr
                hXlp

            have hXDA :
                Geo.PointLine D A Xp.1 :=
              (hilbert_mem_pointLine_iff_onLine
                Geo D A Xp.1 mp.1
                hDA hDmp hAmp).mpr
                hXmp

            exact
              Set.disjoint_left.mp
                hPar.2.2.2
                hXBC hXDA

  have hParPlane :
      IsParallelogram
        (PlaneGeo Geo pi) Ap Bp Cp Dp :=
    And.intro hABCDp hBCDAP

  have hI34 :=
    euclid_proposition_34
      (Geo := PlaneGeo Geo pi)
      Ap Bp Cp Dp
      hParPlane

  have hSidesPlane :
      OppositeSidesCongruent
        (PlaneGeo Geo pi) Ap Bp Cp Dp :=
    hI34.1

  have hAB_CD :
      Geo.Congruent A B C D := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi Ap Bp Cp Dp).mp
        hSidesPlane.1
    simpa [Ap, Bp, Cp, Dp] using h

  have hBC_DA :
      Geo.Congruent B C D A := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi Bp Cp Dp Ap).mp
        hSidesPlane.2
    simpa [Ap, Bp, Cp, Dp] using h

  exact And.intro hAB_CD hBC_DA


/-!
# Euclid XI.24 - one pair of opposite faces

One pair of opposite faces.

For the opposite faces

    ABCD
    EFGH

we compare the triangles

    BAC
    FEG.

The source-level dependency is exactly Euclid's XI.24 argument:

* I.34 on face ABFE gives BA ~= FE;
* I.34 on face CBFG gives BC ~= FG;
* the same two side faces provide the directed parallel data for XI.10;
* XI.10 gives angle ABC ~= angle EFG;
* spatial Hilbert SAS, the ambient analogue of I.4, gives full triangle
  congruence BAC ~= FEG.

No area or general theory of equal plane figures is introduced.
-/

theorem hilbert_XI24_opposite_pi_faces_triangle_congruent
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
    hilbert_XI24_all_faces_parallelograms
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
# Euclid XI.24 - all opposite faces

The three pairs of opposite faces.

The one-pair proof is reused by permuting the three plane directions.
No second or third copy of the XI.10 + SAS argument is written.

The three returned triangle congruences represent the three pairs of
opposite parallelogram faces:

    pi0    / pi1    : BAC ~= FEG
    rho0   / rho1   : BAF ~= CDG
    sigma0 / sigma1 : BCF ~= ADE
-/

theorem hilbert_XI24_all_opposite_faces_triangle_congruent
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
    hilbert_XI24_opposite_pi_faces_triangle_congruent
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
    hilbert_XI24_opposite_pi_faces_triangle_congruent
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
    hilbert_XI24_opposite_pi_faces_triangle_congruent
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
Production conclusion for Euclid XI.24.

The six face fields record that every face is a parallelogram.
The three `opposite_*` fields record the diagonal-triangle congruences
that witness equality of the three pairs of opposite faces in Euclid's
argument.
-/
structure HilbertXI24Conclusion
    (Geo : Geometry.Geo)
    (A B C D E F G Hpt : Geo.Point) : Prop where
  face_pi0 :
    IsParallelogram Geo A B C D
  face_pi1 :
    IsParallelogram Geo E F G Hpt
  face_rho0 :
    IsParallelogram Geo A B F E
  face_rho1 :
    IsParallelogram Geo D C G Hpt
  face_sigma0 :
    IsParallelogram Geo C B F G
  face_sigma1 :
    IsParallelogram Geo D A E Hpt

  opposite_pi :
    TriangleCongruenceResult Geo B A C F E G
  opposite_rho :
    TriangleCongruenceResult Geo B A F C D G
  opposite_sigma :
    TriangleCongruenceResult Geo B C F A D E


/--
Euclid XI.24.

If a solid is bounded by three pairs of parallel planes, then all six
faces are parallelograms and the three pairs of opposite faces are equal
in the explicit synthetic sense witnessed by congruent diagonal
triangles.
-/
theorem euclid_proposition_11_24
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
    hilbert_XI24_all_faces_parallelograms
      (Geo := Geo)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg

  have hOpp :=
    hilbert_XI24_all_opposite_faces_triangle_congruent
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

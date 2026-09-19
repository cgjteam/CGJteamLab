import CGJteamLab.Proposition11_23
import CGJteamLab.HilbertWyler3DCompatibility

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.23 - Hilbert-Wyler route

Production Hilbert-Wyler realization of Euclid XI.23 in three-dimensional
Hilbert geometry.

Architecture:

1. Hilbert 3D proves the Hilbert-Wyler incidence package by
   `hilbertWylerAxioms_of_hilbert3D`.
2. The normalization and spatial incidence steps are routed through
   `HilbertWylerAxioms`.
3. The metric, order, Euclidean, PlaneGeo, circumcenter, XI.12, SAS and
   SSS layers are shared with the direct Hilbert proof.
4. No E4 structure or ambient dimension-four assumption is used.

The theorem `euclid_proposition_11_23_wyler_core` exposes the explicit
Hilbert-Wyler incidence dependency.  The public theorem
`euclid_proposition_11_23_wyler` derives that dependency from the Hilbert
3D environment, so Wyler is derived theory in the three-dimensional
setting rather than an additional geometric axiom.
-/


------------------------------------------------------------------------
-- Angle copy in one plane
------------------------------------------------------------------------

theorem hilbert_XI23_copy_angle_equal_radius_in_plane_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [W : HilbertWylerAxioms Geo]
    (pi : S.Plane)
    (A O B C P D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCpi : S.OnPlane C pi)
    (hPpi : S.OnPlane P pi)
    (hDpi : S.OnPlane D pi)
    (hCPD : Not (PrimCollinear Geo C P D)) :
    exists R : Geo.Point,
      S.OnPlane R pi /\
      Geo.Congruent P R P C /\
      Not (PrimCollinear Geo C P R) /\
      Geo.AngleCongruent A O B C P R := by

  have hCP :
      Ne C P :=
    hilbert_noncollinear_ne_first
      Geo C P D hCPD

  cases HP.line_through C P hCP with
  | intro base hBase =>
    have hCbase : H.OnLine C base := hBase.1
    have hPbase : H.OnLine P base := hBase.2

    have hBasePi :
        HilbertLineInPlane Geo base pi :=
      W.line_in_plane
        C P hCP
        base hCbase hPbase
        pi hCpi hPpi

    have hDoff :
        Not (H.OnLine D base) := by
      intro hDbase
      apply hCPD
      exact
        Exists.intro base
          (And.intro hCbase
            (And.intro hPbase hDbase))

    cases
        HilbertSpaceCongruence.angle_construction_in_plane
          (Geo := Geo)
          A O B
          C P D
          hAOB
          hCP
          pi
          base
          hBasePi
          hCbase
          hPbase
          hDpi
          hDoff with
    | intro X hXData =>
      have hXSameSide :
          HilbertSameSideInPlane Geo X D base pi :=
        hXData.1

      have hAOB_CPX :
          Geo.AngleCongruent A O B C P X :=
        hXData.2.1

      have hXpi :
          S.OnPlane X pi :=
        hXSameSide.1

      have hXoff :
          Not (H.OnLine X base) :=
        hXSameSide.2.2.1

      have hPX :
          Ne P X := by
        intro hPXeq
        subst X
        exact hXoff hPbase

      cases
          HilbertSpaceCongruence.segment_construction
            (Geo := Geo)
            P C
            P X
            hPX with
      | intro R hRData =>
        have hRayPXR :
            HilbertSameRay Geo P X R :=
          hRData.1

        have hPR_PC :
            Geo.Congruent P R P C :=
          hRData.2

        have hRpi :
            S.OnPlane R pi := by
          cases hRayPXR.2.2.1 with
          | intro rayLine hRayLineData =>
            have hPray : H.OnLine P rayLine :=
              hRayLineData.1
            have hXray : H.OnLine X rayLine :=
              hRayLineData.2.1
            have hRray : H.OnLine R rayLine :=
              hRayLineData.2.2

            have hRayPi :
                HilbertLineInPlane Geo rayLine pi :=
              W.line_in_plane
                P X hPX
                rayLine hPray hXray
                pi hPpi hXpi

            exact hRayPi R hRray

        have hPR :
            Ne P R :=
          hRayPXR.2.1.symm

        have hCPR :
            Not (PrimCollinear Geo C P R) := by
          intro hCol

          have hRbase :
              H.OnLine R base :=
            hilbert_on_line_of_primCollinear_with_two_on_line
              (Geo := Geo)
              hCP
              hCbase hPbase
              hCol

          cases hRayPXR.2.2.1 with
          | intro rayLine hRayLineData =>
            have hPray : H.OnLine P rayLine :=
              hRayLineData.1
            have hXray : H.OnLine X rayLine :=
              hRayLineData.2.1
            have hRray : H.OnLine R rayLine :=
              hRayLineData.2.2

            have hRayBase :
                rayLine = base :=
              HP.line_unique
                P R hPR
                rayLine base
                hPray hRray
                hPbase hRbase

            rw [hRayBase] at hXray
            exact hXoff hXray

        let Cp : PlanePoint Geo pi :=
          { val := C, property := hCpi }

        let Pp : PlanePoint Geo pi :=
          { val := P, property := hPpi }

        let Xp : PlanePoint Geo pi :=
          { val := X, property := hXpi }

        let Rp : PlanePoint Geo pi :=
          { val := R, property := hRpi }

        have hCPX :
            Not (PrimCollinear Geo C P X) := by
          intro hCol

          have hXbase' :
              H.OnLine X base :=
            hilbert_on_line_of_primCollinear_with_two_on_line
              (Geo := Geo)
              hCP
              hCbase hPbase
              hCol

          exact hXoff hXbase'

        have hCPXPlane :
            Not
              (PrimCollinear
                (PlaneGeo Geo pi)
                Cp Pp Xp) := by
          intro hCol
          apply hCPX
          exact
            planeGeo_primCollinear_to_ambient
              (Geo := Geo)
              pi
              Cp Pp Xp
              hCol

        have hRayPlane :
            HilbertSameRay
              (PlaneGeo Geo pi)
              Pp Xp Rp := by
          apply
            (planeGeo_sameRay_iff_ambient
              (Geo := Geo)
              pi
              Pp Xp Rp).mpr
          simpa [Pp, Xp, Rp] using hRayPXR

        have hAngleEqPlane :
            (PlaneGeo Geo pi).Angle Cp Pp Xp =
            (PlaneGeo Geo pi).Angle Cp Pp Rp :=
          hilbert_angle_eq_of_sameRay_second
            (PlaneGeo Geo pi)
            Pp Cp Xp Rp
            hRayPlane

        have hCPXreflPlane :
            (PlaneGeo Geo pi).AngleCongruent
              Cp Pp Xp
              Cp Pp Xp :=
          HilbertCongruence.angle_congruence_reflexive
            (Geo := PlaneGeo Geo pi)
            Cp Pp Xp
            hCPXPlane

        have hCPX_CPR_plane :
            (PlaneGeo Geo pi).AngleCongruent
              Cp Pp Xp
              Cp Pp Rp := by
          unfold Geometry.Geo.AngleCongruent at hCPXreflPlane
          unfold Geometry.Geo.AngleCongruent
          rw [hAngleEqPlane.symm]
          exact hCPXreflPlane

        have hCPX_CPR :
            Geo.AngleCongruent C P X C P R := by
          have h :=
            (planeGeo_angleCongruent_iff_ambient
              (Geo := Geo)
              pi
              Cp Pp Xp
              Cp Pp Rp).mp
              hCPX_CPR_plane
          simpa [Cp, Pp, Xp, Rp] using h

        have hAOB_CPR :
            Geo.AngleCongruent A O B C P R :=
          Geometry.Geo.angle_congruent_transitivity
            Geo
            A O B
            C P X
            C P R
            hAOB_CPX
            hCPX_CPR

        exact
          Exists.intro R
            (And.intro hRpi
              (And.intro hPR_PC
                (And.intro hCPR hAOB_CPR)))



------------------------------------------------------------------------
-- Three normalized angles in one plane
------------------------------------------------------------------------

theorem hilbert_XI23_three_angles_one_plane_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [W : HilbertWylerAxioms Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (_h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (_h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (_hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists pi : S.Plane,
    exists R1 R2 R3 : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane P pi /\
      S.OnPlane R1 pi /\
      S.OnPlane R2 pi /\
      S.OnPlane R3 pi /\
      Geo.AngleCongruent A O B C P R1 /\
      Geo.AngleCongruent C P D C P R2 /\
      Geo.AngleCongruent E Q F C P R3 /\
      Geo.Congruent P R1 P C /\
      Geo.Congruent P R2 P C /\
      Geo.Congruent P R3 P C /\
      Not (PrimCollinear Geo C P R1) /\
      Not (PrimCollinear Geo C P R2) /\
      Not (PrimCollinear Geo C P R3) := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  cases W.plane_through C P D hCPD with
  | intro pi hPi =>
    have hCpi : S.OnPlane C pi :=
      hPi.1

    have hPpi : S.OnPlane P pi :=
      hPi.2.1

    have hDpi : S.OnPlane D pi :=
      hPi.2.2

    cases
        hilbert_XI23_copy_angle_equal_radius_in_plane_wyler
          (Geo := Geo)
          (W := W)
          pi
          A O B
          C P D
          hAOB
          hCpi hPpi hDpi
          hCPD with
    | intro R1 hR1 =>
      have hR1pi : S.OnPlane R1 pi :=
        hR1.1

      have hPR1_PC :
          Geo.Congruent P R1 P C :=
        hR1.2.1

      have hCPR1 :
          Not (PrimCollinear Geo C P R1) :=
        hR1.2.2.1

      have hAOB_CPR1 :
          Geo.AngleCongruent A O B C P R1 :=
        hR1.2.2.2

      cases
          hilbert_XI23_copy_angle_equal_radius_in_plane_wyler
            (Geo := Geo)
            (W := W)
            pi
            C P D
            C P D
            hCPD
            hCpi hPpi hDpi
            hCPD with
      | intro R2 hR2 =>
        have hR2pi : S.OnPlane R2 pi :=
          hR2.1

        have hPR2_PC :
            Geo.Congruent P R2 P C :=
          hR2.2.1

        have hCPR2 :
            Not (PrimCollinear Geo C P R2) :=
          hR2.2.2.1

        have hCPD_CPR2 :
            Geo.AngleCongruent C P D C P R2 :=
          hR2.2.2.2

        cases
            hilbert_XI23_copy_angle_equal_radius_in_plane_wyler
              (Geo := Geo)
              (W := W)
              pi
              E Q F
              C P D
              hEQF
              hCpi hPpi hDpi
              hCPD with
        | intro R3 hR3 =>
          have hR3pi : S.OnPlane R3 pi :=
            hR3.1

          have hPR3_PC :
              Geo.Congruent P R3 P C :=
            hR3.2.1

          have hCPR3 :
              Not (PrimCollinear Geo C P R3) :=
            hR3.2.2.1

          have hEQF_CPR3 :
              Geo.AngleCongruent E Q F C P R3 :=
            hR3.2.2.2

          refine Exists.intro pi ?_
          refine Exists.intro R1 ?_
          refine Exists.intro R2 ?_
          refine Exists.intro R3 ?_

          constructor
          case left =>
            exact hCpi
          case right =>
            constructor
            case left =>
              exact hPpi
            case right =>
              constructor
              case left =>
                exact hR1pi
              case right =>
                constructor
                case left =>
                  exact hR2pi
                case right =>
                  constructor
                  case left =>
                    exact hR3pi
                  case right =>
                    constructor
                    case left =>
                      exact hAOB_CPR1
                    case right =>
                      constructor
                      case left =>
                        exact hCPD_CPR2
                      case right =>
                        constructor
                        case left =>
                          exact hEQF_CPR3
                        case right =>
                          constructor
                          case left =>
                            exact hPR1_PC
                          case right =>
                            constructor
                            case left =>
                              exact hPR2_PC
                            case right =>
                              constructor
                              case left =>
                                exact hPR3_PC
                              case right =>
                                constructor
                                case left =>
                                  exact hCPR1
                                case right =>
                                  constructor
                                  case left =>
                                    exact hCPR2
                                  case right =>
                                    exact hCPR3


/--
Hilbert 3D public form: derive the Wyler incidence package first.
-/



------------------------------------------------------------------------
-- Normalized XI.22
------------------------------------------------------------------------

theorem hilbert_XI23_normalized_XI22_in_one_plane_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [W : HilbertWylerAxioms Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists pi : S.Plane,
    exists R1 R2 R3 K : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane P pi /\
      S.OnPlane R1 pi /\
      S.OnPlane R2 pi /\
      S.OnPlane R3 pi /\
      S.OnPlane K pi /\
      Geo.AngleCongruent A O B C P R1 /\
      Geo.AngleCongruent C P D C P R2 /\
      Geo.AngleCongruent E Q F C P R3 /\
      Geo.Congruent P C P R1 /\
      Geo.Congruent P C P R2 /\
      Geo.Congruent P C P R3 /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R1
        C P R2
        C P R3 /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R2
        C P R3
        C P R1 /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R3
        C P R1
        C P R2 /\
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        C P R1
        C P R2
        C P R3 /\
      Geo.Congruent C K C R1 /\
      Geo.Congruent R2 K C R3 := by

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  cases
      hilbert_XI23_three_angles_one_plane_wyler
        (Geo := Geo)
        (W := W)
        A O B C P D E Q F
        h12_3 h23_1 h31_2 hFour with
  | intro pi hPiRest =>
    cases hPiRest with
    | intro R1 hR1Rest =>
      cases hR1Rest with
      | intro R2 hR2Rest =>
        cases hR2Rest with
        | intro R3 hData =>

          have hCpi : S.OnPlane C pi :=
            hData.1

          have hPpi : S.OnPlane P pi :=
            hData.2.1

          have hR1pi : S.OnPlane R1 pi :=
            hData.2.2.1

          have hR2pi : S.OnPlane R2 pi :=
            hData.2.2.2.1

          have hR3pi : S.OnPlane R3 pi :=
            hData.2.2.2.2.1

          have hAOB_CPR1 :
              Geo.AngleCongruent A O B C P R1 :=
            hData.2.2.2.2.2.1

          have hCPD_CPR2 :
              Geo.AngleCongruent C P D C P R2 :=
            hData.2.2.2.2.2.2.1

          have hEQF_CPR3 :
              Geo.AngleCongruent E Q F C P R3 :=
            hData.2.2.2.2.2.2.2.1

          have hPR1_PC :
              Geo.Congruent P R1 P C :=
            hData.2.2.2.2.2.2.2.2.1

          have hPR2_PC :
              Geo.Congruent P R2 P C :=
            hData.2.2.2.2.2.2.2.2.2.1

          have hPR3_PC :
              Geo.Congruent P R3 P C :=
            hData.2.2.2.2.2.2.2.2.2.2.1

          have hCPR1 :
              Not (PrimCollinear Geo C P R1) :=
            hData.2.2.2.2.2.2.2.2.2.2.2.1

          have hCPR2 :
              Not (PrimCollinear Geo C P R2) :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hCPR3 :
              Not (PrimCollinear Geo C P R3) :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2

          have h12N :
              HilbertTwoAnglesGreaterThanAngle
                Geo
                C P R1
                C P R2
                C P R3 :=
            hilbert_space_twoAnglesGreater_transport_all_in_plane
              (Geo := Geo)
              pi
              A O B
              C P D
              E Q F
              C P R1
              C P R2
              C P R3
              hCpi hPpi hR1pi
              hCpi hPpi hR2pi
              hCpi hPpi hR3pi
              h12_3
              hCPR1
              hCPR2
              hCPR3
              hAOB_CPR1
              hCPD_CPR2
              hEQF_CPR3

          have h23N :
              HilbertTwoAnglesGreaterThanAngle
                Geo
                C P R2
                C P R3
                C P R1 :=
            hilbert_space_twoAnglesGreater_transport_all_in_plane
              (Geo := Geo)
              pi
              C P D
              E Q F
              A O B
              C P R2
              C P R3
              C P R1
              hCpi hPpi hR2pi
              hCpi hPpi hR3pi
              hCpi hPpi hR1pi
              h23_1
              hCPR2
              hCPR3
              hCPR1
              hCPD_CPR2
              hEQF_CPR3
              hAOB_CPR1

          have h31N :
              HilbertTwoAnglesGreaterThanAngle
                Geo
                C P R3
                C P R1
                C P R2 :=
            hilbert_space_twoAnglesGreater_transport_all_in_plane
              (Geo := Geo)
              pi
              E Q F
              A O B
              C P D
              C P R3
              C P R1
              C P R2
              hCpi hPpi hR3pi
              hCpi hPpi hR1pi
              hCpi hPpi hR2pi
              h31_2
              hCPR3
              hCPR1
              hCPR2
              hEQF_CPR3
              hAOB_CPR1
              hCPD_CPR2

          have hFourN :
              HilbertThreeAnglesLessThanFourRightAngles
                Geo
                C P R1
                C P R2
                C P R3 :=
            hilbert_space_threeAnglesLessThanFourRight_transport_all_in_plane
              (Geo := Geo)
              pi
              A O B
              C P D
              E Q F
              C P R1
              C P R2
              C P R3
              hCpi hPpi hR1pi
              hCpi hPpi hR2pi
              hCpi hPpi hR3pi
              hFour
              hCPR1
              hCPR2
              hCPR3
              hAOB_CPR1
              hCPD_CPR2
              hEQF_CPR3

          let Cp : PlanePoint Geo pi :=
            { val := C, property := hCpi }

          let Pp : PlanePoint Geo pi :=
            { val := P, property := hPpi }

          let R1p : PlanePoint Geo pi :=
            { val := R1, property := hR1pi }

          let R2p : PlanePoint Geo pi :=
            { val := R2, property := hR2pi }

          let R3p : PlanePoint Geo pi :=
            { val := R3, property := hR3pi }

          have h12Plane :
              HilbertTwoAnglesGreaterThanAngle
                (PlaneGeo Geo pi)
                Cp Pp R1p
                Cp Pp R2p
                Cp Pp R3p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_twoAnglesGreater_to_plane
                (Geo := Geo)
                pi
                C P R1
                C P R2
                C P R3
                hCpi hPpi hR1pi
                hCpi hPpi hR2pi
                hCpi hPpi hR3pi
                h12N)

          have h23Plane :
              HilbertTwoAnglesGreaterThanAngle
                (PlaneGeo Geo pi)
                Cp Pp R2p
                Cp Pp R3p
                Cp Pp R1p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_twoAnglesGreater_to_plane
                (Geo := Geo)
                pi
                C P R2
                C P R3
                C P R1
                hCpi hPpi hR2pi
                hCpi hPpi hR3pi
                hCpi hPpi hR1pi
                h23N)

          have h31Plane :
              HilbertTwoAnglesGreaterThanAngle
                (PlaneGeo Geo pi)
                Cp Pp R3p
                Cp Pp R1p
                Cp Pp R2p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_twoAnglesGreater_to_plane
                (Geo := Geo)
                pi
                C P R3
                C P R1
                C P R2
                hCpi hPpi hR3pi
                hCpi hPpi hR1pi
                hCpi hPpi hR2pi
                h31N)

          have hFourPlane :
              HilbertThreeAnglesLessThanFourRightAngles
                (PlaneGeo Geo pi)
                Cp Pp R1p
                Cp Pp R2p
                Cp Pp R3p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_threeAnglesFourRight_to_plane
                (Geo := Geo)
                pi
                C P R1
                C P R2
                C P R3
                hCpi hPpi hR1pi
                hCpi hPpi hR2pi
                hCpi hPpi hR3pi
                hFourN)

          have hPC : Ne P C :=
            (hilbert_noncollinear_ne_first
              Geo C P D hCPD).symm

          have hPR1C :
              Not (PrimCollinear Geo P R1 C) := by
            intro hCol
            apply hCPR1
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.2
                    (And.intro hL.1 hL.2.1))

          have hPR2C :
              Not (PrimCollinear Geo P R2 C) := by
            intro hCol
            apply hCPR2
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.2
                    (And.intro hL.1 hL.2.1))

          have hPR3C :
              Not (PrimCollinear Geo P R3 C) := by
            intro hCol
            apply hCPR3
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.2
                    (And.intro hL.1 hL.2.1))

          have hPR1 : Ne P R1 :=
            hilbert_noncollinear_ne_first
              Geo P R1 C hPR1C

          have hPR2 : Ne P R2 :=
            hilbert_noncollinear_ne_first
              Geo P R2 C hPR2C

          have hPR3 : Ne P R3 :=
            hilbert_noncollinear_ne_first
              Geo P R3 C hPR3C

          have hPC_PR1 :
              Geo.Congruent P C P R1 :=
            hilbert_space_congruent_symmetry
              (Geo := Geo)
              P R1
              P C
              hPR1
              hPR1_PC

          have hPC_PR2 :
              Geo.Congruent P C P R2 :=
            hilbert_space_congruent_symmetry
              (Geo := Geo)
              P R2
              P C
              hPR2
              hPR2_PC

          have hPC_PR3 :
              Geo.Congruent P C P R3 :=
            hilbert_space_congruent_symmetry
              (Geo := Geo)
              P R3
              P C
              hPR3
              hPR3_PC

          have hPC_PC :
              Geo.Congruent P C P C :=
            hilbert_space_congruent_reflexive
              (Geo := Geo)
              P C hPC

          have hPC_PR1_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp R1p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp R1p).mpr
            simpa [Pp, Cp, R1p] using hPC_PR1

          have hPC_PR2_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp R2p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp R2p).mpr
            simpa [Pp, Cp, R2p] using hPC_PR2

          have hPC_PR3_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp R3p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp R3p).mpr
            simpa [Pp, Cp, R3p] using hPC_PR3

          have hPC_PC_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp Cp := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp Cp).mpr
            simpa [Pp, Cp] using hPC_PC

          cases
              euclid_proposition_11_22
                (PlaneGeo Geo pi)
                Cp Pp R1p
                Cp Pp R2p
                Cp Pp R3p
                h12Plane
                h23Plane
                h31Plane
                hPC_PR1_plane
                hPC_PC_plane
                hPC_PR2_plane
                hPC_PC_plane
                hPC_PR3_plane with
          | intro Kp hKData =>
            let K : Geo.Point := Kp.1

            have hKpi : S.OnPlane K pi := by
              simpa [K] using Kp.2

            have hCK_CR1 :
                Geo.Congruent C K C R1 := by
              have h :=
                (planeGeo_congruent
                  (Geo := Geo)
                  pi
                  Cp Kp
                  Cp R1p).mp
                  hKData.1
              simpa [Cp, R1p, K] using h

            have hR2K_CR3 :
                Geo.Congruent R2 K C R3 := by
              have h :=
                (planeGeo_congruent
                  (Geo := Geo)
                  pi
                  R2p Kp
                  Cp R3p).mp
                  hKData.2
              simpa [R2p, Cp, R3p, K] using h

            refine Exists.intro pi ?_
            refine Exists.intro R1 ?_
            refine Exists.intro R2 ?_
            refine Exists.intro R3 ?_
            refine Exists.intro K ?_

            constructor
            case left =>
              exact hCpi
            case right =>
              constructor
              case left =>
                exact hPpi
              case right =>
                constructor
                case left =>
                  exact hR1pi
                case right =>
                  constructor
                  case left =>
                    exact hR2pi
                  case right =>
                    constructor
                    case left =>
                      exact hR3pi
                    case right =>
                      constructor
                      case left =>
                        exact hKpi
                      case right =>
                        constructor
                        case left =>
                          exact hAOB_CPR1
                        case right =>
                          constructor
                          case left =>
                            exact hCPD_CPR2
                          case right =>
                            constructor
                            case left =>
                              exact hEQF_CPR3
                            case right =>
                              constructor
                              case left =>
                                exact hPC_PR1
                              case right =>
                                constructor
                                case left =>
                                  exact hPC_PR2
                                case right =>
                                  constructor
                                  case left =>
                                    exact hPC_PR3
                                  case right =>
                                    constructor
                                    case left =>
                                      exact h12N
                                    case right =>
                                      constructor
                                      case left =>
                                        exact h23N
                                      case right =>
                                        constructor
                                        case left =>
                                          exact h31N
                                        case right =>
                                          constructor
                                          case left =>
                                            exact hFourN
                                          case right =>
                                            constructor
                                            case left =>
                                              exact hCK_CR1
                                            case right =>
                                              exact hR2K_CR3



------------------------------------------------------------------------
-- Spatial apex
------------------------------------------------------------------------

theorem hilbert_XI23_normalized_spatial_apex_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    [W : HilbertWylerAxioms Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo A O B C P D E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo C P D E Q F A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo E Q F A O B C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo A O B C P D E Q F) :
    exists pi : S.Plane,
    exists R1 R2 R3 K R : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane P pi /\
      S.OnPlane R1 pi /\
      S.OnPlane R2 pi /\
      S.OnPlane R3 pi /\
      S.OnPlane K pi /\
      Not (S.OnPlane R pi) /\
      Geo.AngleCongruent A O B C P R1 /\
      Geo.AngleCongruent C P D C P R2 /\
      Geo.AngleCongruent E Q F C P R3 /\
      Not (PrimCollinear Geo C P R1) /\
      Not (PrimCollinear Geo C P R2) /\
      Not (PrimCollinear Geo C P R3) /\
      Geo.Congruent P C P R1 /\
      Geo.Congruent P C P R2 /\
      Geo.Congruent P C P R3 /\
      Geo.Congruent C K C R1 /\
      Geo.Congruent R2 K C R3 /\
      Not (PrimCollinear Geo C R2 K) /\
      Geo.Congruent R C P C /\
      Geo.Congruent R R2 P C /\
      Geo.Congruent R K P C := by

  cases
      hilbert_XI23_normalized_XI22_in_one_plane_wyler
        (Geo := Geo)
        (W := W)
        A O B C P D E Q F
        h12_3 h23_1 h31_2 hFour with
  | intro pi hPiRest =>
    cases hPiRest with
    | intro R1 hR1Rest =>
      cases hR1Rest with
      | intro R2 hR2Rest =>
        cases hR2Rest with
        | intro R3 hR3Rest =>
          cases hR3Rest with
          | intro K hData =>

          have hCpi :
              S.OnPlane C pi :=
            hData.1

          have hPpi :
              S.OnPlane P pi :=
            hData.2.1

          have hR1pi :
              S.OnPlane R1 pi :=
            hData.2.2.1

          have hR2pi :
              S.OnPlane R2 pi :=
            hData.2.2.2.1

          have hR3pi :
              S.OnPlane R3 pi :=
            hData.2.2.2.2.1

          have hKpi :
              S.OnPlane K pi :=
            hData.2.2.2.2.2.1

          have hAOB_CPR1 :
              Geo.AngleCongruent A O B C P R1 :=
            hData.2.2.2.2.2.2.1

          have hCPD_CPR2 :
              Geo.AngleCongruent C P D C P R2 :=
            hData.2.2.2.2.2.2.2.1

          have hEQF_CPR3 :
              Geo.AngleCongruent E Q F C P R3 :=
            hData.2.2.2.2.2.2.2.2.1

          have hPC_PR1 :
              Geo.Congruent P C P R1 :=
            hData.2.2.2.2.2.2.2.2.2.1

          have hPC_PR2 :
              Geo.Congruent P C P R2 :=
            hData.2.2.2.2.2.2.2.2.2.2.1

          have hPC_PR3 :
              Geo.Congruent P C P R3 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.1

          have h12N :
              HilbertTwoAnglesGreaterThanAngle
                Geo C P R1 C P R2 C P R3 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.1

          have h23N :
              HilbertTwoAnglesGreaterThanAngle
                Geo C P R2 C P R3 C P R1 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have h31N :
              HilbertTwoAnglesGreaterThanAngle
                Geo C P R3 C P R1 C P R2 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hFourN :
              HilbertThreeAnglesLessThanFourRightAngles
                Geo C P R1 C P R2 C P R3 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hCK_CR1 :
              Geo.Congruent C K C R1 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hR2K_CR3 :
              Geo.Congruent R2 K C R3 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

          have hCPR1 :
              Not (PrimCollinear Geo C P R1) :=
            h12N.1

          have hCPR2 :
              Not (PrimCollinear Geo C P R2) :=
            h12N.2.1

          have hCPR3 :
              Not (PrimCollinear Geo C P R3) :=
            h12N.2.2.1

          let Cp : PlanePoint Geo pi :=
            { val := C, property := hCpi }

          let Pp : PlanePoint Geo pi :=
            { val := P, property := hPpi }

          let R1p : PlanePoint Geo pi :=
            { val := R1, property := hR1pi }

          let R2p : PlanePoint Geo pi :=
            { val := R2, property := hR2pi }

          let R3p : PlanePoint Geo pi :=
            { val := R3, property := hR3pi }

          let Kp : PlanePoint Geo pi :=
            { val := K, property := hKpi }

          have h12Plane :
              HilbertTwoAnglesGreaterThanAngle
                (PlaneGeo Geo pi)
                Cp Pp R1p
                Cp Pp R2p
                Cp Pp R3p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_twoAnglesGreater_to_plane
                (Geo := Geo)
                pi
                C P R1
                C P R2
                C P R3
                hCpi hPpi hR1pi
                hCpi hPpi hR2pi
                hCpi hPpi hR3pi
                h12N)

          have h23Plane :
              HilbertTwoAnglesGreaterThanAngle
                (PlaneGeo Geo pi)
                Cp Pp R2p
                Cp Pp R3p
                Cp Pp R1p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_twoAnglesGreater_to_plane
                (Geo := Geo)
                pi
                C P R2
                C P R3
                C P R1
                hCpi hPpi hR2pi
                hCpi hPpi hR3pi
                hCpi hPpi hR1pi
                h23N)

          have h31Plane :
              HilbertTwoAnglesGreaterThanAngle
                (PlaneGeo Geo pi)
                Cp Pp R3p
                Cp Pp R1p
                Cp Pp R2p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_twoAnglesGreater_to_plane
                (Geo := Geo)
                pi
                C P R3
                C P R1
                C P R2
                hCpi hPpi hR3pi
                hCpi hPpi hR1pi
                hCpi hPpi hR2pi
                h31N)

          have hFourPlane :
              HilbertThreeAnglesLessThanFourRightAngles
                (PlaneGeo Geo pi)
                Cp Pp R1p
                Cp Pp R2p
                Cp Pp R3p := by
            simpa [Cp, Pp, R1p, R2p, R3p] using
              (hilbert_space_threeAnglesFourRight_to_plane
                (Geo := Geo)
                pi
                C P R1
                C P R2
                C P R3
                hCpi hPpi hR1pi
                hCpi hPpi hR2pi
                hCpi hPpi hR3pi
                hFourN)

          have hPC : Ne P C :=
            (hilbert_noncollinear_ne_first
              Geo C P R1 hCPR1).symm

          have hPC_PC :
              Geo.Congruent P C P C :=
            hilbert_space_congruent_reflexive
              (Geo := Geo)
              P C hPC

          have hPC_PR1_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp R1p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp R1p).mpr
            simpa [Pp, Cp, R1p] using hPC_PR1

          have hPC_PR2_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp R2p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp R2p).mpr
            simpa [Pp, Cp, R2p] using hPC_PR2

          have hPC_PR3_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp R3p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp R3p).mpr
            simpa [Pp, Cp, R3p] using hPC_PR3

          have hPC_PC_plane :
              (PlaneGeo Geo pi).Congruent
                Pp Cp Pp Cp := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Pp Cp Pp Cp).mpr
            simpa [Pp, Cp] using hPC_PC

          have hCK_CR1_plane :
              (PlaneGeo Geo pi).Congruent
                Cp Kp Cp R1p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi Cp Kp Cp R1p).mpr
            simpa [Cp, Kp, R1p] using hCK_CR1

          have hR2K_CR3_plane :
              (PlaneGeo Geo pi).Congruent
                R2p Kp Cp R3p := by
            apply
              (planeGeo_congruent
                (Geo := Geo)
                pi R2p Kp Cp R3p).mpr
            simpa [R2p, Kp, Cp, R3p] using hR2K_CR3

          have hCR2KPlane :
              Not
                (PrimCollinear
                  (PlaneGeo Geo pi)
                  Cp R2p Kp) :=
            hilbert_XI23_chord_triangle_noncollinear_XI
              (PlaneGeo Geo pi)
              Cp Pp R1p
              Cp Pp R2p
              Cp Pp R3p
              Kp
              h12Plane
              h23Plane
              h31Plane
              hPC_PR1_plane
              hPC_PC_plane
              hPC_PR2_plane
              hPC_PC_plane
              hPC_PR3_plane
              hCK_CR1_plane
              hR2K_CR3_plane

          have hCR2K :
              Not (PrimCollinear Geo C R2 K) :=
            planeGeo_not_primCollinear_to_ambient
              (Geo := Geo)
              pi
              Cp R2p Kp
              hCR2KPlane

          cases
              hilbert_triangle_circumcenter_exists_XI
                (PlaneGeo Geo pi)
                Cp R2p Kp
                hCR2KPlane with
          | intro Up hUData =>
            have hUC_UR2_plane :
                (PlaneGeo Geo pi).Congruent
                  Up Cp Up R2p :=
              hUData.1

            have hUC_UK_plane :
                (PlaneGeo Geo pi).Congruent
                  Up Cp Up Kp :=
              hUData.2

            let U : Geo.Point := Up.1

            have hUpi : S.OnPlane U pi := by
              simpa [U] using Up.2

            have hUC_UR2 :
                Geo.Congruent U C U R2 := by
              have h :=
                (planeGeo_congruent
                  (Geo := Geo)
                  pi
                  Up Cp
                  Up R2p).mp
                  hUC_UR2_plane
              simpa [U, Cp, R2p] using h

            have hUC_UK :
                Geo.Congruent U C U K := by
              have h :=
                (planeGeo_congruent
                  (Geo := Geo)
                  pi
                  Up Cp
                  Up Kp).mp
                  hUC_UK_plane
              simpa [U, Cp, Kp] using h

            cases
                hilbert_XI23_radius_height_in_plane_XI
                  (Geo := Geo)
                  pi
                  Cp Pp R1p
                  Cp Pp R2p
                  Cp Pp R3p
                  Up Kp
                  h12Plane
                  h23Plane
                  h31Plane
                  hFourPlane
                  hPC_PR1_plane
                  hPC_PC_plane
                  hPC_PR2_plane
                  hPC_PC_plane
                  hPC_PR3_plane
                  hCK_CR1_plane
                  hR2K_CR3_plane
                  hUC_UR2_plane
                  hUC_UK_plane with
            | intro hRadiusPlane hHeight =>

              cases hHeight with
              | intro E0p hE0Rest =>
                cases hE0Rest with
                | intro K0p hK0Rest =>
                  cases hK0Rest with
                  | intro H0p hAux =>

                    have hPE0C_plane :
                        (PlaneGeo Geo pi).Between Pp E0p Cp :=
                      hAux.1

                    have hPE0_UC_plane :
                        (PlaneGeo Geo pi).Congruent
                          Pp E0p Up Cp :=
                      hAux.2.1

                    have hPH0_PC_plane :
                        (PlaneGeo Geo pi).Congruent
                          Pp H0p Pp Cp :=
                      hAux.2.2.2.1

                    have hE0PH0_plane :
                        Not
                          (PrimCollinear
                            (PlaneGeo Geo pi)
                            E0p Pp H0p) :=
                      hAux.2.2.2.2.2.1

                    have hRightPE0H0_plane :
                        HilbertRightAngle
                          (PlaneGeo Geo pi)
                          Pp E0p H0p :=
                      hAux.2.2.2.2.2.2

                    let E0 : Geo.Point := E0p.1
                    let H0 : Geo.Point := H0p.1

                    have hNonzero :=
                      bookZero_48_lessThanNotEqual
                        (PlaneGeo Geo pi)
                        Up Cp
                        Pp Cp
                        hRadiusPlane

                    have hUCPlane : Ne Up Cp :=
                      hNonzero.1

                    have hUC : Ne U C := by
                      intro h
                      apply hUCPlane
                      exact Subtype.ext h

                    have hUR2Plane : Ne Up R2p :=
                      bookZero_nullSegment3
                        (PlaneGeo Geo pi)
                        Up Cp
                        Up R2p
                        hUCPlane
                        hUC_UR2_plane

                    have hUR2 : Ne U R2 := by
                      intro h
                      apply hUR2Plane
                      exact Subtype.ext h

                    have hUKPlane : Ne Up Kp :=
                      bookZero_nullSegment3
                        (PlaneGeo Geo pi)
                        Up Cp
                        Up Kp
                        hUCPlane
                        hUC_UK_plane

                    have hUK : Ne U K := by
                      intro h
                      apply hUKPlane
                      exact Subtype.ext h

                    have hPE0C :
                        Geo.Between P E0 C := by
                      have h :=
                        (planeGeo_between
                          (Geo := Geo)
                          pi
                          Pp E0p Cp).mp
                          hPE0C_plane
                      simpa [Pp, E0, Cp] using h

                    have hPE0 : Ne P E0 :=
                      (HilbertSpaceOrder.between_incidence
                        (Geo := Geo)
                        P E0 C hPE0C).1

                    have hPE0_UC :
                        Geo.Congruent P E0 U C := by
                      have h :=
                        (planeGeo_congruent
                          (Geo := Geo)
                          pi
                          Pp E0p
                          Up Cp).mp
                          hPE0_UC_plane
                      simpa [Pp, E0, U, Cp] using h

                    have hUC_PE0 :
                        Geo.Congruent U C P E0 :=
                      hilbert_space_congruent_symmetry
                        (Geo := Geo)
                        P E0
                        U C
                        hPE0
                        hPE0_UC

                    have hUC_E0P :
                        Geo.Congruent U C E0 P :=
                      (Geometry.Geo.congruent_reverse_second
                        Geo
                        U C
                        P E0).mp
                        hUC_PE0

                    have hUR2_E0P :
                        Geo.Congruent U R2 E0 P :=
                      HilbertSpaceCongruence.segment_congruence_common
                        (Geo := Geo)
                        U C
                        U R2
                        E0 P
                        hUC_UR2
                        hUC_E0P

                    have hUK_E0P :
                        Geo.Congruent U K E0 P :=
                      HilbertSpaceCongruence.segment_congruence_common
                        (Geo := Geo)
                        U C
                        U K
                        E0 P
                        hUC_UK
                        hUC_E0P

                    have hPH0_PC :
                        Geo.Congruent P H0 P C := by
                      have h :=
                        (planeGeo_congruent
                          (Geo := Geo)
                          pi
                          Pp H0p
                          Pp Cp).mp
                          hPH0_PC_plane
                      simpa [Pp, H0, Cp] using h

                    have hE0PH0 :
                        Not (PrimCollinear Geo E0 P H0) := by
                      have h :=
                        planeGeo_not_primCollinear_to_ambient
                          (Geo := Geo)
                          pi
                          E0p Pp H0p
                          hE0PH0_plane
                      simpa [E0, Pp, H0] using h

                    have hRightPE0H0 :
                        HilbertRightAngle Geo P E0 H0 := by
                      have h :=
                        (planeGeo_rightAngle_iff_ambient
                          (Geo := Geo)
                          pi
                          Pp E0p H0p).mp
                          hRightPE0H0_plane
                      simpa [Pp, E0, H0] using h

                    cases
                        hilbert_XI23_spatial_apex_from_right_triangle_XI
                          (Geo := Geo)
                          C R2 K U E0 P H0
                          pi
                          hCpi
                          hR2pi
                          hKpi
                          hUpi
                          hUC
                          hUR2
                          hUK
                          hUC_E0P
                          hUR2_E0P
                          hUK_E0P
                          hE0PH0
                          hRightPE0H0 with
                    | intro R hRData =>

                      have hRoff :
                          Not (S.OnPlane R pi) :=
                        hRData.1

                      have hCR_PH0 :
                          Geo.Congruent C R P H0 :=
                        hRData.2.1

                      have hR2R_PH0 :
                          Geo.Congruent R2 R P H0 :=
                        hRData.2.2.1

                      have hKR_PH0 :
                          Geo.Congruent K R P H0 :=
                        hRData.2.2.2

                      have hCR : Ne C R := by
                        intro hEq
                        subst R
                        exact hRoff hCpi

                      have hR2R : Ne R2 R := by
                        intro hEq
                        subst R
                        exact hRoff hR2pi

                      have hKR : Ne K R := by
                        intro hEq
                        subst R
                        exact hRoff hKpi

                      have hPH0_CR :
                          Geo.Congruent P H0 C R :=
                        hilbert_space_congruent_symmetry
                          (Geo := Geo)
                          C R
                          P H0
                          hCR
                          hCR_PH0

                      have hPH0_R2R :
                          Geo.Congruent P H0 R2 R :=
                        hilbert_space_congruent_symmetry
                          (Geo := Geo)
                          R2 R
                          P H0
                          hR2R
                          hR2R_PH0

                      have hPH0_KR :
                          Geo.Congruent P H0 K R :=
                        hilbert_space_congruent_symmetry
                          (Geo := Geo)
                          K R
                          P H0
                          hKR
                          hKR_PH0

                      have hCR_PC :
                          Geo.Congruent C R P C :=
                        HilbertSpaceCongruence.segment_congruence_common
                          (Geo := Geo)
                          P H0
                          C R
                          P C
                          hPH0_CR
                          hPH0_PC

                      have hR2R_PC :
                          Geo.Congruent R2 R P C :=
                        HilbertSpaceCongruence.segment_congruence_common
                          (Geo := Geo)
                          P H0
                          R2 R
                          P C
                          hPH0_R2R
                          hPH0_PC

                      have hKR_PC :
                          Geo.Congruent K R P C :=
                        HilbertSpaceCongruence.segment_congruence_common
                          (Geo := Geo)
                          P H0
                          K R
                          P C
                          hPH0_KR
                          hPH0_PC

                      have hRC_PC :
                          Geo.Congruent R C P C :=
                        (Geometry.Geo.congruent_reverse_first
                          Geo
                          C R
                          P C).mp
                          hCR_PC

                      have hRR2_PC :
                          Geo.Congruent R R2 P C :=
                        (Geometry.Geo.congruent_reverse_first
                          Geo
                          R2 R
                          P C).mp
                          hR2R_PC

                      have hRK_PC :
                          Geo.Congruent R K P C :=
                        (Geometry.Geo.congruent_reverse_first
                          Geo
                          K R
                          P C).mp
                          hKR_PC

                      refine Exists.intro pi ?_
                      refine Exists.intro R1 ?_
                      refine Exists.intro R2 ?_
                      refine Exists.intro R3 ?_
                      refine Exists.intro K ?_
                      refine Exists.intro R ?_

                      refine And.intro hCpi ?_
                      refine And.intro hPpi ?_
                      refine And.intro hR1pi ?_
                      refine And.intro hR2pi ?_
                      refine And.intro hR3pi ?_
                      refine And.intro hKpi ?_
                      refine And.intro hRoff ?_
                      refine And.intro hAOB_CPR1 ?_
                      refine And.intro hCPD_CPR2 ?_
                      refine And.intro hEQF_CPR3 ?_
                      refine And.intro hCPR1 ?_
                      refine And.intro hCPR2 ?_
                      refine And.intro hCPR3 ?_
                      refine And.intro hPC_PR1 ?_
                      refine And.intro hPC_PR2 ?_
                      refine And.intro hPC_PR3 ?_
                      refine And.intro hCK_CR1 ?_
                      refine And.intro hR2K_CR3 ?_
                      refine And.intro hCR2K ?_
                      refine And.intro hRC_PC ?_
                      refine And.intro hRR2_PC ?_
                      exact hRK_PC

/--
Hilbert 3D public form: derive the Wyler incidence package first.
-/



------------------------------------------------------------------------
-- Wyler core theorem
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Public Hilbert 3D theorem
------------------------------------------------------------------------

theorem euclid_proposition_11_23_wyler_core
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    [W : HilbertWylerAxioms Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo A O B C P D E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo C P D E Q F A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo E Q F A O B C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo A O B C P D E Q F) :
    HilbertThreeAnglesHaveTrihedralRealization
      Geo A O B C P D E Q F := by

  cases
      hilbert_XI23_normalized_spatial_apex_wyler
        (Geo := Geo)
        (W := W)
        A O B C P D E Q F
        h12_3 h23_1 h31_2 hFour with
  | intro pi hPiRest =>
    cases hPiRest with
    | intro R1 hR1Rest =>
      cases hR1Rest with
      | intro R2 hR2Rest =>
        cases hR2Rest with
        | intro R3 hR3Rest =>
          cases hR3Rest with
          | intro K hKRest =>
            cases hKRest with
            | intro R hData =>

          have hCpi :
              S.OnPlane C pi :=
            hData.1

          have hPpi :
              S.OnPlane P pi :=
            hData.2.1

          have hR1pi :
              S.OnPlane R1 pi :=
            hData.2.2.1

          have hR2pi :
              S.OnPlane R2 pi :=
            hData.2.2.2.1

          have hR3pi :
              S.OnPlane R3 pi :=
            hData.2.2.2.2.1

          have hKpi :
              S.OnPlane K pi :=
            hData.2.2.2.2.2.1

          have hRoff :
              Not (S.OnPlane R pi) :=
            hData.2.2.2.2.2.2.1

          have hAOB_CPR1 :
              Geo.AngleCongruent A O B C P R1 :=
            hData.2.2.2.2.2.2.2.1

          have hCPD_CPR2 :
              Geo.AngleCongruent C P D C P R2 :=
            hData.2.2.2.2.2.2.2.2.1

          have hEQF_CPR3 :
              Geo.AngleCongruent E Q F C P R3 :=
            hData.2.2.2.2.2.2.2.2.2.1

          have hCPR1 :
              Not (PrimCollinear Geo C P R1) :=
            hData.2.2.2.2.2.2.2.2.2.2.1

          have hCPR2 :
              Not (PrimCollinear Geo C P R2) :=
            hData.2.2.2.2.2.2.2.2.2.2.2.1

          have hCPR3 :
              Not (PrimCollinear Geo C P R3) :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hPC_PR1 :
              Geo.Congruent P C P R1 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hPC_PR2 :
              Geo.Congruent P C P R2 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hPC_PR3 :
              Geo.Congruent P C P R3 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hCK_CR1 :
              Geo.Congruent C K C R1 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hR2K_CR3 :
              Geo.Congruent R2 K C R3 :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hCR2K :
              Not (PrimCollinear Geo C R2 K) :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hRC_PC :
              Geo.Congruent R C P C :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hRR2_PC :
              Geo.Congruent R R2 P C :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

          have hRK_PC :
              Geo.Congruent R K P C :=
            hData.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

          have hCR2 : Ne C R2 :=
            hilbert_noncollinear_ne_first
              Geo C R2 K hCR2K

          have hR2KC :
              Not (PrimCollinear Geo R2 K C) := by
            intro hCol
            apply hCR2K
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.2
                    (And.intro hL.1 hL.2.1))

          have hR2K : Ne R2 K :=
            hilbert_noncollinear_ne_first
              Geo R2 K C hR2KC

          have hKCR2 :
              Not (PrimCollinear Geo K C R2) := by
            intro hCol
            apply hCR2K
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.2.2 hL.1))

          have hKC : Ne K C :=
            hilbert_noncollinear_ne_first
              Geo K C R2 hKCR2

          have hRC : Ne R C := by
            intro hEq
            subst R
            exact hRoff hCpi

          have hRR2 : Ne R R2 := by
            intro hEq
            subst R
            exact hRoff hR2pi

          have hRK : Ne R K := by
            intro hEq
            subst R
            exact hRoff hKpi

          --------------------------------------------------------------
          -- Wyler plane-preservation helper.
          --------------------------------------------------------------

          have hOnPlaneOfCollinear :
              forall X Y Z : Geo.Point,
                Ne X Y ->
                S.OnPlane X pi ->
                S.OnPlane Y pi ->
                PrimCollinear Geo X Y Z ->
                S.OnPlane Z pi := by
            intro X Y Z hXY hXpi hYpi hCol

            cases HP.line_through X Y hXY with
            | intro l hL =>
              have hXl : H.OnLine X l :=
                hL.1

              have hYl : H.OnLine Y l :=
                hL.2

              have hlpi :
                  HilbertLineInPlane Geo l pi :=
                W.line_in_plane
                  X Y hXY
                  l hXl hYl
                  pi hXpi hYpi

              have hZl :
                  H.OnLine Z l :=
                hilbert_on_line_of_primCollinear_with_two_on_line
                  (Geo := Geo)
                  hXY
                  hXl hYl
                  hCol

              exact hlpi Z hZl

          --------------------------------------------------------------
          -- The three spatial face triangles are proper.
          --------------------------------------------------------------

          have hRKC :
              Not (PrimCollinear Geo R K C) := by
            intro hCol
            apply hRoff

            have hKCR :
                PrimCollinear Geo K C R := by
              cases hCol with
              | intro l hL =>
                exact
                  Exists.intro l
                    (And.intro hL.2.1
                      (And.intro hL.2.2 hL.1))

            exact
              hOnPlaneOfCollinear
                K C R
                hKC
                hKpi hCpi
                hKCR

          have hRCR2 :
              Not (PrimCollinear Geo R C R2) := by
            intro hCol
            apply hRoff

            have hCR2R :
                PrimCollinear Geo C R2 R := by
              cases hCol with
              | intro l hL =>
                exact
                  Exists.intro l
                    (And.intro hL.2.1
                      (And.intro hL.2.2 hL.1))

            exact
              hOnPlaneOfCollinear
                C R2 R
                hCR2
                hCpi hR2pi
                hCR2R

          have hRR2K :
              Not (PrimCollinear Geo R R2 K) := by
            intro hCol
            apply hRoff

            have hR2KR :
                PrimCollinear Geo R2 K R := by
              cases hCol with
              | intro l hL =>
                exact
                  Exists.intro l
                    (And.intro hL.2.1
                      (And.intro hL.2.2 hL.1))

            exact
              hOnPlaneOfCollinear
                R2 K R
                hR2K
                hR2pi hKpi
                hR2KR

          --------------------------------------------------------------
          -- Plane representatives of the normalized source triangles.
          --------------------------------------------------------------

          let Pp : PlanePoint Geo pi :=
            { val := P, property := hPpi }

          let Cp : PlanePoint Geo pi :=
            { val := C, property := hCpi }

          let R1p : PlanePoint Geo pi :=
            { val := R1, property := hR1pi }

          let R2p : PlanePoint Geo pi :=
            { val := R2, property := hR2pi }

          let R3p : PlanePoint Geo pi :=
            { val := R3, property := hR3pi }

          have hPCR1 :
              Not (PrimCollinear Geo P C R1) := by
            intro hCol
            apply hCPR1
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.1 hL.2.2))

          have hPCR2 :
              Not (PrimCollinear Geo P C R2) := by
            intro hCol
            apply hCPR2
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.1 hL.2.2))

          have hPCR3 :
              Not (PrimCollinear Geo P C R3) := by
            intro hCol
            apply hCPR3
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.1 hL.2.2))

          have hPCR1Plane :
              Not
                (PrimCollinear
                  (PlaneGeo Geo pi)
                  Pp Cp R1p) := by
            intro hCol
            apply hPCR1
            have h :=
              planeGeo_primCollinear_to_ambient
                (Geo := Geo)
                pi Pp Cp R1p hCol
            simpa [Pp, Cp, R1p] using h

          have hPCR2Plane :
              Not
                (PrimCollinear
                  (PlaneGeo Geo pi)
                  Pp Cp R2p) := by
            intro hCol
            apply hPCR2
            have h :=
              planeGeo_primCollinear_to_ambient
                (Geo := Geo)
                pi Pp Cp R2p hCol
            simpa [Pp, Cp, R2p] using h

          have hPCR3Plane :
              Not
                (PrimCollinear
                  (PlaneGeo Geo pi)
                  Pp Cp R3p) := by
            intro hCol
            apply hPCR3
            have h :=
              planeGeo_primCollinear_to_ambient
                (Geo := Geo)
                pi Pp Cp R3p hCol
            simpa [Pp, Cp, R3p] using h

          --------------------------------------------------------------
          -- Normalize the second lateral side in each SSS comparison.
          --------------------------------------------------------------

          have hPC_RC :
              Geo.Congruent P C R C :=
            hilbert_space_congruent_symmetry
              (Geo := Geo)
              R C
              P C
              hRC
              hRC_PC

          have hRC_PR1 :
              Geo.Congruent R C P R1 :=
            HilbertSpaceCongruence.segment_congruence_common
              (Geo := Geo)
              P C
              R C
              P R1
              hPC_RC
              hPC_PR1

          have hPC_RR2 :
              Geo.Congruent P C R R2 :=
            hilbert_space_congruent_symmetry
              (Geo := Geo)
              R R2
              P C
              hRR2
              hRR2_PC

          have hRR2_PR2 :
              Geo.Congruent R R2 P R2 :=
            HilbertSpaceCongruence.segment_congruence_common
              (Geo := Geo)
              P C
              R R2
              P R2
              hPC_RR2
              hPC_PR2

          have hPC_RK :
              Geo.Congruent P C R K :=
            hilbert_space_congruent_symmetry
              (Geo := Geo)
              R K
              P C
              hRK
              hRK_PC

          have hRK_PR3 :
              Geo.Congruent R K P R3 :=
            HilbertSpaceCongruence.segment_congruence_common
              (Geo := Geo)
              P C
              R K
              P R3
              hPC_RK
              hPC_PR3

          have hKC_CR1 :
              Geo.Congruent K C C R1 :=
            (Geometry.Geo.congruent_reverse_first
              Geo
              C K
              C R1).mp
              hCK_CR1

          have hCR2_CR2 :
              Geo.Congruent C R2 C R2 :=
            hilbert_space_congruent_reflexive
              (Geo := Geo)
              C R2 hCR2

          --------------------------------------------------------------
          -- SSS 1.
          --------------------------------------------------------------

          have hFirstNorm :
              Geo.AngleCongruent
                K R C
                C P R1 := by
            have h :=
              hilbert_space_sss_angleA_in_plane
                (Geo := Geo)
                pi
                R K C
                Pp Cp R1p
                hRKC
                hPCR1Plane
                hRK_PC
                hKC_CR1
                hRC_PR1
            simpa [Pp, Cp, R1p] using h

          have hCPR1_AOB :
              Geo.AngleCongruent
                C P R1
                A O B :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              A O B
              C P R1
              hAOB_CPR1

          have hFirst :
              Geo.AngleCongruent
                K R C
                A O B :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              K R C
              C P R1
              A O B
              hFirstNorm
              hCPR1_AOB

          --------------------------------------------------------------
          -- SSS 2.
          --------------------------------------------------------------

          have hSecondNorm :
              Geo.AngleCongruent
                C R R2
                C P R2 := by
            have h :=
              hilbert_space_sss_angleA_in_plane
                (Geo := Geo)
                pi
                R C R2
                Pp Cp R2p
                hRCR2
                hPCR2Plane
                hRC_PC
                hCR2_CR2
                hRR2_PR2
            simpa [Pp, Cp, R2p] using h

          have hCPR2_CPD :
              Geo.AngleCongruent
                C P R2
                C P D :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              C P D
              C P R2
              hCPD_CPR2

          have hSecond :
              Geo.AngleCongruent
                C R R2
                C P D :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              C R R2
              C P R2
              C P D
              hSecondNorm
              hCPR2_CPD

          --------------------------------------------------------------
          -- SSS 3.
          --------------------------------------------------------------

          have hThirdNorm :
              Geo.AngleCongruent
                R2 R K
                C P R3 := by
            have h :=
              hilbert_space_sss_angleA_in_plane
                (Geo := Geo)
                pi
                R R2 K
                Pp Cp R3p
                hRR2K
                hPCR3Plane
                hRR2_PC
                hR2K_CR3
                hRK_PR3
            simpa [Pp, Cp, R3p] using h

          have hCPR3_EQF :
              Geo.AngleCongruent
                C P R3
                E Q F :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              E Q F
              C P R3
              hEQF_CPR3

          have hThird :
              Geo.AngleCongruent
                R2 R K
                E Q F :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              R2 R K
              C P R3
              E Q F
              hThirdNorm
              hCPR3_EQF

          --------------------------------------------------------------
          -- Trihedral properness and Wyler plane uniqueness.
          --------------------------------------------------------------

          have hKRC :
              Not (PrimCollinear Geo K R C) := by
            intro hCol
            apply hRKC
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.1 hL.2.2))

          have hCRR2 :
              Not (PrimCollinear Geo C R R2) := by
            intro hCol
            apply hRCR2
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.1 hL.2.2))

          have hR2RK :
              Not (PrimCollinear Geo R2 R K) := by
            intro hCol
            apply hRR2K
            cases hCol with
            | intro l hL =>
              exact
                Exists.intro l
                  (And.intro hL.2.1
                    (And.intro hL.1 hL.2.2))

          have hNoCoplanar :
              Not
                (exists omega : S.Plane,
                  S.OnPlane R omega /\
                  S.OnPlane K omega /\
                  S.OnPlane C omega /\
                  S.OnPlane R2 omega) := by
            intro hCop
            cases hCop with
            | intro omega hOmega =>
              have hRomega : S.OnPlane R omega :=
                hOmega.1

              have hKomega : S.OnPlane K omega :=
                hOmega.2.1

              have hComega : S.OnPlane C omega :=
                hOmega.2.2.1

              have hR2omega : S.OnPlane R2 omega :=
                hOmega.2.2.2

              have homega_pi :
                  omega = pi :=
                W.plane_unique
                  C R2 K
                  hCR2K
                  omega pi
                  hComega hR2omega hKomega
                  hCpi hR2pi hKpi

              rw [homega_pi] at hRomega
              exact hRoff hRomega

          have hTri :
              HilbertTrihedralConfiguration
                Geo R K C R2 :=
            And.intro hKRC
              (And.intro hCRR2
                (And.intro hR2RK hNoCoplanar))

          have hRealizes :
              HilbertTrihedralRealizesThreeAngles
                Geo
                R K C R2
                A O B
                C P D
                E Q F :=
            hilbertTrihedralRealizesThreeAngles_intro
              Geo
              R K C R2
              A O B C P D E Q F
              hTri
              hFirst
              hSecond
              hThird

          exact
            hilbertThreeAnglesHaveTrihedralRealization_intro
              Geo
              A O B C P D E Q F
              R K C R2
              hRealizes


/--
Hilbert 3D corollary: the Wyler incidence package is first derived from
the Hilbert spatial environment, so no additional public geometric
axiom is assumed.
-/


theorem euclid_proposition_11_23_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo A O B C P D E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo C P D E Q F A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo E Q F A O B C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo A O B C P D E Q F) :
    HilbertThreeAnglesHaveTrihedralRealization
      Geo A O B C P D E Q F := by

  let W : HilbertWylerAxioms Geo :=
    hilbertWylerAxioms_of_hilbert3D
      (Geo := Geo)

  exact
    euclid_proposition_11_23_wyler_core
      (Geo := Geo)
      (W := W)
      A O B C P D E Q F
      h12_3 h23_1 h31_2 hFour

end Geometry

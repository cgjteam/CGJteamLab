import CGJteamLab.Hilbert3DInterface
import CGJteamLab.HilbertWylerAxioms

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Hilbert 3D -> Hilbert-Wyler compatibility

In genuine Hilbert 3D, the Hilbert-Wyler incidence package is derived
theory, not an additional axiom.

The common incidence fields are inherited from the Hilbert spatial
environment. The only nontrivial compatibility step is Wyler I.7:
Hilbert's three-dimensional plane-intersection theorem implies the
required exact intersection-line formulation.

No global instance is installed here. This avoids changing the global
typeclass graph and keeps the dependency direction explicit:

    Hilbert 3D -> Hilbert-Wyler.
-/

theorem hilbertWylerAxioms_of_hilbert3D
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo] :
    HilbertWylerAxioms Geo := by

  constructor

  case two_points_on_each_line =>
    exact HSI.two_points_on_each_line

  case three_noncollinear_on_plane =>
    exact
      hilbert_three_noncollinear_on_plane
        (Geo := Geo)

  case plane_through =>
    exact HSI.plane_through

  case plane_unique =>
    exact HSI.plane_unique

  case line_in_plane =>
    exact HSI.line_in_plane

  case wyler_i7_intersection_line =>
    intro pi a b hab hapi hbpi
      P hPpi
      alpha beta
      haalpha hPalpha
      hbbeta hPbeta

    have hAlphaBeta : Ne alpha beta := by
      intro hEq

      cases HSI.two_points_on_each_line a with
      | intro A hArest =>
        cases hArest with
        | intro Aprime hAdata =>
          have hAAprime : Ne A Aprime := hAdata.1
          have hAa : H.OnLine A a := hAdata.2.1
          have hAprimea : H.OnLine Aprime a := hAdata.2.2

          have hApi : S.OnPlane A pi :=
            hapi A hAa

          have hAprimepi : S.OnPlane Aprime pi :=
            hapi Aprime hAprimea

          have hAalpha : S.OnPlane A alpha :=
            haalpha A hAa

          have hAprimealpha : S.OnPlane Aprime alpha :=
            haalpha Aprime hAprimea

          cases HSI.two_points_on_each_line b with
          | intro B0 hB0rest =>
            cases hB0rest with
            | intro B1 hBdata =>
              have hB01 : Ne B0 B1 := hBdata.1
              have hB0b : H.OnLine B0 b := hBdata.2.1
              have hB1b : H.OnLine B1 b := hBdata.2.2

              have hBexists :
                  exists B : Geo.Point,
                    H.OnLine B b /\
                    Not (H.OnLine B a) := by
                by_cases hB0a : H.OnLine B0 a

                case pos =>
                  by_cases hB1a : H.OnLine B1 a

                  case pos =>
                    have hba : b = a :=
                      HP.line_unique
                        B0 B1 hB01
                        b a
                        hB0b hB1b
                        hB0a hB1a

                    exact False.elim (hab hba.symm)

                  case neg =>
                    exact
                      Exists.intro B1
                        (And.intro hB1b hB1a)

                case neg =>
                  exact
                    Exists.intro B0
                      (And.intro hB0b hB0a)

              cases hBexists with
              | intro B hBprops =>
                have hBb : H.OnLine B b :=
                  hBprops.1

                have hBa : Not (H.OnLine B a) :=
                  hBprops.2

                have hBpi : S.OnPlane B pi :=
                  hbpi B hBb

                have hBbeta : S.OnPlane B beta :=
                  hbbeta B hBb

                have hBalpha : S.OnPlane B alpha := by
                  rw [hEq]
                  exact hBbeta

                have hAAprimeB :
                    Not (PrimCollinear Geo A Aprime B) := by
                  intro hCol

                  have hBonA : H.OnLine B a :=
                    hilbert_on_line_of_primCollinear_with_two_on_line
                      (Geo := Geo)
                      hAAprime
                      hAa hAprimea
                      hCol

                  exact hBa hBonA

                have hPiAlpha : pi = alpha :=
                  HSI.plane_unique
                    A Aprime B
                    hAAprimeB
                    pi alpha
                    hApi hAprimepi hBpi
                    hAalpha hAprimealpha hBalpha

                apply hPpi
                rw [hPiAlpha]
                exact hPalpha

    cases
        hilbert_plane_intersection_line
          (Geo := Geo)
          alpha beta
          hAlphaBeta
          P
          hPalpha hPbeta with
    | intro m hmData =>
      have hCharacterization :
          forall X : Geo.Point,
            (S.OnPlane X alpha /\ S.OnPlane X beta) <->
              H.OnLine X m :=
        hmData.2.2.2

      exact
        Exists.intro m
          (fun X =>
            Iff.symm (hCharacterization X))

end Geometry

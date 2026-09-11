-- E4HyperplaneFrameCriterionDerived FIX4 - 2026-09-11
import CGJteamLab.E4AmbientXI4
import CGJteamLab.Coxeter.E4HyperplanePerpendicularFrame

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Derivation of the E4 hyperplane perpendicular-frame criterion

The historical class

    Hilbert4DHyperplanePerpendicularFrameCriterion_corrected

was introduced as a temporary four-dimensional orthogonality boundary.

It is in fact derivable from the corrected E4 incidence/order/congruence
layers and Euclid XI.4.

The proof uses XI.4 twice.

Given three independent hyperplane directions a,b,c through O:

1. a and b determine a plane N inside Sigma;
2. XI.4 gives l perpendicular to N;
3. for an arbitrary line m in Sigma through O, c and m determine a
   plane M inside Sigma;
4. local 3D incidence inside Sigma gives a second point common to N and M,
   hence a common line d through O;
5. since d lies in N, l is perpendicular to d;
6. XI.4 applied to c and d in M gives l perpendicular to M, hence to m.

No new axiom is introduced.
-/

/--
If four points are noncoplanar, then the first three are noncollinear.

This is the dimension-corrected ambient E4 incidence proof.  It uses no
ambient `HilbertSpaceIncidence Geo`.
-/
theorem hilbert4D_noncoplanar4_first_three_noncollinear_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (A B C D : Geo.Point)
    (hNoncop :
      Not (HilbertCoplanar4 Geo A B C D)) :
    Not (PrimCollinear Geo A B C) := by

  intro hABC

  rcases hABC with
    ⟨l, hAl, hBl, hCl⟩

  by_cases hDl : H.OnLine D l

  · rcases
        hilbert_point_off_line
          (Geo := Geo)
          l with
      ⟨P, hPl⟩

    rcases
        hilbert4D_plane_through_line_and_external_point
          (Geo := Geo)
          l P hPl with
      ⟨pi, hlpi, _hPpi⟩

    exact
      hNoncop
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hlpi D hDl⟩

  · rcases
        hilbert4D_plane_through_line_and_external_point
          (Geo := Geo)
          l D hDl with
      ⟨pi, hlpi, hDpi⟩

    exact
      hNoncop
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hDpi⟩


/--
The historical corrected E4 hyperplane frame criterion follows from
the ordinary corrected E4 incidence/order/congruence layers.

Thus it is not an independent axiom.
-/
theorem hilbert4D_hyperplanePerpendicularFrameCriterion_of_XI4
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo] :
    Hilbert4DHyperplanePerpendicularFrameCriterion_corrected Geo where

  normal_of_spanning_frame := by
    intro Sigma O l a b c
      hOl hFrame
      hPerpA hPerpB hPerpC

    rcases hFrame with
      ⟨haSigma,
       hbSigma,
       hcSigma,
       hOa,
       hOb,
       hOc,
       A, B, C,
       hAa,
       hBb,
       hCc,
       hNoncop⟩

    have hOSigma :
        Q.OnHyperplane O Sigma :=
      haSigma O hOa

    have hASigma :
        Q.OnHyperplane A Sigma :=
      haSigma A hAa

    have hBSigma :
        Q.OnHyperplane B Sigma :=
      hbSigma B hBb

    have hCSigma :
        Q.OnHyperplane C Sigma :=
      hcSigma C hCc

    have hOAB :
        Not (PrimCollinear Geo O A B) :=
      hilbert4D_noncoplanar4_first_three_noncollinear_corrected
        (Geo := Geo)
        O A B C
        hNoncop

    have hOA : Ne O A :=
      hilbert_noncollinear_ne_first
        (Geo := Geo)
        O A B
        hOAB

    have hOBA :
        Not (PrimCollinear Geo O B A) := by
      intro hCol
      exact
        hOAB
          (PrimCollinearRotate
            (Geo := Geo)
            O B A
            hCol)

    have hOB : Ne O B :=
      hilbert_noncollinear_ne_first
        (Geo := Geo)
        O B A
        hOBA

    have hab : Ne a b := by
      intro hab
      subst b
      exact
        hOAB
          ⟨a, hOa, hAa, hBb⟩

    rcases
        H4I.plane_through
          O A B
          hOAB with
      ⟨N, hON, hAN, hBN⟩

    have haN :
        HilbertLineInPlane Geo a N :=
      H4I.line_in_plane
        O A hOA
        a hOa hAa
        N hON hAN

    have hbN :
        HilbertLineInPlane Geo b N :=
      H4I.line_in_plane
        O B hOB
        b hOb hBb
        N hON hBN

    have hNSigma :
        HilbertPlaneInHyperplane4 Geo N Sigma :=
      H4L.plane_in_hyperplane
        O A B
        hOAB
        N
        hON hAN hBN
        Sigma
        hOSigma hASigma hBSigma

    have hCnotN :
        Not
          (Q.toHilbertSpacePrimitive.OnPlane C N) := by
      intro hCN

      exact
        hNoncop
          ⟨N,
           hON,
           hAN,
           hBN,
           hCN⟩

    have hPerpN :
        HilbertLinePerpendicularPlaneAt
          Geo l N O :=
      hilbert4D_XI4_line_perpendicular_plane_corrected
        (Geo := Geo)
        N
        a b l
        O
        hON
        haN hbN
        hOa hOb
        hab
        hOl
        hPerpA hPerpB

    refine
      ⟨hOl, hOSigma, ?_⟩

    intro m hmSigma hOm

    by_cases hmc : m = c

    · subst m
      exact hPerpC

    · let mSigma :
          HyperplaneLine4 Geo Sigma :=
        ⟨m, hmSigma⟩

      let cSigma :
          HyperplaneLine4 Geo Sigma :=
        ⟨c, hcSigma⟩

      let OSigma :
          HyperplanePoint4 Geo Sigma :=
        ⟨O, hOSigma⟩

      have hmcLocal :
          Ne mSigma cSigma := by
        intro hEq
        apply hmc
        exact
          congrArg
            (fun q : HyperplaneLine4 Geo Sigma => q.1)
            hEq

      have hOmLocal :
          HyperplaneOnLine4 Geo OSigma mSigma :=
        hOm

      have hOcLocal :
          HyperplaneOnLine4 Geo OSigma cSigma :=
        hOc

      rcases
          hilbert_plane_through_two_intersecting_lines
            (Geo := HyperplaneGeo4 Geo Sigma)
            mSigma cSigma
            hmcLocal
            OSigma
            hOmLocal hOcLocal with
        ⟨Mlocal,
         hmMlocal,
         hcMlocal,
         _hMunique⟩

      let M :
          Q.toHilbertSpacePrimitive.Plane :=
        Mlocal.1

      have hMSigma :
          HilbertPlaneInHyperplane4 Geo M Sigma :=
        Mlocal.2

      have hmM :
          HilbertLineInPlane Geo m M := by
        intro X hXm
        exact
          hmMlocal
            ⟨X, hmSigma X hXm⟩
            hXm

      have hcM :
          HilbertLineInPlane Geo c M := by
        intro X hXc
        exact
          hcMlocal
            ⟨X, hcSigma X hXc⟩
            hXc

      have hOM :
          Q.toHilbertSpacePrimitive.OnPlane O M :=
        hmM O hOm

      have hCM :
          Q.toHilbertSpacePrimitive.OnPlane C M :=
        hcM C hCc

      have hNM : Ne N M := by
        intro hNM
        apply hCnotN
        rw [hNM]
        exact hCM

      rcases
          H4L.plane_second_common_point_in_hyperplane
            Sigma
            N M
            hNSigma hMSigma
            hNM
            O
            hON hOM with
        ⟨R,
         hRO,
         hRN,
         hRM⟩

      rcases
          HilbertPlaneIncidence.line_through
            O R
            hRO.symm with
        ⟨d, hOd, hRd⟩

      have hdN :
          HilbertLineInPlane Geo d N :=
        H4I.line_in_plane
          O R
          hRO.symm
          d hOd hRd
          N hON hRN

      have hdM :
          HilbertLineInPlane Geo d M :=
        H4I.line_in_plane
          O R
          hRO.symm
          d hOd hRd
          M hOM hRM

      have hcd : Ne c d := by
        intro hcd
        subst d

        have hCN :
            Q.toHilbertSpacePrimitive.OnPlane C N :=
          hdN C hCc

        exact hCnotN hCN

      have hPerpD :
          HilbertLinesPerpendicularAt Geo l d O :=
        HilbertLinePerpendicularPlaneAt.perpendicular_to_line
          (Geo := Geo)
          hPerpN
          hdN
          hOd

      have hPerpM :
          HilbertLinePerpendicularPlaneAt
            Geo l M O :=
        hilbert4D_XI4_line_perpendicular_plane_corrected
          (Geo := Geo)
          M
          c d l
          O
          hOM
          hcM hdM
          hOc hOd
          hcd
          hOl
          hPerpC hPerpD

      exact
        HilbertLinePerpendicularPlaneAt.perpendicular_to_line
          (Geo := Geo)
          hPerpM
          hmM
          hOm

end Geometry

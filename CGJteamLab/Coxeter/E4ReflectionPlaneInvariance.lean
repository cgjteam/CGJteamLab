import CGJteamLab.HilbertDimensionFreeAffineCarriers
import CGJteamLab.Coxeter.E4NormalParallel

/-!
# Corrected E4 reflection invariance via Smith/Wyler

Production form of the reflection-invariance checkpoint.

The historical dependency on `AffineFlat4D_test80...` is deliberately
removed: this proof does not use any declaration from that module or
from the test76--test80 chain.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 refactor checkpoint 02: reflection invariance via Smith/Wyler carriers

This is the refactored form of test81.

The old proof manually chose two points on the normal line, proved a
noncollinearity statement, and invoked plane uniqueness to show that
the carrier plane of two parallel normals is the given plane N.

That entire incidence block is now replaced by the dimension-free
Smith/Wyler carrier theorem

  `hilbert_dimension_free_disjoint_coplanar_line_absorbed_by_plane`.

The E4-specific proof is therefore reduced to:

* reflection foot F and normal carrier l;
* F = O: same-foot normal uniqueness;
* F != O: XI.6 gives l parallel to the known normal r;
* the dimension-free carrier theorem puts l inside N.

All point-line-plane incidence is supplied by
`HilbertDimensionFreeIncidence`; the corrected E4 ambient incidence
instance is reconstructed by the compatibility bridge from refactor01.
-/

/--
Relational reflection invariance on the new Smith/Wyler-based E4
incidence architecture.
-/
theorem hilbert4D_reflection_relation_preserves_plane_of_normal_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (N : Q.toHilbertSpacePrimitive.Plane)
    (O : Geo.Point)
    (r : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (P P' : Geo.Point)
    (hPN :
      Q.toHilbertSpacePrimitive.OnPlane P N)
    (hRefl :
      IsHyperplaneReflection4_corrected
        Geo Sigma P P') :
    Q.toHilbertSpacePrimitive.OnPlane P' N := by

  rcases hRefl with hFixed | hOff

  case inl =>
    rw [hFixed.2]
    exact hPN

  case inr =>
    have hFootExists :=
      hOff.2

    let F : Geo.Point :=
      Classical.choose hFootExists

    have hFootData :=
      Classical.choose_spec hFootExists

    have hPerpThrough :
        PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P :=
      hFootData.1

    have hMid :
        HilbertIsMidpoint Geo F P P' :=
      hFootData.2

    have hCarrierExists :=
      hPerpThrough

    let l : Geo.Line :=
      Classical.choose hCarrierExists

    have hCarrierData :=
      Classical.choose_spec hCarrierExists

    have hPl :
        H.OnLine P l :=
      hCarrierData.1

    have hLNormal :
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo l Sigma F :=
      hCarrierData.2

    have hFl :
        H.OnLine F l :=
      hLNormal.1

    have hMidData :=
      H4O.between_incidence
        P F P'
        hMid.1

    have hPF :
        Ne P F :=
      hMidData.1

    have hColPFP' :
        PrimCollinear Geo P F P' :=
      hMidData.2.2.2.1

    have hP'l :
        H.OnLine P' l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hColPFP'

    by_cases hFO :
        F = O

    case pos =>
      have hLNormalO :
          HilbertLinePerpendicularHyperplaneAt4_corrected
            Geo l Sigma O :=
        Eq.mp
          (congrArg
            (fun X : Geo.Point =>
              HilbertLinePerpendicularHyperplaneAt4_corrected
                Geo l Sigma X)
            hFO)
          hLNormal

      have hlr :
          l = r :=
        hilbert4D_normal_same_foot_unique_corrected
          (Geo := Geo)
          Sigma
          l r
          O
          hLNormalO
          hRNormal

      have hP'r :
          H.OnLine P' r := by
        rw [<- hlr]
        exact hP'l

      exact
        hrN P' hP'r

    case neg =>
      have hPar :
          Hilbert4DLinesParallel_corrected
            Geo l r :=
        hilbert4D_normals_to_same_hyperplane_parallel_corrected
          (Geo := Geo)
          Sigma
          l r
          F O
          hFO
          hLNormal
          hRNormal

      let pi : Q.toHilbertSpacePrimitive.Plane :=
        Classical.choose hPar

      have hParPi :=
        Classical.choose_spec hPar

      have hlPi :
          HilbertLineInPlane Geo l pi :=
        hParPi.1

      have hrPi :
          HilbertLineInPlane Geo r pi :=
        hParPi.2.1

      have hDisjoint :
          HilbertLinesDisjoint Geo l r :=
        hParPi.2.2

      have hlN :
          HilbertLineInPlane Geo l N :=
        hilbert_dimension_free_disjoint_coplanar_line_absorbed_by_plane
          (Geo := Geo)
          N pi
          r l
          P
          hrN
          hrPi
          hlPi
          hPl
          hPN
          hDisjoint

      exact
        hlN P' hP'l


/--
Functional wrapper for the corrected hyperplane reflection.
-/
theorem hyperplaneReflect4_preserves_plane_of_normal_smith
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (N : Q.toHilbertSpacePrimitive.Plane)
    (O : Geo.Point)
    (r : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (P : Geo.Point)
    (hPN :
      Q.toHilbertSpacePrimitive.OnPlane P N) :
    Q.toHilbertSpacePrimitive.OnPlane
      (hyperplaneReflect4_corrected Geo Sigma P)
      N := by

  exact
    hilbert4D_reflection_relation_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma N O r
      hrN hRNormal
      P
      (hyperplaneReflect4_corrected Geo Sigma P)
      hPN
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P)

end Geometry

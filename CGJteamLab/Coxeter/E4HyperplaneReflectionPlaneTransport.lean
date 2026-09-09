import CGJteamLab.Coxeter.E4HyperplaneReflectionLineTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection: plane transport

Exact line transport is now available.  This module lifts it one
dimension higher.

The only genuinely new geometric ingredient is a planar transversal
lemma.  Let A,B,C be noncollinear points of a plane pi, with

  a = AB,
  b = AC.

For a point P of pi outside both a and b, extend AB beyond B to D.
The two lines PB and PD cannot both be disjoint from b: otherwise
Group IV, applied inside pi, would identify them, forcing P onto a.
Hence one of PB,PD meets b.

Thus there is a line through P containing

* a point T of a, and
* a point U of b,

with T != U.

Under exact line transport, the images of T and U already lie in the
target plane determined by the images of A,B,C.  Therefore the image
of the whole line TU, and in particular the image of P, lies in that
target plane.

No coordinates, vectors, scalar products, or numerical angle data are
used.
-/

/-! ## A source-plane transversal -/

/--
For a nondegenerate triangle A,B,C in pi, every point P of pi which is
on neither AB nor AC lies on a line joining a point of AB different
from A to a point of AC.

The proof uses corrected ambient Group IV only to exclude two distinct
parallels through P.
-/
theorem hilbert4D_plane_two_side_transversal_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [H4E : Hilbert4DAmbientEuclidean Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C P : Geo.Point)
    (hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hBpi :
      Q.toHilbertSpacePrimitive.OnPlane B pi)
    (hCpi :
      Q.toHilbertSpacePrimitive.OnPlane C pi)
    (hPpi :
      Q.toHilbertSpacePrimitive.OnPlane P pi)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (a b : Geo.Line)
    (hAa : H.OnLine A a)
    (hBa : H.OnLine B a)
    (hAb : H.OnLine A b)
    (hCb : H.OnLine C b)
    (hPa :
      Not (H.OnLine P a))
    (hPb :
      Not (H.OnLine P b)) :
    exists T U : Geo.Point,
      exists r : Geo.Line,
        Ne T U /\
        H.OnLine T a /\
        H.OnLine U b /\
        H.OnLine P r /\
        H.OnLine T r /\
        H.OnLine U r := by

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC :
      Ne A C := by
    intro hACeq
    apply hABC
    subst C

    exact
      Exists.intro a
        (And.intro hAa
          (And.intro hBa hAa))

  have hab :
      Ne a b := by

    intro habEq

    apply hABC

    exact
      Exists.intro a
        (And.intro hAa
          (And.intro hBa
            (by
              rw [habEq]
              exact hCb)))

  have hapi :
      HilbertLineInPlane Geo a pi :=
    D.line_in_plane
      A B hAB
      a hAa hBa
      pi hApi hBpi

  have hbpi :
      HilbertLineInPlane Geo b pi :=
    D.line_in_plane
      A C hAC
      b hAb hCb
      pi hApi hCpi

  have hDExists :=
    H4O.between_extension
      A B hAB

  let D0 : Geo.Point :=
    Classical.choose hDExists

  have hABD :
      Geo.Between A B D0 :=
    Classical.choose_spec hDExists

  have hABDData :=
    H4O.between_incidence
      A B D0 hABD

  have hBD :
      Ne B D0 :=
    hABDData.2.1

  have hAD :
      Ne A D0 :=
    hABDData.2.2.1

  have hDCol :
      PrimCollinear Geo A B D0 :=
    hABDData.2.2.2.1

  have hDa :
      H.OnLine D0 a :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAB
      hAa hBa
      hDCol

  have hDpi :
      Q.toHilbertSpacePrimitive.OnPlane D0 pi :=
    hapi D0 hDa

  have hPB :
      Ne P B := by
    intro hEq
    apply hPa
    rw [hEq]
    exact hBa

  have hPD :
      Ne P D0 := by
    intro hEq
    apply hPa
    rw [hEq]
    exact hDa

  have hPBLineExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      P B hPB

  let rB : Geo.Line :=
    Classical.choose hPBLineExists

  have hrBData :=
    Classical.choose_spec hPBLineExists

  have hPrB :
      H.OnLine P rB :=
    hrBData.1

  have hBrB :
      H.OnLine B rB :=
    hrBData.2

  have hrBpi :
      HilbertLineInPlane Geo rB pi :=
    D.line_in_plane
      P B hPB
      rB hPrB hBrB
      pi hPpi hBpi

  have hPDLineExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      P D0 hPD

  let rD : Geo.Line :=
    Classical.choose hPDLineExists

  have hrDData :=
    Classical.choose_spec hPDLineExists

  have hPrD :
      H.OnLine P rD :=
    hrDData.1

  have hDrD :
      H.OnLine D0 rD :=
    hrDData.2

  have hrDpi :
      HilbertLineInPlane Geo rD pi :=
    D.line_in_plane
      P D0 hPD
      rD hPrD hDrD
      pi hPpi hDpi

  have hNotBothDisjoint :
      Not
        (HilbertLinesDisjoint Geo rB b /\
         HilbertLinesDisjoint Geo rD b) := by

    intro hBoth

    have hrBD :
        rB = rD :=
      H4E.parallel_unique_in_plane
        pi
        b hbpi
        P hPpi hPb
        rB rD
        hrBpi hrDpi
        hPrB hBoth.1
        hPrD hBoth.2

    have hBa_rD :
        H.OnLine B rD := by
      rw [<- hrBD]
      exact hBrB

    have ha_rD :
        a = rD :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        B D0 hBD
        a rD
        hBa hDa
        hBa_rD hDrD

    apply hPa

    rw [ha_rD]
    exact hPrD

  have hChoice :
      (Not (HilbertLinesDisjoint Geo rB b)) \/
      (Not (HilbertLinesDisjoint Geo rD b)) := by

    by_cases hBdisj :
        HilbertLinesDisjoint Geo rB b

    case pos =>
      exact
        Or.inr
          (by
            intro hDdisj
            exact hNotBothDisjoint
              (And.intro hBdisj hDdisj))

    case neg =>
      exact Or.inl hBdisj

  cases hChoice with

  | inl hBnotDisj =>

      have hMeet :
          HilbertLinesMeet Geo rB b := by

        by_contra hNoMeet
        exact hBnotDisj hNoMeet

      let U : Geo.Point :=
        Classical.choose hMeet

      have hUData :=
        Classical.choose_spec hMeet

      have hUrB :
          H.OnLine U rB :=
        hUData.1

      have hUb :
          H.OnLine U b :=
        hUData.2

      have hBnotb :
          Not (H.OnLine B b) := by

        intro hBb

        have habEq :
            a = b :=
          HilbertPlaneIncidence.line_unique
            (Geo := Geo)
            A B hAB
            a b
            hAa hBa
            hAb hBb

        exact hab habEq

      have hBU :
          Ne B U := by

        intro hEq
        apply hBnotb
        rw [hEq]
        exact hUb

      exact
        Exists.intro B
          (Exists.intro U
            (Exists.intro rB
              (And.intro hBU
                (And.intro hBa
                  (And.intro hUb
                    (And.intro hPrB
                      (And.intro hBrB hUrB)))))))

  | inr hDnotDisj =>

      have hMeet :
          HilbertLinesMeet Geo rD b := by

        by_contra hNoMeet
        exact hDnotDisj hNoMeet

      let U : Geo.Point :=
        Classical.choose hMeet

      have hUData :=
        Classical.choose_spec hMeet

      have hUrD :
          H.OnLine U rD :=
        hUData.1

      have hUb :
          H.OnLine U b :=
        hUData.2

      have hDnotb :
          Not (H.OnLine D0 b) := by

        intro hDb

        have habEq :
            a = b :=
          HilbertPlaneIncidence.line_unique
            (Geo := Geo)
            A D0 hAD
            a b
            hAa hDa
            hAb hDb

        exact hab habEq

      have hDU :
          Ne D0 U := by

        intro hEq
        apply hDnotb
        rw [hEq]
        exact hUb

      exact
        Exists.intro D0
          (Exists.intro U
            (Exists.intro rD
              (And.intro hDU
                (And.intro hDa
                  (And.intro hUb
                    (And.intro hPrD
                      (And.intro hDrD hUrD)))))))


/-! ## Exact plane transport -/

/--
Exact setwise transport of one ambient 2-plane by corrected E4
hyperplane reflection.
-/
def HyperplaneReflectionMapsPlane4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Q.toHilbertSpacePrimitive.Plane) : Prop :=

  forall P : Geo.Point,
    Q.toHilbertSpacePrimitive.OnPlane P source <->
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma P)
        target


/--
One-way plane transport from a noncollinear marked triple.
-/
theorem hyperplaneReflectionMapsPlane4_corrected_forward_of_three_points
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [H4E : Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Q.toHilbertSpacePrimitive.Plane)
    (A B C : Geo.Point)
    (hAs :
      Q.toHilbertSpacePrimitive.OnPlane A source)
    (hBs :
      Q.toHilbertSpacePrimitive.OnPlane B source)
    (hCs :
      Q.toHilbertSpacePrimitive.OnPlane C source)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA't :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma A)
        target)
    (hB't :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma B)
        target)
    (hC't :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma C)
        target)
    (P : Geo.Point)
    (hPs :
      Q.toHilbertSpacePrimitive.OnPlane P source) :
    Q.toHilbertSpacePrimitive.OnPlane
      (hyperplaneReflect4_corrected Geo Sigma P)
      target := by

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC :
      Ne A C := by
    intro hEq
    apply hABC
    subst C

    have hLineExists :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB

    let q : Geo.Line :=
      Classical.choose hLineExists

    have hqData :=
      Classical.choose_spec hLineExists

    exact
      Exists.intro q
        (And.intro hqData.1
          (And.intro hqData.2 hqData.1))

  have haExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      A B hAB

  let a : Geo.Line :=
    Classical.choose haExists

  have haData :=
    Classical.choose_spec haExists

  have hAa :
      H.OnLine A a :=
    haData.1

  have hBa :
      H.OnLine B a :=
    haData.2

  have hbExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      A C hAC

  let b : Geo.Line :=
    Classical.choose hbExists

  have hbData :=
    Classical.choose_spec hbExists

  have hAb :
      H.OnLine A b :=
    hbData.1

  have hCb :
      H.OnLine C b :=
    hbData.2

  have hapi :
      HilbertLineInPlane Geo a source :=
    D.line_in_plane
      A B hAB
      a hAa hBa
      source hAs hBs

  have hbpi :
      HilbertLineInPlane Geo b source :=
    D.line_in_plane
      A C hAC
      b hAb hCb
      source hAs hCs

  let a' : Geo.Line :=
    hyperplaneReflectionLineCarrier4_corrected
      (Geo := Geo)
      Sigma a

  let b' : Geo.Line :=
    hyperplaneReflectionLineCarrier4_corrected
      (Geo := Geo)
      Sigma b

  have hMapA :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma a a' := by
    exact
      hyperplaneReflectionLineCarrier4_corrected_spec
        (Geo := Geo)
        Sigma a

  have hMapB :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma b b' := by
    exact
      hyperplaneReflectionLineCarrier4_corrected_spec
        (Geo := Geo)
        Sigma b

  have hA'a' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma A)
        a' :=
    (hMapA A).mp hAa

  have hB'a' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma B)
        a' :=
    (hMapA B).mp hBa

  have hA'b' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma A)
        b' :=
    (hMapB A).mp hAb

  have hC'b' :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma C)
        b' :=
    (hMapB C).mp hCb

  have hA'B' :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B) := by

    intro hEq
    apply hAB
    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  have hA'C' :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma C) := by

    intro hEq
    apply hAC
    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  have ha't :
      HilbertLineInPlane Geo a' target :=
    D.line_in_plane
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      hA'B'
      a' hA'a' hB'a'
      target hA't hB't

  have hb't :
      HilbertLineInPlane Geo b' target :=
    D.line_in_plane
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma C)
      hA'C'
      b' hA'b' hC'b'
      target hA't hC't

  by_cases hPa :
      H.OnLine P a

  case pos =>
    exact
      ha't
        (hyperplaneReflect4_corrected Geo Sigma P)
        ((hMapA P).mp hPa)

  case neg =>
    by_cases hPb :
        H.OnLine P b

    case pos =>
      exact
        hb't
          (hyperplaneReflect4_corrected Geo Sigma P)
          ((hMapB P).mp hPb)

    case neg =>
      have hTransExists :=
        hilbert4D_plane_two_side_transversal_corrected
          (Geo := Geo)
          source
          A B C P
          hAs hBs hCs hPs
          hABC
          a b
          hAa hBa hAb hCb
          hPa hPb

      let T : Geo.Point :=
        Classical.choose hTransExists

      have hUExists :=
        Classical.choose_spec hTransExists

      let U : Geo.Point :=
        Classical.choose hUExists

      have hrExists :=
        Classical.choose_spec hUExists

      let r : Geo.Line :=
        Classical.choose hrExists

      have hTransData :=
        Classical.choose_spec hrExists

      have hTU :
          Ne T U :=
        hTransData.1

      have hTa :
          H.OnLine T a :=
        hTransData.2.1

      have hUb :
          H.OnLine U b :=
        hTransData.2.2.1

      have hPr :
          H.OnLine P r :=
        hTransData.2.2.2.1

      have hTr :
          H.OnLine T r :=
        hTransData.2.2.2.2.1

      have hUr :
          H.OnLine U r :=
        hTransData.2.2.2.2.2

      have hT't :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma T)
            target :=
        ha't
          (hyperplaneReflect4_corrected Geo Sigma T)
          ((hMapA T).mp hTa)

      have hU't :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma U)
            target :=
        hb't
          (hyperplaneReflect4_corrected Geo Sigma U)
          ((hMapB U).mp hUb)

      let r' : Geo.Line :=
        hyperplaneReflectionLineCarrier4_corrected
          (Geo := Geo)
          Sigma r

      have hMapR :
          HyperplaneReflectionMapsLine4_corrected
            Geo Sigma r r' := by
        exact
          hyperplaneReflectionLineCarrier4_corrected_spec
            (Geo := Geo)
            Sigma r

      have hT'r' :
          H.OnLine
            (hyperplaneReflect4_corrected Geo Sigma T)
            r' :=
        (hMapR T).mp hTr

      have hU'r' :
          H.OnLine
            (hyperplaneReflect4_corrected Geo Sigma U)
            r' :=
        (hMapR U).mp hUr

      have hP'r' :
          H.OnLine
            (hyperplaneReflect4_corrected Geo Sigma P)
            r' :=
        (hMapR P).mp hPr

      have hT'U' :
          Ne
            (hyperplaneReflect4_corrected Geo Sigma T)
            (hyperplaneReflect4_corrected Geo Sigma U) := by

        intro hEq
        apply hTU
        exact
          (hyperplaneReflectionEquiv4_corrected
            Geo Sigma).injective hEq

      have hr't :
          HilbertLineInPlane Geo r' target :=
        D.line_in_plane
          (hyperplaneReflect4_corrected Geo Sigma T)
          (hyperplaneReflect4_corrected Geo Sigma U)
          hT'U'
          r' hT'r' hU'r'
          target hT't hU't

      exact
        hr't
          (hyperplaneReflect4_corrected Geo Sigma P)
          hP'r'


/--
Three noncollinear source points and their images in target force exact
setwise plane transport.
-/
theorem hyperplaneReflectionMapsPlane4_corrected_of_three_points
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Q.toHilbertSpacePrimitive.Plane)
    (A B C : Geo.Point)
    (hAs :
      Q.toHilbertSpacePrimitive.OnPlane A source)
    (hBs :
      Q.toHilbertSpacePrimitive.OnPlane B source)
    (hCs :
      Q.toHilbertSpacePrimitive.OnPlane C source)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA't :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma A)
        target)
    (hB't :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma B)
        target)
    (hC't :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma C)
        target) :
    HyperplaneReflectionMapsPlane4_corrected
      Geo Sigma source target := by

  intro P
  constructor

  case mp =>
    intro hPs

    exact
      hyperplaneReflectionMapsPlane4_corrected_forward_of_three_points
        (Geo := Geo)
        Sigma
        source target
        A B C
        hAs hBs hCs
        hABC
        hA't hB't hC't
        P hPs

  case mpr =>
    intro hP't

    have hImageNoncol :
        Not
          (PrimCollinear
            Geo
            (hyperplaneReflect4_corrected Geo Sigma A)
            (hyperplaneReflect4_corrected Geo Sigma B)
            (hyperplaneReflect4_corrected Geo Sigma C)) :=
      hyperplaneReflect4_corrected_preserves_noncollinear
        (Geo := Geo)
        Sigma A B C hABC

    have hBackA :
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma A))
          source := by

      simpa only [
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma A
      ] using hAs

    have hBackB :
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma B))
          source := by

      simpa only [
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma B
      ] using hBs

    have hBackC :
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma C))
          source := by

      simpa only [
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma C
      ] using hCs

    have hBack :=
      hyperplaneReflectionMapsPlane4_corrected_forward_of_three_points
        (Geo := Geo)
        Sigma
        target source
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma C)
        hA't hB't hC't
        hImageNoncol
        hBackA hBackB hBackC
        (hyperplaneReflect4_corrected Geo Sigma P)
        hP't

    simpa only [
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma P
    ] using hBack


/--
Every ambient plane has an exact image plane.
-/
theorem hyperplaneReflectionMapsPlane4_corrected_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Q.toHilbertSpacePrimitive.Plane) :
    exists target : Q.toHilbertSpacePrimitive.Plane,
      HyperplaneReflectionMapsPlane4_corrected
        Geo Sigma source target := by

  have hABCExists :=
    D.three_noncollinear_on_plane source

  let A : Geo.Point :=
    Classical.choose hABCExists

  have hBCExists :=
    Classical.choose_spec hABCExists

  let B : Geo.Point :=
    Classical.choose hBCExists

  have hCExists :=
    Classical.choose_spec hBCExists

  let C : Geo.Point :=
    Classical.choose hCExists

  have hABCData :=
    Classical.choose_spec hCExists

  have hAs :=
    hABCData.1

  have hBs :=
    hABCData.2.1

  have hCs :=
    hABCData.2.2.1

  have hABC :=
    hABCData.2.2.2

  have hImageNoncol :
      Not
        (PrimCollinear
          Geo
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma B)
          (hyperplaneReflect4_corrected Geo Sigma C)) :=
    hyperplaneReflect4_corrected_preserves_noncollinear
      (Geo := Geo)
      Sigma A B C hABC

  have hTargetExists :=
    D.plane_through
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C)
      hImageNoncol

  let target : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hTargetExists

  have hTargetData :=
    Classical.choose_spec hTargetExists

  exact
    Exists.intro target
      (hyperplaneReflectionMapsPlane4_corrected_of_three_points
        (Geo := Geo)
        Sigma
        source target
        A B C
        hAs hBs hCs
        hABC
        hTargetData.1
        hTargetData.2.1
        hTargetData.2.2)


/--
The exact image plane is unique.
-/
theorem hyperplaneReflectionMapsPlane4_corrected_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target1 target2 :
      Q.toHilbertSpacePrimitive.Plane)
    (hMap1 :
      HyperplaneReflectionMapsPlane4_corrected
        Geo Sigma source target1)
    (hMap2 :
      HyperplaneReflectionMapsPlane4_corrected
        Geo Sigma source target2) :
    target1 = target2 := by

  have hABCExists :=
    D.three_noncollinear_on_plane source

  let A : Geo.Point :=
    Classical.choose hABCExists

  have hBCExists :=
    Classical.choose_spec hABCExists

  let B : Geo.Point :=
    Classical.choose hBCExists

  have hCExists :=
    Classical.choose_spec hBCExists

  let C : Geo.Point :=
    Classical.choose hCExists

  have hABCData :=
    Classical.choose_spec hCExists

  have hImageNoncol :
      Not
        (PrimCollinear
          Geo
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma B)
          (hyperplaneReflect4_corrected Geo Sigma C)) :=
    hyperplaneReflect4_corrected_preserves_noncollinear
      (Geo := Geo)
      Sigma A B C
      hABCData.2.2.2

  exact
    D.plane_unique
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      (hyperplaneReflect4_corrected Geo Sigma C)
      hImageNoncol
      target1 target2
      ((hMap1 A).mp hABCData.1)
      ((hMap1 B).mp hABCData.2.1)
      ((hMap1 C).mp hABCData.2.2.1)
      ((hMap2 A).mp hABCData.1)
      ((hMap2 B).mp hABCData.2.1)
      ((hMap2 C).mp hABCData.2.2.1)


/--
Canonical exact image plane.
-/
noncomputable def hyperplaneReflectionPlaneCarrier4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Q.toHilbertSpacePrimitive.Plane) :
    Q.toHilbertSpacePrimitive.Plane :=

  Classical.choose
    (hyperplaneReflectionMapsPlane4_corrected_exists
      (Geo := Geo)
      Sigma source)


/--
Specification of the canonical image plane.
-/
theorem hyperplaneReflectionPlaneCarrier4_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Q.toHilbertSpacePrimitive.Plane) :
    HyperplaneReflectionMapsPlane4_corrected
      Geo Sigma source
      (hyperplaneReflectionPlaneCarrier4_corrected
        (Geo := Geo)
        Sigma source) :=

  Classical.choose_spec
    (hyperplaneReflectionMapsPlane4_corrected_exists
      (Geo := Geo)
      Sigma source)


/--
Any exact target is the canonical image plane.
-/
theorem hyperplaneReflectionPlaneCarrier4_corrected_eq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target :
      Q.toHilbertSpacePrimitive.Plane)
    (hMap :
      HyperplaneReflectionMapsPlane4_corrected
        Geo Sigma source target) :
    hyperplaneReflectionPlaneCarrier4_corrected
        (Geo := Geo)
        Sigma source =
      target := by

  exact
    hyperplaneReflectionMapsPlane4_corrected_unique
      (Geo := Geo)
      Sigma
      source
      (hyperplaneReflectionPlaneCarrier4_corrected
        (Geo := Geo)
        Sigma source)
      target
      (hyperplaneReflectionPlaneCarrier4_corrected_spec
        (Geo := Geo)
        Sigma source)
      hMap


/--
Exact plane transport reverses under the same involutive reflection.
-/
theorem hyperplaneReflectionMapsPlane4_corrected_symm
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target :
      Q.toHilbertSpacePrimitive.Plane)
    (hMap :
      HyperplaneReflectionMapsPlane4_corrected
        Geo Sigma source target) :
    HyperplaneReflectionMapsPlane4_corrected
      Geo Sigma target source := by

  intro P
  constructor

  case mp =>
    intro hPt

    have hDoubleTarget :
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P))
          target := by

      simpa only [
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma P
      ] using hPt

    exact
      (hMap
        (hyperplaneReflect4_corrected Geo Sigma P)).mpr
        hDoubleTarget

  case mpr =>
    intro hPs

    have hDoubleTarget :
        Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P))
          target :=
      (hMap
        (hyperplaneReflect4_corrected Geo Sigma P)).mp
        hPs

    simpa only [
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma P
    ] using hDoubleTarget


/--
Canonical plane transport is involutive.
-/
theorem hyperplaneReflectionPlaneCarrier4_corrected_involutive
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Q.toHilbertSpacePrimitive.Plane) :
    hyperplaneReflectionPlaneCarrier4_corrected
        (Geo := Geo)
        Sigma
        (hyperplaneReflectionPlaneCarrier4_corrected
          (Geo := Geo)
          Sigma source) =
      source := by

  have hForward :=
    hyperplaneReflectionPlaneCarrier4_corrected_spec
      (Geo := Geo)
      Sigma source

  have hBackward :=
    hyperplaneReflectionMapsPlane4_corrected_symm
      (Geo := Geo)
      Sigma
      source
      (hyperplaneReflectionPlaneCarrier4_corrected
        (Geo := Geo)
        Sigma source)
      hForward

  exact
    hyperplaneReflectionPlaneCarrier4_corrected_eq
      (Geo := Geo)
      Sigma
      (hyperplaneReflectionPlaneCarrier4_corrected
        (Geo := Geo)
        Sigma source)
      source
      hBackward

end Geometry

import CGJteamLab.Wyler.Hilbert3DWyler
import CGJteamLab.Wyler.HilbertWylerMetric
import CGJteamLab.Wyler.HilbertWylerParallel
import CGJteamLab.Wyler.HilbertWylerEuclidean
import CGJteamLab.Wyler.HilbertWylerPlanes

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler interface extracted from Euclid Book XI

This is the first consolidated interface produced from the flat-native
laboratory for Euclid XI.1-XI.14.

The theorem bodies below are copied from the individually compiled native
laboratory files, in proposition order.  The purpose of this version is
structural consolidation: replace fourteen experimental modules by one
module before dependency inversion and API renaming.

Current dependency status:

* `Hilbert3DWyler` supplies the pure 3D flat/span/join/meet calculus.
* `Proposition11_14` is still imported transitively to expose lower metric,
  order, Euclidean, and construction helpers developed during Book XI.
* No `*_native` laboratory module is imported by this file.

The next refactoring phase is to move genuinely reusable lower helpers out
of the numbered `Proposition11_*` modules.  The final intended dependency is

  Hilbert3DWyler
        |
        v
  HilbertWylerInterface
        |
        v
  Proposition11_n

rather than the temporary dependency on `Proposition11_14` used here.
-/


/-! ================================================================
    Book XI laboratory extraction: XI.1
    ================================================================ -/
/-!
# Euclid XI.1 in flat-native form

The point of this experiment is not to rename the old incidence theorem.

The flat proof factors XI.1 into two independent closure statements:

1. if A and B lie in a plane pi, then Span{A,B} lies in pi;
2. if A and B are distinct points of a line l, then the whole line l
   lies in Span{A,B}.

Combining the two gives Euclid XI.1.

Importantly, this proof does NOT require `HilbertPlaneIncidence Geo`.
The stronger exact identity

  Span{A,B} = carrier(l)

does require that extra interface in the current library, but XI.1 itself
does not need the exact identity.
-/

/--
Pair-span closure inside a plane.

Distinctness of A and B is irrelevant here.
-/
theorem euclid_XI1_pair_span_subset_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A B : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi) :
    Set.Subset
      (HilbertSpan3D Geo ({A, B} : Set Geo.Point))
      (HilbertPlaneCarrier3D Geo pi) := by

  apply
    hilbertSpan3D_least
      (Geo := Geo)
      ({A, B} : Set Geo.Point)
      (HilbertPlaneCarrier3D Geo pi)

  exact
    hilbertPlaneCarrier3D_flat
      (Geo := Geo) pi

  intro X hX
  change S.OnPlane X pi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX

  rcases hX with hXA | hXB

  next =>
    subst X
    exact hApi

  next =>
    subst X
    exact hBpi


/--
A line through two distinct generators is contained in their span.

This is the rank-one lower inclusion needed by XI.1.  It uses only the
line-closure clause of `HilbertFlat3D`.
-/
theorem euclid_XI1_lineCarrier_subset_pair_span
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l) :
    Set.Subset
      (HilbertLineCarrier3D Geo l)
      (HilbertSpan3D Geo ({A, B} : Set Geo.Point)) := by

  have hAspan :
      HilbertSpan3D Geo ({A, B} : Set Geo.Point) A := by
    apply
      hilbertSpan3D_extensive
        (Geo := Geo)
        ({A, B} : Set Geo.Point)
    simp

  have hBspan :
      HilbertSpan3D Geo ({A, B} : Set Geo.Point) B := by
    apply
      hilbertSpan3D_extensive
        (Geo := Geo)
        ({A, B} : Set Geo.Point)
    simp

  have hSpanFlat :
      HilbertFlat3D Geo
        (HilbertSpan3D Geo ({A, B} : Set Geo.Point)) :=
    hilbertSpan3D_flat
      (Geo := Geo)
      ({A, B} : Set Geo.Point)

  intro X hXl
  change H.OnLine X l at hXl

  exact
    hSpanFlat.1
      A B
      hAspan hBspan
      hAB
      l hAl hBl
      X hXl


/--
Euclid XI.1 reconstructed purely through the flat calculus.

The assumptions are exactly the old XI.1 assumptions; no
`HilbertPlaneIncidence Geo` instance is added.
-/
theorem euclid_proposition_11_1_via_flats
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi) :
    HilbertLineInPlane Geo l pi := by

  have hLineSpan :
      Set.Subset
        (HilbertLineCarrier3D Geo l)
        (HilbertSpan3D Geo ({A, B} : Set Geo.Point)) :=
    euclid_XI1_lineCarrier_subset_pair_span
      (Geo := Geo)
      l A B
      hAB hAl hBl

  have hSpanPlane :
      Set.Subset
        (HilbertSpan3D Geo ({A, B} : Set Geo.Point))
        (HilbertPlaneCarrier3D Geo pi) :=
    euclid_XI1_pair_span_subset_plane
      (Geo := Geo)
      pi A B
      hApi hBpi

  intro X hXl

  exact
    hSpanPlane
      (hLineSpan hXl)


/-! ================================================================
    Book XI laboratory extraction: XI.2
    ================================================================ -/
/-!
# Euclid XI.2 in flat-native form

The classical statement has two clauses:

1. two distinct intersecting lines lie in one plane;
2. every nondegenerate triangle lies in one plane.

In flat language the natural statements are stronger and more structural:

1. the join of the two line carriers is exactly a plane carrier;
2. the span of the three noncollinear vertices is exactly a plane carrier.

Thus XI.2 becomes a rank-two generation theorem.
-/

/--
Flat-native first clause of Euclid XI.2.

Two distinct intersecting lines do not merely lie in a common plane:
their join is exactly that plane.
-/
theorem euclid_proposition_11_2_via_join
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (P : Geo.Point)
    (hlm : Ne l m)
    (hPl : H.OnLine P l)
    (hPm : H.OnLine P m) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo m pi /\
      HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo l)
        (HilbertLineCarrier3D Geo m) =
      HilbertPlaneCarrier3D Geo pi := by

  exact
    hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
      (Geo := Geo)
      l m P
      hlm hPl hPm


/--
Flat-native second clause of Euclid XI.2.

Three noncollinear points do not merely lie in some plane:
their span is exactly the carrier of a plane.
-/
theorem euclid_proposition_11_2_triangle_via_span
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists pi : S.Plane,
      HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) =
      HilbertPlaneCarrier3D Geo pi := by

  cases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B C hABC with
  | intro pi hData =>
      have hApi : S.OnPlane A pi :=
        hData.1

      have hBpi : S.OnPlane B pi :=
        hData.2.1

      have hCpi : S.OnPlane C pi :=
        hData.2.2

      exact
        Exists.intro pi
          (hilbertSpan3D_triple_eq_planeCarrier
            (Geo := Geo)
            A B C pi
            hABC
            hApi hBpi hCpi)


/--
The classical first clause recovered from the flat-native join theorem.

This is intentionally included only as a comparison endpoint.
-/
theorem euclid_proposition_11_2_from_join
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (P : Geo.Point)
    (hlm : Ne l m)
    (hPl : H.OnLine P l)
    (hPm : H.OnLine P m) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo m pi := by

  cases
      euclid_proposition_11_2_via_join
        (Geo := Geo)
        l m P hlm hPl hPm with
  | intro pi hData =>
      exact
        Exists.intro pi
          (And.intro hData.1 hData.2.1)


/--
The classical triangle clause recovered from the exact span statement.
-/
theorem euclid_proposition_11_2_triangle_from_span
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists pi : S.Plane,
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi := by

  cases
      euclid_proposition_11_2_triangle_via_span
        (Geo := Geo)
        A B C hABC with
  | intro pi hSpan =>
      have hExt :=
        hilbertSpan3D_extensive
          (Geo := Geo)
          ({A, B, C} : Set Geo.Point)

      have hAspan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) A := by
        apply hExt
        simp

      have hBspan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) B := by
        apply hExt
        simp

      have hCspan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) C := by
        apply hExt
        simp

      have hApi : S.OnPlane A pi := by
        change HilbertPlaneCarrier3D Geo pi A
        simpa [hSpan] using hAspan

      have hBpi : S.OnPlane B pi := by
        change HilbertPlaneCarrier3D Geo pi B
        simpa [hSpan] using hBspan

      have hCpi : S.OnPlane C pi := by
        change HilbertPlaneCarrier3D Geo pi C
        simpa [hSpan] using hCspan

      exact
        Exists.intro pi
          (And.intro hApi
            (And.intro hBpi hCpi))


/-! ================================================================
    Book XI laboratory extraction: XI.3
    ================================================================ -/
/-!
# Euclid XI.3 in flat-native form

Classically XI.3 says that two distinct planes with a common point
intersect in a straight line.

In the flat language the natural conclusion is an exact meet identity:

  carrier(pi) inter carrier(rho) = carrier(l).

The common point selects the nonempty branch of the general plane-meet
dichotomy.
-/

/--
Flat-native Euclid XI.3.

Two distinct planes with a common point have a meet equal to a line
carrier.
-/
theorem euclid_proposition_11_3_via_meet
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo l rho /\
      Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      HilbertLineCarrier3D Geo l := by

  exact
    hilbertPlaneCarrier3D_inter_eq_lineCarrier
      (Geo := Geo)
      pi rho hneq
      A hApi hArho


/--
Classical XI.3 recovered from the exact meet identity.

The extensional pointwise statement is now a corollary of the flat
equality rather than the primary structural conclusion.
-/
theorem euclid_proposition_11_3_from_meet
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo l rho /\
      forall X : Geo.Point,
        (S.OnPlane X pi /\ S.OnPlane X rho) <->
        H.OnLine X l := by

  cases
      euclid_proposition_11_3_via_meet
        (Geo := Geo)
        pi rho hneq
        A hApi hArho with
  | intro l hData =>
      have hAl := hData.1
      have hlpi := hData.2.1
      have hlrho := hData.2.2.1
      have hMeet := hData.2.2.2

      refine
        Exists.intro l
          (And.intro hAl
            (And.intro hlpi
              (And.intro hlrho ?_)))

      intro X

      have hPointEq :
          Set.inter
              (HilbertPlaneCarrier3D Geo pi)
              (HilbertPlaneCarrier3D Geo rho) X <->
          HilbertLineCarrier3D Geo l X := by
        rw [hMeet]

      exact hPointEq


/--
XI.3 viewed through the complete meet dichotomy.

The common point rules out the empty branch, leaving the line branch.
This theorem is included to exercise the new general XI.14-era meet API.
-/
theorem euclid_proposition_11_3_via_meet_dichotomy
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      HilbertLineCarrier3D Geo l := by

  have hCases :=
    hilbertPlaneCarrier3D_inter_eq_empty_or_lineCarrier
      (Geo := Geo)
      pi rho hneq

  cases hCases with
  | inl hEmpty =>
      have hAInter :
          Set.inter
            (HilbertPlaneCarrier3D Geo pi)
            (HilbertPlaneCarrier3D Geo rho) A := by
        exact And.intro hApi hArho

      have hFalse :
          (fun _ => False : Set Geo.Point) A := by
        rw [<- hEmpty]
        exact hAInter

      exact False.elim hFalse

  | inr hLine =>
      exact hLine


/-! ================================================================
    Book XI laboratory extraction: XI.4
    ================================================================ -/
/-!
# Euclid XI.4 in flat-native form

The metric content of XI.4 is unchanged:

  l perpendicular m at O
  l perpendicular n at O

implies

  l perpendicular pi at O.

The incidence configuration is changed.

Instead of supplying `m` and `n` as `PlaneLine Geo pi`, the plane is
specified by the structural equation

  join(carrier(m), carrier(n)) = carrier(pi).

Containment of the generators in `pi` is recovered from this equation.
The incidences O in m and O in n are already contained in the two
line-line perpendicularity hypotheses.
-/

/--
Flat-native Euclid XI.4.

Two distinct ambient lines generate the plane `pi`.  If a third line is
perpendicular to both generators at their common point, it is
perpendicular to the generated plane.
-/
theorem euclid_proposition_11_4_via_join_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n l : Geo.Line)
    (O : Geo.Point)
    (hmn : Ne m n)
    (hJoin :
      HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo m)
        (HilbertLineCarrier3D Geo n) =
      HilbertPlaneCarrier3D Geo pi)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m O)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n O) :
    HilbertLinePerpendicularPlaneAt Geo l pi O := by

  have hGen :=
    hilbertJoin3D_generators_subset_of_eq
      (Geo := Geo)
      (HilbertLineCarrier3D Geo m)
      (HilbertLineCarrier3D Geo n)
      (HilbertPlaneCarrier3D Geo pi)
      hJoin

  have hmpi :
      HilbertLineInPlane Geo m pi := by
    intro X hXm
    exact hGen.1 hXm

  have hnpi :
      HilbertLineInPlane Geo n pi := by
    intro X hXn
    exact hGen.2 hXn

  have hOm : H.OnLine O m :=
    hPerpM.2.1

  have hOn : H.OnLine O n :=
    hPerpN.2.1

  have hOpi : S.OnPlane O pi :=
    hmpi O hOm

  let mPi : PlaneLine Geo pi :=
    Subtype.mk m hmpi

  let nPi : PlaneLine Geo pi :=
    Subtype.mk n hnpi

  let OPi : PlanePoint Geo pi :=
    Subtype.mk O hOpi

  have hmPi_nPi : Ne mPi nPi := by
    intro hEq
    apply hmn
    exact congrArg Subtype.val hEq

  have hlm : Ne l m := by
    exact
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        l m O
        hPerpM

  have hln : Ne l n := by
    exact
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        l n O
        hPerpN

  have hOl : H.OnLine O l :=
    hPerpM.1

  exact
    hilbert_XI4_line_perpendicular_plane_core
      (Geo := Geo)
      pi
      mPi nPi
      l
      OPi
      hmPi_nPi
      hlm hln
      hOl hOm hOn
      hPerpM
      hPerpN


/--
XI.4 with the generating plane constructed from the two intersecting
perpendicular generators.

This version starts only with the ambient lines and their common point.
The flat calculus constructs the rank-two carrier before the metric
XI.4 step.
-/
theorem euclid_proposition_11_4_via_generated_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (m n l : Geo.Line)
    (O : Geo.Point)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m O)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n O) :
    exists pi : S.Plane,
      HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo m)
        (HilbertLineCarrier3D Geo n) =
      HilbertPlaneCarrier3D Geo pi /\
      HilbertLinePerpendicularPlaneAt Geo l pi O := by

  have hOm : H.OnLine O m :=
    hPerpM.2.1

  have hOn : H.OnLine O n :=
    hPerpN.2.1

  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        m n O
        hmn hOm hOn with
  | intro pi hData =>
      have hJoin := hData.2.2

      have hPerpPlane :
          HilbertLinePerpendicularPlaneAt Geo l pi O :=
        euclid_proposition_11_4_via_join_native
          (Geo := Geo)
          pi m n l O
          hmn hJoin
          hPerpM hPerpN

      exact
        Exists.intro pi
          (And.intro hJoin hPerpPlane)


/-! ================================================================
    Book XI laboratory extraction: XI.5
    ================================================================ -/
/-!
# Euclid XI.5 in flat-native form

Classically XI.5 concludes that three lines m,n,p are coplanar when
one line l is perpendicular to all three at the common point O and
m != n.

The native flat statement is sharper:

  carrier(p) subset join(carrier(m), carrier(n)).

Thus m and n are the generators.  The third perpendicular line p adds
no new flat rank.

The proof uses:

  pi    = join(m,n)
  sigma = join(l,p)
  q     = meet(pi,sigma)

and the native join form of XI.4.
-/

/--
A line perpendicular to a plane at a point cannot itself lie in that
plane.

This is metric infrastructure, not a pure flat-incidence theorem.
-/
theorem wyler_XI5_linePerpendicularPlaneAt_not_in_plane_native
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l : Geo.Line)
    (pi : S.Plane)
    (O : Geo.Point)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi O) :
    Not (HilbertLineInPlane Geo l pi) := by

  intro hlpi

  have hSelf :
      HilbertLinesPerpendicularAt Geo l l O :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp
      hlpi
      hPerp.1

  exact
    (hilbert_linesPerpendicularAt_ne
      Geo l l O hSelf) rfl


/--
Flat-native Euclid XI.5.

If l is perpendicular at O to m,n,p and m != n, then p is contained in
the join generated by m and n.

Equivalently: adding p does not increase the rank-two flat generated by
m and n.
-/
theorem euclid_proposition_11_5_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m n p : Geo.Line)
    (O : Geo.Point)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m O)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n O)
    (hPerpP :
      HilbertLinesPerpendicularAt Geo l p O) :
    Set.Subset
      (HilbertLineCarrier3D Geo p)
      (HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo m)
        (HilbertLineCarrier3D Geo n)) := by

  have hOl : H.OnLine O l :=
    hPerpM.1

  have hOm : H.OnLine O m :=
    hPerpM.2.1

  have hOn : H.OnLine O n :=
    hPerpN.2.1

  have hOp : H.OnLine O p :=
    hPerpP.2.1

  ----------------------------------------------------------------------
  -- First generated plane: pi = m join n.
  ----------------------------------------------------------------------

  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        m n O
        hmn hOm hOn with
  | intro pi hPiData =>

      have hJoinPi := hPiData.2.2

      have hGenPi :=
        hilbertJoin3D_generators_subset_of_eq
          (Geo := Geo)
          (HilbertLineCarrier3D Geo m)
          (HilbertLineCarrier3D Geo n)
          (HilbertPlaneCarrier3D Geo pi)
          hJoinPi

      have hmpi :
          HilbertLineInPlane Geo m pi := by
        intro X hXm
        exact hGenPi.1 hXm

      have hOpi : S.OnPlane O pi :=
        hmpi O hOm

      have hlPerpPi :
          HilbertLinePerpendicularPlaneAt
            Geo l pi O :=
        euclid_proposition_11_4_via_join_native
          (Geo := Geo)
          pi m n l O
          hmn
          hJoinPi
          hPerpM hPerpN

      ------------------------------------------------------------------
      -- Either p is already in pi, or build sigma = l join p.
      ------------------------------------------------------------------

      by_cases hppi :
          HilbertLineInPlane Geo p pi

      next =>
        intro X hXp
        change H.OnLine X p at hXp
        rw [hJoinPi]
        exact hppi X hXp

      next =>
        have hlp : Ne l p :=
          hilbert_linesPerpendicularAt_ne
            Geo l p O hPerpP

        cases
            hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
              (Geo := Geo)
              l p O
              hlp hOl hOp with
        | intro sigma hSigmaData =>

            have hJoinSigma := hSigmaData.2.2

            have hGenSigma :=
              hilbertJoin3D_generators_subset_of_eq
                (Geo := Geo)
                (HilbertLineCarrier3D Geo l)
                (HilbertLineCarrier3D Geo p)
                (HilbertPlaneCarrier3D Geo sigma)
                hJoinSigma

            have hlsigma :
                HilbertLineInPlane Geo l sigma := by
              intro X hXl
              exact hGenSigma.1 hXl

            have hpsigma :
                HilbertLineInPlane Geo p sigma := by
              intro X hXp
              exact hGenSigma.2 hXp

            have hOsigma : S.OnPlane O sigma :=
              hlsigma O hOl

            have hPiSigma : Ne pi sigma := by
              intro hEq
              apply hppi
              intro X hXp
              rw [hEq]
              exact hpsigma X hXp

            ------------------------------------------------------------
            -- Meet: q = pi meet sigma.
            ------------------------------------------------------------

            cases
                hilbertPlaneCarrier3D_inter_eq_lineCarrier
                  (Geo := Geo)
                  pi sigma
                  hPiSigma
                  O hOpi hOsigma with
            | intro q hQData =>

                have hOq := hQData.1
                have hqpi := hQData.2.1
                have hqsigma := hQData.2.2.1

                have hPerpQ :
                    HilbertLinesPerpendicularAt Geo l q O :=
                  HilbertLinePerpendicularPlaneAt.perpendicular_to_line
                    (Geo := Geo)
                    hlPerpPi
                    hqpi
                    hOq

                --------------------------------------------------------
                -- If p != q, then p and q generate sigma.  Native XI.4
                -- would make l perpendicular to sigma, impossible since
                -- l itself lies in sigma.
                --------------------------------------------------------

                have hpq : p = q := by
                  by_contra hpq

                  have hJoinPQ :
                      HilbertJoin3D Geo
                        (HilbertLineCarrier3D Geo p)
                        (HilbertLineCarrier3D Geo q) =
                      HilbertPlaneCarrier3D Geo sigma :=
                    hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
                      (Geo := Geo)
                      sigma p q
                      hpq
                      hpsigma hqsigma

                  have hlPerpSigma :
                      HilbertLinePerpendicularPlaneAt
                        Geo l sigma O :=
                    euclid_proposition_11_4_via_join_native
                      (Geo := Geo)
                      sigma p q l O
                      hpq
                      hJoinPQ
                      hPerpP hPerpQ

                  exact
                    (wyler_XI5_linePerpendicularPlaneAt_not_in_plane_native
                      (Geo := Geo)
                      l sigma O
                      hlPerpSigma)
                      hlsigma

                have hppi' :
                    HilbertLineInPlane Geo p pi := by
                  rw [hpq]
                  exact hqpi

                intro X hXp
                change H.OnLine X p at hXp
                rw [hJoinPi]
                exact hppi' X hXp


/--
Classical Euclid XI.5 recovered as a thin wrapper around the native
no-rank-increase statement.
-/
theorem euclid_proposition_11_5_from_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m n p : Geo.Line)
    (O : Geo.Point)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m O)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n O)
    (hPerpP :
      HilbertLinesPerpendicularAt Geo l p O) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo m pi /\
      HilbertLineInPlane Geo n pi /\
      HilbertLineInPlane Geo p pi := by

  have hOm : H.OnLine O m :=
    hPerpM.2.1

  have hOn : H.OnLine O n :=
    hPerpN.2.1

  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        m n O
        hmn hOm hOn with
  | intro pi hPiData =>

      have hmpi := hPiData.1
      have hnpi := hPiData.2.1
      have hJoinPi := hPiData.2.2

      have hpSubset :
          Set.Subset
            (HilbertLineCarrier3D Geo p)
            (HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo m)
              (HilbertLineCarrier3D Geo n)) :=
        euclid_proposition_11_5_native
          (Geo := Geo)
          l m n p O
          hmn
          hPerpM hPerpN hPerpP

      have hppi :
          HilbertLineInPlane Geo p pi := by
        intro X hXp
        have hXJoin := hpSubset hXp
        rw [hJoinPi] at hXJoin
        exact hXJoin

      exact
        Exists.intro pi
          (And.intro hmpi
            (And.intro hnpi hppi))


/-! ================================================================
    Book XI laboratory extraction: XI.6
    ================================================================ -/
/-!
# Euclid XI.6 in flat-native form

Classically XI.6 says that two lines perpendicular to the same plane at
distinct feet are parallel in space.

For the flat calculus the natural normal form is more explicit:

  join(carrier(l), carrier(m)) = carrier(sigma)

and

  l,m are disjoint.

Thus the affine word "parallel" is decomposed into:

1. a rank-two statement: the two lines generate one plane;
2. a meet statement at line level: the two carriers have no common point.

The proof below does not call the final theorem `euclid_proposition_11_6`.
It reuses the two lower XI.6 proof components already present in the
production file:
- coplanarity of the two normals;
- disjointness once coplanarity is known.

The generic conversion from coplanarity to an exact join identity comes
from `Hilbert3DWyler`.
-/

/--
Flat-native Euclid XI.6.

Two normals to the same plane at distinct feet generate a plane and are
disjoint.
-/
theorem euclid_proposition_11_6_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B)
    (hMperp :
      HilbertLinePerpendicularPlaneAt
        Geo m pi D) :
    exists sigma : S.Plane,
      HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo l)
        (HilbertLineCarrier3D Geo m) =
      HilbertPlaneCarrier3D Geo sigma /\
      HilbertLinesDisjoint Geo l m := by

  cases
      hilbert_XI6_normals_to_same_plane_coplanar_wyler
        (Geo := Geo)
        pi l m B D
        hBD
        hLperp
        hMperp with
  | intro sigma hSigmaData =>

      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigmaData.2

      have hDisjoint :
          HilbertLinesDisjoint Geo l m :=
        hilbert_XI6_coplanar_normals_disjoint_wyler
          (Geo := Geo)
          pi sigma
          l m
          B D
          hBD
          hlsigma
          hmsigma
          hLperp
          hMperp

      have hlm : Ne l m := by
        intro hEq

        have hBl : H.OnLine B l :=
          (HilbertLinePerpendicularPlaneAt.incidence
            (Geo := Geo)
            hLperp).1

        have hBm : H.OnLine B m := by
          rw [hEq] at hBl
          exact hBl

        exact
          hDisjoint
            (Exists.intro B
              (And.intro hBl hBm))

      have hJoin :
          HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            (HilbertLineCarrier3D Geo m) =
          HilbertPlaneCarrier3D Geo sigma :=
        hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
          (Geo := Geo)
          sigma l m
          hlm
          hlsigma
          hmsigma

      exact
        Exists.intro sigma
          (And.intro hJoin hDisjoint)


/--
Classical XI.6 recovered from the flat-native normal form.

This is only a comparison endpoint.  In the final architecture the
public `Proposition11_6` theorem can be a thin wrapper of this form.
-/
theorem euclid_proposition_11_6_from_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B)
    (hMperp :
      HilbertLinePerpendicularPlaneAt
        Geo m pi D) :
    HilbertSpaceLinesParallel Geo l m := by

  cases
      euclid_proposition_11_6_native
        (Geo := Geo)
        pi l m B D
        hBD
        hLperp
        hMperp with
  | intro sigma hData =>

      have hJoin := hData.1
      have hDisjoint := hData.2

      have hGen :=
        hilbertJoin3D_generators_subset_of_eq
          (Geo := Geo)
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)
          (HilbertPlaneCarrier3D Geo sigma)
          hJoin

      have hlsigma :
          HilbertLineInPlane Geo l sigma := by
        intro X hXl
        exact hGen.1 hXl

      have hmsigma :
          HilbertLineInPlane Geo m sigma := by
        intro X hXm
        exact hGen.2 hXm

      exact
        Exists.intro sigma
          (And.intro hlsigma
            (And.intro hmsigma hDisjoint))


/-! ================================================================
    Book XI laboratory extraction: XI.7
    ================================================================ -/
/-!
# Euclid XI.7 in flat-native form

The central flat fact is more general than Euclid XI.7:

  E in l, F in m
  ----------------
  Span{E,F} subset Join(l,m).

No parallelism is needed for this inclusion. It is just monotonicity of
span under inclusion of generators.

Parallelism enters only to force `Join(l,m)` to be a plane carrier and
to force E != F, so that `Span{E,F}` is exactly the carrier of the
joining line.
-/

/--
Generic connector-span monotonicity.

A pair of points chosen on two generator lines has span contained in the
join of those lines.
-/
theorem hilbertSpan3D_pair_subset_join_of_mem_lines
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l m : Geo.Line)
    (E F : Geo.Point)
    (hEl : H.OnLine E l)
    (hFm : H.OnLine F m) :
    Set.Subset
      (HilbertSpan3D Geo ({E, F} : Set Geo.Point))
      (HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo l)
        (HilbertLineCarrier3D Geo m)) := by

  apply
    hilbertSpan3D_mono
      (Geo := Geo)

  intro X hX

  simp only
    [Set.mem_insert_iff,
     Set.mem_singleton_iff] at hX

  rcases hX with hXE | hXF

  next =>
    subst X
    exact Or.inl hEl

  next =>
    subst X
    exact Or.inr hFm


/--
Flat-native Euclid XI.7.

For two parallel lines l,m and points E in l, F in m:

- the join of l and m is exactly a plane carrier;
- the span of E,F is exactly a line carrier;
- that connector line carrier is contained in the generated plane.

This is the rank-one-inside-rank-two form of XI.7.
-/
theorem euclid_proposition_11_7_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (E F : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hEl : H.OnLine E l)
    (hFm : H.OnLine F m) :
    exists sigma : S.Plane,
      exists n : Geo.Line,
        HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            (HilbertLineCarrier3D Geo m) =
          HilbertPlaneCarrier3D Geo sigma /\
        HilbertSpan3D Geo ({E, F} : Set Geo.Point) =
          HilbertLineCarrier3D Geo n /\
        Set.Subset
          (HilbertLineCarrier3D Geo n)
          (HilbertPlaneCarrier3D Geo sigma) := by

  cases hParallel with
  | intro sigma hSigma =>
      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigma.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigma.2.1

      have hDisjoint :
          HilbertLinesDisjoint Geo l m :=
        hSigma.2.2

      have hlm : Ne l m := by
        intro hEq

        have hEm : H.OnLine E m := by
          simpa [hEq] using hEl

        exact
          hDisjoint
            (Exists.intro E
              (And.intro hEl hEm))

      have hJoin :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo sigma :=
        hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
          (Geo := Geo)
          sigma l m
          hlm
          hlsigma
          hmsigma

      have hEF : Ne E F := by
        intro hEq
        subst F

        exact
          hDisjoint
            (Exists.intro E
              (And.intro hEl hFm))

      cases
          HilbertPlaneIncidence.line_through
            E F hEF with
      | intro n hN =>
          have hEn : H.OnLine E n :=
            hN.1

          have hFn : H.OnLine F n :=
            hN.2

          have hSpanN :
              HilbertSpan3D Geo ({E, F} : Set Geo.Point) =
                HilbertLineCarrier3D Geo n :=
            hilbertSpan3D_pair_eq_lineCarrier
              (Geo := Geo)
              E F n
              hEF
              hEn hFn

          have hPairSubsetJoin :
              Set.Subset
                (HilbertSpan3D Geo ({E, F} : Set Geo.Point))
                (HilbertJoin3D Geo
                  (HilbertLineCarrier3D Geo l)
                  (HilbertLineCarrier3D Geo m)) :=
            hilbertSpan3D_pair_subset_join_of_mem_lines
              (Geo := Geo)
              l m E F
              hEl hFm

          have hNsubsetSigma :
              Set.Subset
                (HilbertLineCarrier3D Geo n)
                (HilbertPlaneCarrier3D Geo sigma) := by

            intro X hXn

            have hXSpan :
                HilbertSpan3D Geo ({E, F} : Set Geo.Point) X := by
              rw [hSpanN]
              exact hXn

            have hXJoin :=
              hPairSubsetJoin hXSpan

            rw [hJoin] at hXJoin
            exact hXJoin

          exact
            Exists.intro sigma
              (Exists.intro n
                (And.intro hJoin
                  (And.intro hSpanN hNsubsetSigma)))


/--
Classical XI.7 recovered from the native flat statement.
-/
theorem euclid_proposition_11_7_from_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (E F : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hEl : H.OnLine E l)
    (hFm : H.OnLine F m) :
    exists sigma : S.Plane,
      HilbertLineInPlane Geo l sigma /\
      HilbertLineInPlane Geo m sigma /\
      exists n : Geo.Line,
        H.OnLine E n /\
        H.OnLine F n /\
        HilbertLineInPlane Geo n sigma := by

  cases
      euclid_proposition_11_7_native
        (Geo := Geo)
        l m E F
        hParallel hEl hFm with
  | intro sigma hSigma =>
      cases hSigma with
      | intro n hData =>
          have hJoin := hData.1
          have hSpanN := hData.2.1
          have hNsubsetSigma := hData.2.2

          have hGen :=
            hilbertJoin3D_generators_subset_of_eq
              (Geo := Geo)
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m)
              (HilbertPlaneCarrier3D Geo sigma)
              hJoin

          have hlsigma :
              HilbertLineInPlane Geo l sigma := by
            intro X hXl
            exact hGen.1 hXl

          have hmsigma :
              HilbertLineInPlane Geo m sigma := by
            intro X hXm
            exact hGen.2 hXm

          have hExt :=
            hilbertSpan3D_extensive
              (Geo := Geo)
              ({E, F} : Set Geo.Point)

          have hESpan :
              HilbertSpan3D Geo ({E, F} : Set Geo.Point) E := by
            apply hExt
            simp

          have hFSpan :
              HilbertSpan3D Geo ({E, F} : Set Geo.Point) F := by
            apply hExt
            simp

          have hEn : H.OnLine E n := by
            have h := hESpan
            rw [hSpanN] at h
            exact h

          have hFn : H.OnLine F n := by
            have h := hFSpan
            rw [hSpanN] at h
            exact h

          have hnsigma :
              HilbertLineInPlane Geo n sigma := by
            intro X hXn
            exact hNsubsetSigma hXn

          exact
            Exists.intro sigma
              (And.intro hlsigma
                (And.intro hmsigma
                  (Exists.intro n
                    (And.intro hEn
                      (And.intro hFn hnsigma)))))


/-! ================================================================
    Book XI laboratory extraction: XI.8
    ================================================================ -/
/-!
# Euclid XI.8 in flat-native form

XI.8 exposes a genuine boundary of the flat calculus.

The flat-incidence skeleton is

  sigma = join(l,m)
  q     = meet(pi,sigma)

where l,m are parallel and l is perpendicular to pi.

Pure flat incidence determines `sigma` and `q`, but it does not by itself
force the second parallel line `m` to meet the intersection line `q`.
That is the genuinely Euclidean Group IV step.

After the intersection point D is obtained, the final metric step has
the native XI.4 form:

  join(d,e) = pi
  m perpendicular d at D
  m perpendicular e at D
  --------------------------------
  m perpendicular pi at D.
-/

/--
The flat configuration behind the opening step of XI.8.

The common plane of the parallel lines is their exact join.  Its meet
with the reference plane is a line q.  Group IV supplies a point D of
the second parallel line lying on that meet line.
-/
theorem hilbert_XI8_parallel_plane_meet_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m : Geo.Line)
    (pi : S.Plane)
    (B : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo l pi B) :
    exists sigma : S.Plane,
      exists q : Geo.Line,
        exists D : Geo.Point,
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo sigma /\
          Set.inter
              (HilbertPlaneCarrier3D Geo pi)
              (HilbertPlaneCarrier3D Geo sigma) =
            HilbertLineCarrier3D Geo q /\
          H.OnLine D m /\
          H.OnLine D q := by

  cases hParallel with
  | intro sigma hSigmaData =>
      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigmaData.2.1

      have hDisjoint :
          HilbertLinesDisjoint Geo l m :=
        hSigmaData.2.2

      have hlm : Ne l m := by
        intro hEq

        have hBl : H.OnLine B l :=
          (HilbertLinePerpendicularPlaneAt.incidence
            (Geo := Geo) hPerp).1

        have hBm : H.OnLine B m := by
          rw [hEq] at hBl
          exact hBl

        exact
          hDisjoint
            (Exists.intro B
              (And.intro hBl hBm))

      have hJoin :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo sigma :=
        hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
          (Geo := Geo)
          sigma l m
          hlm
          hlsigma
          hmsigma

      have hBInc :=
        HilbertLinePerpendicularPlaneAt.incidence
          (Geo := Geo) hPerp

      have hBl : H.OnLine B l :=
        hBInc.1

      have hBpi : S.OnPlane B pi :=
        hBInc.2

      have hBsigma : S.OnPlane B sigma :=
        hlsigma B hBl

      have hSigmaPi : Ne sigma pi := by
        intro hEq

        apply
          (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
            (Geo := Geo)
            l pi B hPerp)

        intro X hXl

        have hXsigma : S.OnPlane X sigma :=
          hlsigma X hXl

        rw [hEq] at hXsigma
        exact hXsigma

      cases
          hilbertPlaneCarrier3D_inter_eq_lineCarrier
            (Geo := Geo)
            pi sigma
            hSigmaPi.symm
            B hBpi hBsigma with
      | intro q hQData =>

          have hMeet :=
            hQData.2.2.2

          cases
              hilbert_XI8_parallel_meets_perpendicular_plane_wyler
                (Geo := Geo)
                pi l m B
                (Exists.intro sigma
                  (And.intro hlsigma
                    (And.intro hmsigma hDisjoint)))
                hPerp with
          | intro D hDData =>

              have hDm : H.OnLine D m :=
                hDData.1

              have hDpi : S.OnPlane D pi :=
                hDData.2

              have hDsigma : S.OnPlane D sigma :=
                hmsigma D hDm

              have hDInter :
                  Set.inter
                    (HilbertPlaneCarrier3D Geo pi)
                    (HilbertPlaneCarrier3D Geo sigma) D :=
                And.intro hDpi hDsigma

              have hDq : H.OnLine D q := by
                have h :=
                  hDInter
                rw [hMeet] at h
                exact h

              exact
                Exists.intro sigma
                  (Exists.intro q
                    (Exists.intro D
                      (And.intro hJoin
                        (And.intro hMeet
                          (And.intro hDm hDq)))))


/--
Flat-native Euclid XI.8.

The final reference plane is represented by two generator lines d,e.
The second parallel line m is perpendicular to both generators at D,
hence native XI.4 makes it perpendicular to the generated plane.
-/
theorem euclid_proposition_11_8_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m : Geo.Line)
    (pi : S.Plane)
    (B : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo l pi B) :
    exists D : Geo.Point,
      exists d e : Geo.Line,
        H.OnLine D m /\
        HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo d)
            (HilbertLineCarrier3D Geo e) =
          HilbertPlaneCarrier3D Geo pi /\
        HilbertLinesPerpendicularAt Geo m d D /\
        HilbertLinesPerpendicularAt Geo m e D /\
        HilbertLinePerpendicularPlaneAt Geo m pi D := by

  cases
      hilbert_XI8_auxiliary_line_perpendicular_to_parallel_wyler
        (Geo := Geo)
        pi l m B
        hParallel hPerp with
  | intro D hD =>
      cases hD with
      | intro d hd =>
          cases hd with
          | intro e hData =>

              have hDm := hData.1
              have hBd := hData.2.2.1
              have hDd := hData.2.2.2.1
              have hdpi := hData.2.2.2.2.1
              have hDe := hData.2.2.2.2.2.1
              have hepi := hData.2.2.2.2.2.2.1
              have hPerpED := hData.2.2.2.2.2.2.2.1
              have hPerpEm := hData.2.2.2.2.2.2.2.2

              have hPerpMd :
                  HilbertLinesPerpendicularAt Geo m d D :=
                hilbert_XI8_parallel_line_perpendicular_to_given_BD_wyler
                  (Geo := Geo)
                  pi
                  l m d
                  B D
                  hParallel
                  hPerp
                  hDm
                  hData.2.1
                  hBd
                  hDd
                  hdpi

              have hPerpMe :
                  HilbertLinesPerpendicularAt Geo m e D :=
                hilbertLinesPerpendicularAt_symm_wyler
                  (Geo := Geo)
                  e m D
                  hPerpEm

              have hed : Ne e d :=
                hilbert_linesPerpendicularAt_ne
                  (Geo := Geo)
                  e d D
                  hPerpED

              have hde : Ne d e :=
                hed.symm

              have hJoinPi :
                  HilbertJoin3D Geo
                      (HilbertLineCarrier3D Geo d)
                      (HilbertLineCarrier3D Geo e) =
                    HilbertPlaneCarrier3D Geo pi :=
                hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
                  (Geo := Geo)
                  pi d e
                  hde
                  hdpi
                  hepi

              have hFinal :
                  HilbertLinePerpendicularPlaneAt Geo m pi D :=
                euclid_proposition_11_4_via_join_native
                  (Geo := Geo)
                  pi d e m D
                  hde
                  hJoinPi
                  hPerpMd
                  hPerpMe

              exact
                Exists.intro D
                  (Exists.intro d
                    (Exists.intro e
                      (And.intro hDm
                        (And.intro hJoinPi
                          (And.intro hPerpMd
                            (And.intro hPerpMe hFinal))))))


/-! ================================================================
    Book XI laboratory extraction: XI.9
    ================================================================ -/
/-!
# Euclid XI.9 in flat-native form

XI.9 is naturally expressed as a rank-two plus empty-meet statement.

Assume l and m are each parallel to n, while l,m,n are not all
coplanar.  Then the native conclusion is:

  join(l,m) = plane omega

and

  l,m are disjoint.

The key generator rule used repeatedly is

  line + external point = plane.

This replaces proposition-local plane uniqueness arguments by equality
of carriers generated by the same data.
-/

/--
Flat-native Euclid XI.9.

Two lines parallel to the same line, under the noncoplanarity hypothesis
of XI.9, generate a plane and are disjoint.
-/
theorem euclid_proposition_11_9_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m n : Geo.Line)
    (hParallelLN : HilbertSpaceLinesParallel Geo l n)
    (hParallelMN : HilbertSpaceLinesParallel Geo m n)
    (hNoCommonPlane :
      Not (exists omega : S.Plane,
        HilbertLineInPlane Geo l omega /\
        HilbertLineInPlane Geo m omega /\
        HilbertLineInPlane Geo n omega)) :
    exists omega : S.Plane,
      HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m) =
        HilbertPlaneCarrier3D Geo omega /\
      HilbertLinesDisjoint Geo l m := by

  cases hParallelLN with
  | intro sigma hSigmaData =>
      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hnsigma :
          HilbertLineInPlane Geo n sigma :=
        hSigmaData.2.1

      have hDisjointLN :
          HilbertLinesDisjoint Geo l n :=
        hSigmaData.2.2

      cases hParallelMN with
      | intro tau hTauData =>
          have hmtau :
              HilbertLineInPlane Geo m tau :=
            hTauData.1

          have hntau :
              HilbertLineInPlane Geo n tau :=
            hTauData.2.1

          have hDisjointMN :
              HilbertLinesDisjoint Geo m n :=
            hTauData.2.2

          --------------------------------------------------------------
          -- sigma and tau are genuinely different carriers.
          --------------------------------------------------------------

          have hSigmaTauCarrier :
              Ne
                (HilbertPlaneCarrier3D Geo sigma)
                (HilbertPlaneCarrier3D Geo tau) := by
            intro hCarrierEq

            have hmsigma :
                HilbertLineInPlane Geo m sigma := by
              intro X hXm
              change HilbertPlaneCarrier3D Geo sigma X
              rw [hCarrierEq]
              exact hmtau X hXm

            exact
              hNoCommonPlane
                (Exists.intro sigma
                  (And.intro hlsigma
                    (And.intro hmsigma hnsigma)))

          have hlm : Ne l m := by
            intro hEq

            have hmsigma :
                HilbertLineInPlane Geo m sigma := by
              rw [<- hEq]
              exact hlsigma

            exact
              hNoCommonPlane
                (Exists.intro sigma
                  (And.intro hlsigma
                    (And.intro hmsigma hnsigma)))

          cases
              hilbert_point_on_second_line_off_first
                (Geo := Geo)
                l m hlm with
          | intro B hBData =>

              have hBm : H.OnLine B m :=
                hBData.1

              have hBl : Not (H.OnLine B l) :=
                hBData.2

              have hBtau : S.OnPlane B tau :=
                hmtau B hBm

              have hBn : Not (H.OnLine B n) := by
                intro hBn
                exact
                  hDisjointMN
                    (Exists.intro B
                      (And.intro hBm hBn))

              ----------------------------------------------------------
              -- omega = join(l,{B}).
              ----------------------------------------------------------

              cases
                  hilbert_plane_through_line_and_external_point
                    (Geo := Geo)
                    l B hBl with
              | intro omega hOmegaData =>

                  have hlomega :
                      HilbertLineInPlane Geo l omega :=
                    hOmegaData.1

                  have hBomega :
                      S.OnPlane B omega :=
                    hOmegaData.2.1

                  have hJoinOmegaLB :
                      HilbertJoin3D Geo
                          (HilbertLineCarrier3D Geo l)
                          ({B} : Set Geo.Point) =
                        HilbertPlaneCarrier3D Geo omega :=
                    hilbertJoin3D_line_external_point_eq_planeCarrier
                      (Geo := Geo)
                      omega l B
                      hlomega hBomega hBl

                  ------------------------------------------------------
                  -- sigma != omega.
                  ------------------------------------------------------

                  have hSigmaOmegaCarrier :
                      Ne
                        (HilbertPlaneCarrier3D Geo sigma)
                        (HilbertPlaneCarrier3D Geo omega) := by
                    intro hCarrierEq

                    have hBsigma : S.OnPlane B sigma := by
                      change HilbertPlaneCarrier3D Geo sigma B
                      rw [hCarrierEq]
                      exact hBomega

                    have hJoinSigmaNB :
                        HilbertJoin3D Geo
                            (HilbertLineCarrier3D Geo n)
                            ({B} : Set Geo.Point) =
                          HilbertPlaneCarrier3D Geo sigma :=
                      hilbertJoin3D_line_external_point_eq_planeCarrier
                        (Geo := Geo)
                        sigma n B
                        hnsigma hBsigma hBn

                    have hJoinTauNB :
                        HilbertJoin3D Geo
                            (HilbertLineCarrier3D Geo n)
                            ({B} : Set Geo.Point) =
                          HilbertPlaneCarrier3D Geo tau :=
                      hilbertJoin3D_line_external_point_eq_planeCarrier
                        (Geo := Geo)
                        tau n B
                        hntau hBtau hBn

                    apply hSigmaTauCarrier
                    exact hJoinSigmaNB.symm.trans hJoinTauNB

                  ------------------------------------------------------
                  -- omega != tau.
                  ------------------------------------------------------

                  have hOmegaTauCarrier :
                      Ne
                        (HilbertPlaneCarrier3D Geo omega)
                        (HilbertPlaneCarrier3D Geo tau) := by
                    intro hCarrierEq

                    have hltau :
                        HilbertLineInPlane Geo l tau := by
                      intro X hXl
                      change HilbertPlaneCarrier3D Geo tau X
                      rw [<- hCarrierEq]
                      exact hlomega X hXl

                    exact
                      hNoCommonPlane
                        (Exists.intro tau
                          (And.intro hltau
                            (And.intro hmtau hntau)))

                  have hOmegaTau : Ne omega tau := by
                    intro hEq
                    apply hOmegaTauCarrier
                    rw [hEq]

                  ------------------------------------------------------
                  -- r = meet(omega,tau), through B.
                  ------------------------------------------------------

                  cases
                      hilbertPlaneCarrier3D_inter_eq_lineCarrier
                        (Geo := Geo)
                        omega tau
                        hOmegaTau
                        B hBomega hBtau with
                  | intro r hRData =>

                      have hBr : H.OnLine B r :=
                        hRData.1

                      have hromega :
                          HilbertLineInPlane Geo r omega :=
                        hRData.2.1

                      have hrtau :
                          HilbertLineInPlane Geo r tau :=
                        hRData.2.2.1

                      --------------------------------------------------
                      -- r is disjoint from n.
                      --------------------------------------------------

                      have hDisjointRN :
                          HilbertLinesDisjoint Geo r n := by
                        intro hMeet

                        cases hMeet with
                        | intro P hPData =>
                            have hPr : H.OnLine P r :=
                              hPData.1

                            have hPn : H.OnLine P n :=
                              hPData.2

                            have hPomega : S.OnPlane P omega :=
                              hromega P hPr

                            have hPsigma : S.OnPlane P sigma :=
                              hnsigma P hPn

                            have hPl : Not (H.OnLine P l) := by
                              intro hPl
                              exact
                                hDisjointLN
                                  (Exists.intro P
                                    (And.intro hPl hPn))

                            have hJoinSigmaLP :
                                HilbertJoin3D Geo
                                    (HilbertLineCarrier3D Geo l)
                                    ({P} : Set Geo.Point) =
                                  HilbertPlaneCarrier3D Geo sigma :=
                              hilbertJoin3D_line_external_point_eq_planeCarrier
                                (Geo := Geo)
                                sigma l P
                                hlsigma hPsigma hPl

                            have hJoinOmegaLP :
                                HilbertJoin3D Geo
                                    (HilbertLineCarrier3D Geo l)
                                    ({P} : Set Geo.Point) =
                                  HilbertPlaneCarrier3D Geo omega :=
                              hilbertJoin3D_line_external_point_eq_planeCarrier
                                (Geo := Geo)
                                omega l P
                                hlomega hPomega hPl

                            apply hSigmaOmegaCarrier
                            exact
                              hJoinSigmaLP.symm.trans hJoinOmegaLP

                      --------------------------------------------------
                      -- Group IV in tau identifies r with m.
                      --------------------------------------------------

                      have hrm : r = m :=
                        HilbertSpaceEuclidean.parallel_unique_in_plane
                          (Geo := Geo)
                          tau
                          n hntau
                          B hBtau hBn
                          r m
                          hrtau hmtau
                          hBr hDisjointRN
                          hBm hDisjointMN

                      have hmomega :
                          HilbertLineInPlane Geo m omega := by
                        rw [<- hrm]
                        exact hromega

                      --------------------------------------------------
                      -- l and m are disjoint.
                      --------------------------------------------------

                      have hDisjointLM :
                          HilbertLinesDisjoint Geo l m := by
                        intro hMeet

                        cases hMeet with
                        | intro P hPData =>
                            have hPl : H.OnLine P l :=
                              hPData.1

                            have hPm : H.OnLine P m :=
                              hPData.2

                            have hPn : Not (H.OnLine P n) := by
                              intro hPn
                              exact
                                hDisjointLN
                                  (Exists.intro P
                                    (And.intro hPl hPn))

                            have hPsigma : S.OnPlane P sigma :=
                              hlsigma P hPl

                            have hPtau : S.OnPlane P tau :=
                              hmtau P hPm

                            have hJoinSigmaNP :
                                HilbertJoin3D Geo
                                    (HilbertLineCarrier3D Geo n)
                                    ({P} : Set Geo.Point) =
                                  HilbertPlaneCarrier3D Geo sigma :=
                              hilbertJoin3D_line_external_point_eq_planeCarrier
                                (Geo := Geo)
                                sigma n P
                                hnsigma hPsigma hPn

                            have hJoinTauNP :
                                HilbertJoin3D Geo
                                    (HilbertLineCarrier3D Geo n)
                                    ({P} : Set Geo.Point) =
                                  HilbertPlaneCarrier3D Geo tau :=
                              hilbertJoin3D_line_external_point_eq_planeCarrier
                                (Geo := Geo)
                                tau n P
                                hntau hPtau hPn

                            apply hSigmaTauCarrier
                            exact
                              hJoinSigmaNP.symm.trans hJoinTauNP

                      have hJoinLM :
                          HilbertJoin3D Geo
                              (HilbertLineCarrier3D Geo l)
                              (HilbertLineCarrier3D Geo m) =
                            HilbertPlaneCarrier3D Geo omega :=
                        hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
                          (Geo := Geo)
                          omega l m
                          hlm
                          hlomega
                          hmomega

                      exact
                        Exists.intro omega
                          (And.intro hJoinLM hDisjointLM)


/--
Classical XI.9 recovered from the native normal form.
-/
theorem euclid_proposition_11_9_from_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m n : Geo.Line)
    (hParallelLN : HilbertSpaceLinesParallel Geo l n)
    (hParallelMN : HilbertSpaceLinesParallel Geo m n)
    (hNoCommonPlane :
      Not (exists omega : S.Plane,
        HilbertLineInPlane Geo l omega /\
        HilbertLineInPlane Geo m omega /\
        HilbertLineInPlane Geo n omega)) :
    HilbertSpaceLinesParallel Geo l m := by

  cases
      euclid_proposition_11_9_native
        (Geo := Geo)
        l m n
        hParallelLN hParallelMN
        hNoCommonPlane with
  | intro omega hData =>

      have hJoin := hData.1
      have hDisjoint := hData.2

      have hGen :=
        hilbertJoin3D_generators_subset_of_eq
          (Geo := Geo)
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)
          (HilbertPlaneCarrier3D Geo omega)
          hJoin

      have hlomega :
          HilbertLineInPlane Geo l omega := by
        intro X hXl
        exact hGen.1 hXl

      have hmomega :
          HilbertLineInPlane Geo m omega := by
        intro X hXm
        exact hGen.2 hXm

      exact
        Exists.intro omega
          (And.intro hlomega
            (And.intro hmomega hDisjoint))


/-! ================================================================
    Book XI laboratory extraction: XI.10
    ================================================================ -/
/-! ================================================================
    Book XI laboratory extraction: XI.11
    ================================================================ -/
/-!
# Euclid XI.11 in flat-native form

XI.11 does not introduce a new flat-construction rule.  Its geometric
construction is genuinely metric: from a point outside a plane, construct
a perpendicular to the plane.

The useful flat core is instead an equivalence of input representations:

  A notin pi

if and only if

  join(carrier(pi), {A}) = E^3.

Thus the classical incidence hypothesis can be replaced by an exact
rank-three certificate.
-/

/--
A point is external to a plane exactly when adjoining it to the plane
raises the span to the whole ambient three-space.
-/
theorem hilbertJoin3D_plane_point_eq_univ_iff_external
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A : Geo.Point) :
    HilbertJoin3D Geo
        (HilbertPlaneCarrier3D Geo pi)
        ({A} : Set Geo.Point) =
      (Set.univ : Set Geo.Point) <->
    Not (S.OnPlane A pi) := by

  constructor

  next =>
    intro hRank3 hApi

    cases
        hilbert_point_off_plane
          (Geo := Geo)
          pi with
    | intro P hPpi =>

        have hPointSubsetPlane :
            Set.Subset
              ({A} : Set Geo.Point)
              (HilbertPlaneCarrier3D Geo pi) := by
          intro X hXA
          simp only [Set.mem_singleton_iff] at hXA
          subst X
          exact hApi

        have hJoinSubsetPlane :
            Set.Subset
              (HilbertJoin3D Geo
                (HilbertPlaneCarrier3D Geo pi)
                ({A} : Set Geo.Point))
              (HilbertPlaneCarrier3D Geo pi) :=
          hilbertJoin3D_least
            (Geo := Geo)
            (HilbertPlaneCarrier3D Geo pi)
            ({A} : Set Geo.Point)
            (HilbertPlaneCarrier3D Geo pi)
            (hilbertPlaneCarrier3D_flat
              (Geo := Geo) pi)
            (fun X hX => hX)
            hPointSubsetPlane

        have hPJoin :
            HilbertJoin3D Geo
              (HilbertPlaneCarrier3D Geo pi)
              ({A} : Set Geo.Point) P := by
          rw [hRank3]
          trivial

        have hPpi' : S.OnPlane P pi :=
          hJoinSubsetPlane hPJoin

        exact hPpi hPpi'

  next =>
    intro hApi
    exact
      hilbertJoin3D_plane_external_point_eq_univ
        (Geo := Geo)
        pi A hApi


/--
Flat-native Euclid XI.11.

Instead of assuming directly that A is outside pi, the theorem assumes
the structural rank-three identity

  join(pi,{A}) = E^3.

The output is the classical XI.11 perpendicular construction.
-/
theorem euclid_proposition_11_11_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A : Geo.Point)
    (hRank3 :
      HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          ({A} : Set Geo.Point) =
        (Set.univ : Set Geo.Point)) :
    exists l F,
      H.OnLine A l /\
      HilbertLinePerpendicularPlaneAt Geo l pi F := by

  have hApi : Not (S.OnPlane A pi) :=
    (hilbertJoin3D_plane_point_eq_univ_iff_external
      (Geo := Geo)
      pi A).mp hRank3

  exact
    euclid_proposition_11_11_wyler
      (Geo := Geo)
      pi A hApi


/--
Classical XI.11 recovered as a thin wrapper around the rank-three input
form.
-/
theorem euclid_proposition_11_11_from_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A : Geo.Point)
    (hApi : Not (S.OnPlane A pi)) :
    exists l F,
      H.OnLine A l /\
      HilbertLinePerpendicularPlaneAt Geo l pi F := by

  have hRank3 :
      HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          ({A} : Set Geo.Point) =
        (Set.univ : Set Geo.Point) :=
    (hilbertJoin3D_plane_point_eq_univ_iff_external
      (Geo := Geo)
      pi A).mpr hApi

  exact
    euclid_proposition_11_11_native
      (Geo := Geo)
      pi A hRank3


/-! ================================================================
    Book XI laboratory extraction: XI.12
    ================================================================ -/
/-!
# Euclid XI.12 in flat-native form

The nontrivial branch of XI.12 has a clean flat configuration.

Given a line l and a point A outside l, first form the generated slice

  sigma = join(carrier(l), {A}).

Inside this rank-two carrier construct the line m through A parallel to
l.  The same slice is then also generated by l and m:

  join(carrier(l), carrier(m)) = carrier(sigma).

Thus the middle part of XI.12 has the normal form

  sigma = join(l,{A}) = join(l,m).

The final transfer of perpendicularity is handled by native XI.8.
-/

/--
Generated-slice core used by XI.12.

A line l and an external point A generate a plane sigma.  Inside that
generated plane there is a line m through A parallel to l, and l,m
generate the same plane sigma.
-/
theorem hilbert_XI12_generated_slice_parallel_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l : Geo.Line)
    (A : Geo.Point)
    (hAl : Not (H.OnLine A l)) :
    exists sigma : S.Plane,
      exists m : Geo.Line,
        HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            ({A} : Set Geo.Point) =
          HilbertPlaneCarrier3D Geo sigma /\
        H.OnLine A m /\
        HilbertSpaceLinesParallel Geo l m /\
        HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            (HilbertLineCarrier3D Geo m) =
          HilbertPlaneCarrier3D Geo sigma := by

  cases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l A hAl with
  | intro sigma hSigmaData =>

      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hAsigma :
          S.OnPlane A sigma :=
        hSigmaData.2.1

      have hJoinSlice :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              ({A} : Set Geo.Point) =
            HilbertPlaneCarrier3D Geo sigma :=
        hilbertJoin3D_line_external_point_eq_planeCarrier
          (Geo := Geo)
          sigma l A
          hlsigma hAsigma hAl

      cases
          hilbert_XI12_parallel_through_point_in_plane_wyler
            (Geo := Geo)
            sigma l A
            hlsigma hAsigma hAl with
      | intro m hMData =>

          have hAm : H.OnLine A m :=
            hMData.1

          have hParallel0 :
              HilbertSpaceLinesParallel Geo l m :=
            hMData.2

          cases hParallel0 with
          | intro rho hRhoData =>

              have hlrho :
                  HilbertLineInPlane Geo l rho :=
                hRhoData.1

              have hmrho :
                  HilbertLineInPlane Geo m rho :=
                hRhoData.2.1

              have hDisjoint :
                  HilbertLinesDisjoint Geo l m :=
                hRhoData.2.2

              have hArho : S.OnPlane A rho :=
                hmrho A hAm

              have hJoinRho :
                  HilbertJoin3D Geo
                      (HilbertLineCarrier3D Geo l)
                      ({A} : Set Geo.Point) =
                    HilbertPlaneCarrier3D Geo rho :=
                hilbertJoin3D_line_external_point_eq_planeCarrier
                  (Geo := Geo)
                  rho l A
                  hlrho hArho hAl

              have hCarrierSigmaRho :
                  HilbertPlaneCarrier3D Geo sigma =
                    HilbertPlaneCarrier3D Geo rho :=
                hJoinSlice.symm.trans hJoinRho

              have hmsigma :
                  HilbertLineInPlane Geo m sigma := by
                intro X hXm
                change HilbertPlaneCarrier3D Geo sigma X
                rw [hCarrierSigmaRho]
                exact hmrho X hXm

              have hParallel :
                  HilbertSpaceLinesParallel Geo l m :=
                Exists.intro sigma
                  (And.intro hlsigma
                    (And.intro hmsigma hDisjoint))

              have hlm : Ne l m := by
                intro hEq
                apply hAl
                rw [hEq]
                exact hAm

              have hJoinLM :
                  HilbertJoin3D Geo
                      (HilbertLineCarrier3D Geo l)
                      (HilbertLineCarrier3D Geo m) =
                    HilbertPlaneCarrier3D Geo sigma :=
                hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
                  (Geo := Geo)
                  sigma l m
                  hlm
                  hlsigma
                  hmsigma

              exact
                Exists.intro sigma
                  (Exists.intro m
                    (And.intro hJoinSlice
                      (And.intro hAm
                        (And.intro hParallel hJoinLM))))


/--
Flat-native Euclid XI.12.

The proof uses:
1. a point B external to pi;
2. the rank-three form of XI.11 to construct l perpendicular to pi;
3. if necessary, the generated slice sigma = join(l,{A});
4. a parallel m through A inside that slice;
5. native XI.8 to transfer perpendicularity from l to m.
-/
theorem euclid_proposition_11_12_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi) :
    exists l : Geo.Line,
      HilbertLinePerpendicularPlaneAt Geo l pi A := by

  cases
      hilbert_point_off_plane
        (Geo := Geo)
        pi with
  | intro B hBpi =>

      have hRank3 :
          HilbertJoin3D Geo
              (HilbertPlaneCarrier3D Geo pi)
              ({B} : Set Geo.Point) =
            (Set.univ : Set Geo.Point) :=
        hilbertJoin3D_plane_external_point_eq_univ
          (Geo := Geo)
          pi B hBpi

      cases
          euclid_proposition_11_11_native
            (Geo := Geo)
            pi B hRank3 with
      | intro l hLData =>
          cases hLData with
          | intro F hFData =>

              have hPerp :
                  HilbertLinePerpendicularPlaneAt Geo l pi F :=
                hFData.2

              by_cases hAl : H.OnLine A l

              next =>
                have hAF : A = F :=
                  hilbertLinePerpendicularPlaneAt_foot_unique_wyler
                    (Geo := Geo)
                    pi l F A
                    hPerp
                    hAl
                    hApi

                subst F
                exact Exists.intro l hPerp

              next =>
                cases
                    hilbert_XI12_generated_slice_parallel_native
                      (Geo := Geo)
                      l A hAl with
                | intro sigma hSlice =>
                    cases hSlice with
                    | intro m hMData =>

                        have hAm : H.OnLine A m :=
                          hMData.2.1

                        have hParallel :
                            HilbertSpaceLinesParallel Geo l m :=
                          hMData.2.2.1

                        cases
                            euclid_proposition_11_8_native
                              (Geo := Geo)
                              l m pi F
                              hParallel hPerp with
                        | intro D hDData =>
                            cases hDData with
                            | intro d hDEData =>
                                cases hDEData with
                                | intro e hFinalData =>

                                    have hMperp :
                                        HilbertLinePerpendicularPlaneAt
                                          Geo m pi D :=
                                      hFinalData.2.2.2.2

                                    have hAD : A = D :=
                                      hilbertLinePerpendicularPlaneAt_foot_unique_wyler
                                        (Geo := Geo)
                                        pi m D A
                                        hMperp
                                        hAm
                                        hApi

                                    subst D

                                    exact
                                      Exists.intro m hMperp


/-! ================================================================
    Book XI laboratory extraction: XI.13
    ================================================================ -/
/-!
# Euclid XI.13 in flat-native form

XI.13 gives a complete join-meet-metric contradiction pattern.

Assume that two distinct lines l,m are both perpendicular to the same
plane pi at the same point A.

The flat skeleton is:

  sigma = join(l,m)
  q     = meet(pi,sigma).

Because q lies in pi, both l and m are perpendicular to q.  By symmetry,
q is perpendicular to both generators l,m of sigma.  Native XI.4 then
gives q perpendicular to sigma.  But q itself lies in sigma, which is
impossible.

No call to the classical `euclid_proposition_11_13` is made below.
-/

/--
Distinct normals to one plane at the same point produce a contradiction.

This is the reusable native core of XI.13.
-/
theorem hilbert_XI13_distinct_normals_contradiction_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (A : Geo.Point)
    (hlm : Ne l m)
    (hLperp :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hMperp :
      HilbertLinePerpendicularPlaneAt Geo m pi A) :
    False := by

  have hLInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp

  have hMInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hMperp

  have hAl : H.OnLine A l :=
    hLInc.1

  have hAm : H.OnLine A m :=
    hMInc.1

  have hApi : S.OnPlane A pi :=
    hLInc.2

  ----------------------------------------------------------------------
  -- sigma = join(l,m).
  ----------------------------------------------------------------------

  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        l m A
        hlm
        hAl hAm with
  | intro sigma hSigmaData =>

      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigmaData.2.1

      have hJoinSigma :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo sigma :=
        hSigmaData.2.2

      have hAsigma : S.OnPlane A sigma :=
        hlsigma A hAl

      ------------------------------------------------------------------
      -- sigma != pi.
      ------------------------------------------------------------------

      have hSigmaPi : Ne sigma pi := by
        intro hEq

        have hlpi :
            HilbertLineInPlane Geo l pi := by
          intro X hXl

          have hXsigma : S.OnPlane X sigma :=
            hlsigma X hXl

          rw [hEq] at hXsigma
          exact hXsigma

        exact
          (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
            (Geo := Geo)
            l pi A hLperp)
            hlpi

      ------------------------------------------------------------------
      -- q = meet(pi,sigma).
      ------------------------------------------------------------------

      cases
          hilbertPlaneCarrier3D_inter_eq_lineCarrier
            (Geo := Geo)
            pi sigma
            hSigmaPi.symm
            A hApi hAsigma with
      | intro q hQData =>

          have hAq : H.OnLine A q :=
            hQData.1

          have hqpi :
              HilbertLineInPlane Geo q pi :=
            hQData.2.1

          have hqsigma :
              HilbertLineInPlane Geo q sigma :=
            hQData.2.2.1

          have hMeet :
              Set.inter
                  (HilbertPlaneCarrier3D Geo pi)
                  (HilbertPlaneCarrier3D Geo sigma) =
                HilbertLineCarrier3D Geo q :=
            hQData.2.2.2

          ----------------------------------------------------------------
          -- Metric part: q is perpendicular to both generators l,m.
          ----------------------------------------------------------------

          have hLperpQ :
              HilbertLinesPerpendicularAt Geo l q A :=
            HilbertLinePerpendicularPlaneAt.perpendicular_to_line
              (Geo := Geo)
              hLperp
              hqpi
              hAq

          have hMperpQ :
              HilbertLinesPerpendicularAt Geo m q A :=
            HilbertLinePerpendicularPlaneAt.perpendicular_to_line
              (Geo := Geo)
              hMperp
              hqpi
              hAq

          have hQperpL :
              HilbertLinesPerpendicularAt Geo q l A :=
            hilbertLinesPerpendicularAt_symm_wyler
              (Geo := Geo)
              l q A
              hLperpQ

          have hQperpM :
              HilbertLinesPerpendicularAt Geo q m A :=
            hilbertLinesPerpendicularAt_symm_wyler
              (Geo := Geo)
              m q A
              hMperpQ

          ----------------------------------------------------------------
          -- Native XI.4 on the generated plane sigma.
          ----------------------------------------------------------------

          have hQperpSigma :
              HilbertLinePerpendicularPlaneAt Geo q sigma A :=
            euclid_proposition_11_4_via_join_native
              (Geo := Geo)
              sigma
              l m q A
              hlm
              hJoinSigma
              hQperpL
              hQperpM

          ----------------------------------------------------------------
          -- Contradiction: the meet line q is itself contained in sigma.
          ----------------------------------------------------------------

          exact
            (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
              (Geo := Geo)
              q sigma A hQperpSigma)
              hqsigma


/--
Flat-native Euclid XI.13.

A perpendicular to a plane at a prescribed point is unique as an
unoriented line carrier.
-/
theorem euclid_proposition_11_13_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (A : Geo.Point)
    (hLperp :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hMperp :
      HilbertLinePerpendicularPlaneAt Geo m pi A) :
    l = m := by

  by_contra hlm

  exact
    hilbert_XI13_distinct_normals_contradiction_native
      (Geo := Geo)
      pi l m A
      hlm
      hLperp
      hMperp


/-! ================================================================
    Book XI laboratory extraction: XI.14
    ================================================================ -/
/-!
# Euclid XI.14 in flat-native form

For two distinct planes perpendicular to the same ambient line, the
natural flat conclusion is:

  join(pi,rho) = E^3

and

  meet(pi,rho) = empty.

Thus classical plane parallelism is represented structurally by
maximal join together with empty meet.

The proof below does not call the final theorem
`euclid_proposition_11_14`.  It uses only the lower XI.14 helpers:
- uniqueness of a plane perpendicular to a fixed line at a fixed point;
- the normalized distinct-foot contradiction theorem.
-/

/--
Flat-native core of Euclid XI.14.

Two distinct planes perpendicular to the same line generate the whole
ambient three-space and have empty intersection.
-/
theorem hilbert_XI14_common_normal_join_univ_meet_empty_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hPlanesNe : Ne pi rho)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B) :
    HilbertJoin3D Geo
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      (Set.univ : Set Geo.Point) /\
    Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      (fun _ => False : Set Geo.Point) := by

  have hJoin :
      HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho) =
        (Set.univ : Set Geo.Point) :=
    hilbertJoin3D_two_distinct_planes_eq_univ
      (Geo := Geo)
      pi rho hPlanesNe

  have hAB : Ne A B := by
    intro hABeq
    subst B

    have hPlanesEq : pi = rho :=
      hilbert_XI14_plane_perpendicular_to_line_at_unique_wyler
        (Geo := Geo)
        pi rho l A
        hPerpPi
        hPerpRho

    exact hPlanesNe hPlanesEq

  have hNoCommon :
      HilbertSpacePlanesParallel Geo pi rho :=
    euclid_proposition_11_14_normalized_wyler
      (Geo := Geo)
      pi rho l A B
      hAB
      hPerpPi
      hPerpRho

  have hMeetEmpty :
      Set.inter
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho) =
        (fun _ => False : Set Geo.Point) := by

    apply Set.ext
    intro X
    constructor

    next =>
      intro hX

      have hFalse : False :=
        hNoCommon
          (Exists.intro X
            (And.intro hX.1 hX.2))

      exact False.elim hFalse

    next =>
      intro hX
      exact False.elim hX

  exact
    And.intro hJoin hMeetEmpty


/--
Flat-native Euclid XI.14.

The primary output is the join/meet normal form.  The classical
`HilbertSpacePlanesParallel` statement is recovered as a corollary.
-/
theorem euclid_proposition_11_14_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hPlanesNe : Ne pi rho)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B) :
    HilbertJoin3D Geo
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      (Set.univ : Set Geo.Point) /\
    Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      (fun _ => False : Set Geo.Point) := by

  exact
    hilbert_XI14_common_normal_join_univ_meet_empty_native
      (Geo := Geo)
      pi rho l A B
      hPlanesNe
      hPerpPi
      hPerpRho


/--
Classical XI.14 recovered from the native empty-meet statement.
-/
theorem euclid_proposition_11_14_from_native
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hPlanesNe : Ne pi rho)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B) :
    HilbertSpacePlanesParallel Geo pi rho := by

  have hNative :=
    euclid_proposition_11_14_native
      (Geo := Geo)
      pi rho l A B
      hPlanesNe
      hPerpPi
      hPerpRho

  have hMeetEmpty :=
    hNative.2

  intro hCommon

  cases hCommon with
  | intro X hXData =>

      have hXMeet :
          Set.inter
              (HilbertPlaneCarrier3D Geo pi)
              (HilbertPlaneCarrier3D Geo rho) X :=
        And.intro hXData.1 hXData.2

      rw [hMeetEmpty] at hXMeet
      exact hXMeet

end Geometry

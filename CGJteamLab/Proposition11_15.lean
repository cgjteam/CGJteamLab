import CGJteamLab.Proposition11_14
import CGJteamLab.Proposition11_12
import CGJteamLab.Proposition11_9
import CGJteamLab.Proposition11_8
import CGJteamLab.Proposition11_4

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


/--
Symmetry of spatial line parallelism.

This is proposition-local for now. XI.15 needs the same pair of
parallelisms in the reverse direction when the two reference planes
are exchanged.
-/
theorem hilbert_XI15_spaceLinesParallel_symm
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l m : Geo.Line)
    (hParallel :
      HilbertSpaceLinesParallel Geo l m) :
    HilbertSpaceLinesParallel Geo m l := by

  cases hParallel with
  | intro sigma hData =>
      exact
        Exists.intro sigma
          (And.intro
            hData.2.1
            (And.intro
              hData.1
              (by
                intro hMeet
                cases hMeet with
                | intro P hP =>
                    exact
                      hData.2.2
                        (Exists.intro P
                          (And.intro hP.2 hP.1)))))


/--
XI.15 incidence lemma.

Let `l1,l2` be two distinct intersecting lines of `pi`, meeting at `B`.
Let `m1,m2` lie in another plane `rho`, with

    l1 || m1,
    l2 || m2.

If `pi != rho`, then the intersection point `B` cannot lie in `rho`.

The proof is purely spatial incidence.
-/
theorem hilbert_XI15_intersection_point_off_other_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (hl12 : Ne l1 l2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hPlanesNe : Ne pi rho) :
    Not (S.OnPlane B.1 rho) := by

  intro hBrho

  cases hParallel1 with
  | intro sigma1 hData1 =>

      have hl1sigma1 :
          HilbertLineInPlane Geo l1.1 sigma1 :=
        hData1.1

      have hm1sigma1 :
          HilbertLineInPlane Geo m1.1 sigma1 :=
        hData1.2.1

      have hDisjoint1 :
          HilbertLinesDisjoint Geo l1.1 m1.1 :=
        hData1.2.2

      have hBsigma1 :
          S.OnPlane B.1 sigma1 :=
        hl1sigma1 B.1 hBl1

      have hBm1 :
          Not (H.OnLine B.1 m1.1) := by
        intro hBm1
        exact
          hDisjoint1
            (Exists.intro B.1
              (And.intro hBl1 hBm1))

      have hSigma1Rho :
          sigma1 = rho :=
        hilbert_XI9_planes_eq_of_common_line_and_external_point
          (Geo := Geo)
          m1.1
          B.1
          hBm1
          sigma1 rho
          hm1sigma1
          m1.2
          hBsigma1
          hBrho

      have hl1rho :
          HilbertLineInPlane Geo l1.1 rho := by
        simpa [hSigma1Rho] using hl1sigma1

      cases hParallel2 with
      | intro sigma2 hData2 =>

          have hl2sigma2 :
              HilbertLineInPlane Geo l2.1 sigma2 :=
            hData2.1

          have hm2sigma2 :
              HilbertLineInPlane Geo m2.1 sigma2 :=
            hData2.2.1

          have hDisjoint2 :
              HilbertLinesDisjoint Geo l2.1 m2.1 :=
            hData2.2.2

          have hBsigma2 :
              S.OnPlane B.1 sigma2 :=
            hl2sigma2 B.1 hBl2

          have hBm2 :
              Not (H.OnLine B.1 m2.1) := by
            intro hBm2
            exact
              hDisjoint2
                (Exists.intro B.1
                  (And.intro hBl2 hBm2))

          have hSigma2Rho :
              sigma2 = rho :=
            hilbert_XI9_planes_eq_of_common_line_and_external_point
              (Geo := Geo)
              m2.1
              B.1
              hBm2
              sigma2 rho
              hm2sigma2
              m2.2
              hBsigma2
              hBrho

          have hl2rho :
              HilbertLineInPlane Geo l2.1 rho := by
            simpa [hSigma2Rho] using hl2sigma2

          have hl12Ambient :
              Ne l1.1 l2.1 := by
            intro hEq
            apply hl12
            exact Subtype.ext hEq

          cases
              hilbert_plane_through_two_intersecting_lines
                (Geo := Geo)
                l1.1 l2.1
                hl12Ambient
                B.1
                hBl1
                hBl2
            with
          | intro omega hOmega =>

              have hPiOmega :
                  pi = omega :=
                hOmega.2.2
                  pi
                  l1.2
                  l2.2

              have hRhoOmega :
                  rho = omega :=
                hOmega.2.2
                  rho
                  hl1rho
                  hl2rho

              have hPiRho :
                  pi = rho :=
                hPiOmega.trans hRhoOmega.symm

              exact hPlanesNe hPiRho


/--
XI.15 symmetric incidence package.

For the full XI.15 configuration, the intersection point of each
pair of given lines lies outside the opposite plane:

    B notin rho,
    E notin pi.

This is exactly the information needed before XI.11 can be applied
from `B` to `rho`.
-/
theorem hilbert_XI15_intersection_points_off_opposite_planes
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (E : PlanePoint Geo rho)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (hEm1 : H.OnLine E.1 m1.1)
    (hEm2 : H.OnLine E.1 m2.1)
    (hl12 : Ne l1 l2)
    (hm12 : Ne m1 m2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hPlanesNe : Ne pi rho) :
    Not (S.OnPlane B.1 rho) /\
    Not (S.OnPlane E.1 pi) := by

  have hBoffRho :
      Not (S.OnPlane B.1 rho) :=
    hilbert_XI15_intersection_point_off_other_plane
      (Geo := Geo)
      pi rho
      l1 l2
      m1 m2
      B
      hBl1 hBl2
      hl12
      hParallel1
      hParallel2
      hPlanesNe

  have hParallel1Symm :
      HilbertSpaceLinesParallel Geo m1.1 l1.1 :=
    hilbert_XI15_spaceLinesParallel_symm
      (Geo := Geo)
      l1.1 m1.1
      hParallel1

  have hParallel2Symm :
      HilbertSpaceLinesParallel Geo m2.1 l2.1 :=
    hilbert_XI15_spaceLinesParallel_symm
      (Geo := Geo)
      l2.1 m2.1
      hParallel2

  have hEoffPi :
      Not (S.OnPlane E.1 pi) :=
    hilbert_XI15_intersection_point_off_other_plane
      (Geo := Geo)
      rho pi
      m1 m2
      l1 l2
      E
      hEm1 hEm2
      hm12
      hParallel1Symm
      hParallel2Symm
      (Ne.symm hPlanesNe)

  exact And.intro hBoffRho hEoffPi

/--
XI.15 replacement for the literal I.31 instruction.

Let `m` be a line of the plane `rho`, and let `G` be any point of `rho`.

There are two geometric cases.

* If `G` already lies on `m`, use `m` itself.
* If `G` is outside `m`, use the XI.12 plane-slice parallel construction.

The result is always a line `q` through `G`, contained in `rho`, which is
either equal to `m` or spatially parallel to `m`.

This is the formal repair of the hidden exceptional case in Euclid XI.15.
-/
theorem hilbert_XI15_parallel_or_equal_through_point_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane)
    (m : Geo.Line)
    (G : Geo.Point)
    (hmrho : HilbertLineInPlane Geo m rho)
    (hGrho : S.OnPlane G rho) :
    exists q : Geo.Line,
      H.OnLine G q /\
      HilbertLineInPlane Geo q rho /\
      (q = m \/ HilbertSpaceLinesParallel Geo m q) := by

  by_cases hGm : H.OnLine G m

  --------------------------------------------------------------------
  -- Exceptional case: G already lies on m.
  --------------------------------------------------------------------

  · exact
      ⟨m,
       hGm,
       hmrho,
       Or.inl rfl⟩

  --------------------------------------------------------------------
  -- Generic case: apply the XI.12 plane-slice parallel construction.
  --------------------------------------------------------------------

  · rcases
        hilbert_XI12_parallel_through_point_in_plane
          (Geo := Geo)
          rho
          m
          G
          hmrho
          hGrho
          hGm
      with
      ⟨q, hGq, hParallelMq⟩

    ------------------------------------------------------------------
    -- The XI.12 helper returns ambient spatial parallelism.
    -- Recover explicitly that the constructed carrier q lies in rho.
    ------------------------------------------------------------------

    rcases hParallelMq with
      ⟨sigma,
       hmsigma,
       hqsigma,
       hDisjointMq⟩

    have hGsigma :
        S.OnPlane G sigma :=
      hqsigma G hGq

    have hSigmaRho :
        sigma = rho :=
      hilbert_XI9_planes_eq_of_common_line_and_external_point
        (Geo := Geo)
        m
        G
        hGm
        sigma rho
        hmsigma
        hmrho
        hGsigma
        hGrho

    have hqrho :
        HilbertLineInPlane Geo q rho := by
      simpa [hSigmaRho] using hqsigma

    have hParallelMq' :
        HilbertSpaceLinesParallel Geo m q :=
      ⟨sigma,
       hmsigma,
       hqsigma,
       hDisjointMq⟩

    exact
      ⟨q,
       hGq,
       hqrho,
       Or.inr hParallelMq'⟩


/--
XI.15: construct the common normal used by Euclid.

The XI.15 incidence lemma first proves that the intersection point `B`
of the two lines of `pi` lies outside the distinct plane `rho`.
Euclid XI.11 then constructs a line `n` through `B`, perpendicular to
`rho`, with foot `G`.
-/
theorem hilbert_XI15_normal_from_intersection_to_other_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (hl12 : Ne l1 l2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hPlanesNe : Ne pi rho) :
    exists n : Geo.Line,
    exists G : Geo.Point,
      H.OnLine B.1 n /\
      HilbertLinePerpendicularPlaneAt Geo n rho G := by

  have hBoffRho :
      Not (S.OnPlane B.1 rho) :=
    hilbert_XI15_intersection_point_off_other_plane
      (Geo := Geo)
      pi rho
      l1 l2
      m1 m2
      B
      hBl1 hBl2
      hl12
      hParallel1
      hParallel2
      hPlanesNe

  rcases
      euclid_proposition_11_11
        (Geo := Geo)
        rho
        B.1
        hBoffRho
    with
    ⟨n, G, hBn, hNormalRho⟩

  exact
    ⟨n, G, hBn, hNormalRho⟩


/--
XI.15 construction package through the foot of the XI.11 normal.

Starting with the two pairs of corresponding parallel lines

    l1 || m1,
    l2 || m2,

construct the XI.11 normal `n` from `B` to `rho`, with foot `G`.

Then construct through `G` two lines `q1,q2` in `rho`.
Each `qi` is either literally the corresponding `mi` or is parallel
to it.

This packages the complete formal replacement for Euclid's two I.31
instructions in XI.15, including both exceptional incidence branches.
-/
theorem hilbert_XI15_normal_and_reference_lines
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (hl12 : Ne l1 l2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hPlanesNe : Ne pi rho) :
    exists n : Geo.Line,
    exists G : Geo.Point,
    exists q1 q2 : Geo.Line,
      H.OnLine B.1 n /\
      HilbertLinePerpendicularPlaneAt Geo n rho G /\
      H.OnLine G q1 /\
      HilbertLineInPlane Geo q1 rho /\
      (q1 = m1.1 \/
        HilbertSpaceLinesParallel Geo m1.1 q1) /\
      H.OnLine G q2 /\
      HilbertLineInPlane Geo q2 rho /\
      (q2 = m2.1 \/
        HilbertSpaceLinesParallel Geo m2.1 q2) := by

  rcases
      hilbert_XI15_normal_from_intersection_to_other_plane
        (Geo := Geo)
        pi rho
        l1 l2
        m1 m2
        B
        hBl1 hBl2
        hl12
        hParallel1
        hParallel2
        hPlanesNe
    with
    ⟨n, G, hBn, hNormalRho⟩

  have hNormalInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hNormalRho

  have hGrho :
      S.OnPlane G rho :=
    hNormalInc.2

  rcases
      hilbert_XI15_parallel_or_equal_through_point_in_plane
        (Geo := Geo)
        rho
        m1.1
        G
        m1.2
        hGrho
    with
    ⟨q1,
     hGq1,
     hq1rho,
     hq1m1⟩

  rcases
      hilbert_XI15_parallel_or_equal_through_point_in_plane
        (Geo := Geo)
        rho
        m2.1
        G
        m2.2
        hGrho
    with
    ⟨q2,
     hGq2,
     hq2rho,
     hq2m2⟩

  exact
    ⟨n, G, q1, q2,
     hBn,
     hNormalRho,
     hGq1,
     hq1rho,
     hq1m1,
     hGq2,
     hq2rho,
     hq2m2⟩

/--
XI.15 transport lemma: perpendicularity across a parallel pair.

Assume `l` and `q` are spatially parallel. A transversal `n` meets
`q` at `G` and `l` at `B`, with `G != B`. If `q` is perpendicular to
`n` at `G`, then `l` is perpendicular to `n` at `B`.

The proof follows the mechanism already used in XI.8:

1. the parallelism `l || q` supplies their common carrier plane `sigma`;
2. since `B,G` lie on the transversal `n`, the whole line `n` lies in
   `sigma`;
3. inside `PlaneGeo sigma`, erect through `B` a line `p` perpendicular
   to `n`;
4. neutral I.27, via
   `hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint`,
   shows `q` and `p` are disjoint;
5. both `l` and `p` pass through `B` and are disjoint from `q`;
6. Group IV uniqueness in `sigma` gives `l = p`.

Thus `l` is perpendicular to `n` at `B`.

This is the formal XI.15 replacement for the classical I.29
right-angle transport step.
-/
theorem hilbert_XI15_perpendicular_transfer_across_parallel
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l q n : Geo.Line)
    (B G : Geo.Point)
    (hParallelLQ :
      HilbertSpaceLinesParallel Geo l q)
    (hBl : H.OnLine B l)
    (hBn : H.OnLine B n)
    (hGq : H.OnLine G q)
    (hGn : H.OnLine G n)
    (hGB : Ne G B)
    (hPerpQn :
      HilbertLinesPerpendicularAt Geo q n G) :
    HilbertLinesPerpendicularAt Geo l n B := by

  --------------------------------------------------------------------
  -- The given parallel pair supplies a common carrier plane sigma.
  --------------------------------------------------------------------

  rcases hParallelLQ with
    ⟨sigma,
     hlsigma,
     hqsigma,
     hDisjointLQ⟩

  have hBsigma :
      S.OnPlane B sigma :=
    hlsigma B hBl

  have hGsigma :
      S.OnPlane G sigma :=
    hqsigma G hGq

  --------------------------------------------------------------------
  -- The transversal n lies in sigma because B != G and both points
  -- lie on n and in sigma.
  --------------------------------------------------------------------

  have hnsigma :
      HilbertLineInPlane Geo n sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      G B hGB
      n hGn hBn
      sigma hGsigma hBsigma

  --------------------------------------------------------------------
  -- Work in PlaneGeo(sigma).
  --------------------------------------------------------------------

  let Gp : PlanePoint Geo sigma :=
    ⟨G, hGsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let np : PlaneLine Geo sigma :=
    ⟨n, hnsigma⟩

  have hGBp :
      Ne Gp Bp := by
    intro h
    apply hGB
    exact congrArg Subtype.val h

  have hGnp :
      PlaneOnLine Geo Gp np :=
    hGn

  have hBnp :
      PlaneOnLine Geo Bp np :=
    hBn

  --------------------------------------------------------------------
  -- Extend G-B beyond B in the induced plane.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo sigma)
        Gp Bp hGBp
    with
    ⟨Xp, hGBX⟩

  --------------------------------------------------------------------
  -- Erect at B a nondegenerate right-angle direction to n.
  --------------------------------------------------------------------

  rcases
      hilbert_right_angle_exists_nondegenerate
        (PlaneGeo Geo sigma)
        Gp Bp Xp hGBX
    with
    ⟨Yp, hNonGBY, hRightGBY⟩

  have hBYp :
      Ne Bp Yp := by
    intro h
    subst Yp
    apply hNonGBY
    exact
      ⟨np,
       hGnp,
       hBnp,
       hBnp⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        Bp Yp hBYp
    with
    ⟨pp, hBpp, hYpp⟩

  --------------------------------------------------------------------
  -- Package n perpendicular p at B in PlaneGeo(sigma).
  --------------------------------------------------------------------

  have hPerpNpPp :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma)
        np pp Bp :=
    ⟨hBnp,
     hBpp,
     Gp,
     Yp,
     hGBp,
     hBYp.symm,
     hGnp,
     hYpp,
     hNonGBY,
     hRightGBY⟩

  have hPerpAmbientNP :
      HilbertLinesPerpendicularAt
        Geo n pp.1 B :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma np pp Bp).mp
      hPerpNpPp

  have hPerpPn :
      HilbertLinesPerpendicularAt
        Geo pp.1 n B :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      n pp.1 B
      hPerpAmbientNP

  --------------------------------------------------------------------
  -- Neutral I.27:
  -- q and p are perpendicular to the same transversal n at
  -- distinct feet G and B, hence they are disjoint.
  --------------------------------------------------------------------

  have hDisjointQP :
      HilbertLinesDisjoint Geo q pp.1 :=
    hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint
      (Geo := Geo)
      sigma
      q pp.1 n
      G B
      hGB
      hqsigma
      pp.2
      hnsigma
      hPerpQn
      hPerpPn

  --------------------------------------------------------------------
  -- Reorient q,p disjointness for Group IV.
  --------------------------------------------------------------------

  have hDisjointPQ :
      HilbertLinesDisjoint Geo pp.1 q := by
    rintro ⟨P, hPp, hPq⟩
    exact
      hDisjointQP
        ⟨P, hPq, hPp⟩

  --------------------------------------------------------------------
  -- B is outside q, since B lies on l and l,q are disjoint.
  --------------------------------------------------------------------

  have hBq :
      Not (H.OnLine B q) := by
    intro hBq
    exact
      hDisjointLQ
        ⟨B, hBl, hBq⟩

  --------------------------------------------------------------------
  -- Group IV:
  -- l and p are the unique parallels to q through B in sigma.
  --------------------------------------------------------------------

  have hlp :
      l = pp.1 :=
    HSE.parallel_unique_in_plane
      sigma
      q hqsigma
      B hBsigma hBq
      l pp.1
      hlsigma pp.2
      hBl hDisjointLQ
      hBpp hDisjointPQ

  --------------------------------------------------------------------
  -- Replace p by l.
  --------------------------------------------------------------------

  rw [hlp]

  exact
    hPerpPn


/--
XI.15 normal-to-parallel-line wrapper.

Let `n` be perpendicular to the plane `rho` at `G`. Let `q` be a
line of `rho` through `G`. Then XI.Def.3 gives `n perpendicular q`
at `G`.

If another line `l` through `B` is spatially parallel to `q`, then
the preceding transport lemma gives `n perpendicular l` at `B`.

The distinctness of the feet is automatic: if `B = G`, the parallel
lines `l,q` would have a common point.
-/
theorem hilbert_XI15_plane_normal_perpendicular_to_parallel_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (rho : S.Plane)
    (n q l : Geo.Line)
    (G B : Geo.Point)
    (hNormalRho :
      HilbertLinePerpendicularPlaneAt Geo n rho G)
    (hqrho :
      HilbertLineInPlane Geo q rho)
    (hGq :
      H.OnLine G q)
    (hParallelLQ :
      HilbertSpaceLinesParallel Geo l q)
    (hBl :
      H.OnLine B l)
    (hBn :
      H.OnLine B n) :
    HilbertLinesPerpendicularAt Geo n l B := by

  --------------------------------------------------------------------
  -- Incidence of the normal at its foot.
  --------------------------------------------------------------------

  have hNormalInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hNormalRho

  have hGn :
      H.OnLine G n :=
    hNormalInc.1

  --------------------------------------------------------------------
  -- XI.Def.3: n is perpendicular to q at G.
  --------------------------------------------------------------------

  have hPerpNQ :
      HilbertLinesPerpendicularAt Geo n q G :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hNormalRho
      hqrho
      hGq

  have hPerpQn :
      HilbertLinesPerpendicularAt Geo q n G :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      n q G
      hPerpNQ

  --------------------------------------------------------------------
  -- The two parallel carriers cannot share the point B=G.
  --------------------------------------------------------------------

  have hGB :
      Ne G B := by
    intro hGBEq
    subst B

    rcases hParallelLQ with
      ⟨sigma,
       _hlsigma,
       _hqsigma,
       hDisjointLQ⟩

    exact
      hDisjointLQ
        ⟨G, hBl, hGq⟩

  --------------------------------------------------------------------
  -- I.29-type transport.
  --------------------------------------------------------------------

  have hPerpLn :
      HilbertLinesPerpendicularAt Geo l n B :=
    hilbert_XI15_perpendicular_transfer_across_parallel
      (Geo := Geo)
      l q n
      B G
      hParallelLQ
      hBl
      hBn
      hGq
      hGn
      hGB
      hPerpQn

  exact
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      l n B
      hPerpLn

/--
Strict transitivity of spatial parallelism.

If `l || m` and `m || q`, and the two outer lines are distinct, then
`l || q`.

There are two cases.

* If `l,m,q` lie in one plane, Group IV shows that an intersection of
  `l` and `q` would force `l = q`, contradicting the explicit outer
  distinctness.
* If there is no common plane containing all three lines, Euclid XI.9
  applies directly.

The explicit hypothesis `l != q` is necessary because project
parallelism is strict: a line is not parallel to itself.
-/
theorem hilbert_XI15_spaceParallel_transitive_distinct
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m q : Geo.Line)
    (hLM :
      HilbertSpaceLinesParallel Geo l m)
    (hMQ :
      HilbertSpaceLinesParallel Geo m q)
    (hLQne : Ne l q) :
    HilbertSpaceLinesParallel Geo l q := by

  by_cases hCommon :
      exists omega : S.Plane,
        HilbertLineInPlane Geo l omega /\
        HilbertLineInPlane Geo m omega /\
        HilbertLineInPlane Geo q omega

  --------------------------------------------------------------------
  -- Coplanar case: Group IV.
  --------------------------------------------------------------------

  · rcases hCommon with
      ⟨omega, hlomega, hmomega, hqomega⟩

    rcases hLM with
      ⟨sigmaLM,
       _hlsigmaLM,
       _hmsigmaLM,
       hDisjointLM⟩

    rcases hMQ with
      ⟨sigmaMQ,
       _hmsigmaMQ,
       _hqsigmaMQ,
       hDisjointMQ⟩

    have hDisjointQM :
        HilbertLinesDisjoint Geo q m := by
      rintro ⟨P, hPq, hPm⟩
      exact
        hDisjointMQ
          ⟨P, hPm, hPq⟩

    have hDisjointLQ :
        HilbertLinesDisjoint Geo l q := by
      rintro ⟨P, hPl, hPq⟩

      have hPm :
          Not (H.OnLine P m) := by
        intro hPm
        exact
          hDisjointLM
            ⟨P, hPl, hPm⟩

      have hlq :
          l = q :=
        HSE.parallel_unique_in_plane
          omega
          m hmomega
          P
          (hlomega P hPl)
          hPm
          l q
          hlomega hqomega
          hPl hDisjointLM
          hPq hDisjointQM

      exact
        hLQne hlq

    exact
      ⟨omega,
       hlomega,
       hqomega,
       hDisjointLQ⟩

  --------------------------------------------------------------------
  -- Noncoplanar case: XI.9.
  --------------------------------------------------------------------

  · have hQM :
        HilbertSpaceLinesParallel Geo q m :=
      hilbert_XI15_spaceLinesParallel_symm
        (Geo := Geo)
        m q
        hMQ

    have hNoCommonLQM :
        Not (exists omega : S.Plane,
          HilbertLineInPlane Geo l omega /\
          HilbertLineInPlane Geo q omega /\
          HilbertLineInPlane Geo m omega) := by
      rintro ⟨omega, hlomega, hqomega, hmomega⟩
      exact
        hCommon
          ⟨omega, hlomega, hmomega, hqomega⟩

    exact
      euclid_proposition_11_9
        (Geo := Geo)
        l q m
        hLM
        hQM
        hNoCommonLQM


/--
XI.15 normalized geometric core.

Two distinct intersecting lines `l1,l2` lie in `pi` and meet at `B`.
Two distinct intersecting reference lines `m1,m2` lie in `rho`.
The corresponding pairs are spatially parallel:

    l1 || m1,
    l2 || m2.

Assume `pi != rho`.

The theorem constructs Euclid's XI.11 normal `n` from `B` to `rho`,
handles both hidden I.31 exceptional cases at its foot `G`, transports
the two right angles back to `l1,l2`, applies XI.4 to obtain

    n perpendicular pi,

and finally XI.14 to conclude

    pi || rho.
-/
theorem euclid_proposition_11_15_normalized
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (hl12 : Ne l1 l2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hPlanesNe : Ne pi rho) :
    HilbertSpacePlanesParallel Geo pi rho := by

  --------------------------------------------------------------------
  -- B lies outside rho.
  --------------------------------------------------------------------

  have hBoffRho :
      Not (S.OnPlane B.1 rho) :=
    hilbert_XI15_intersection_point_off_other_plane
      (Geo := Geo)
      pi rho
      l1 l2
      m1 m2
      B
      hBl1 hBl2
      hl12
      hParallel1
      hParallel2
      hPlanesNe

  --------------------------------------------------------------------
  -- XI.11 normal and the two reference lines through its foot.
  --------------------------------------------------------------------

  rcases
      hilbert_XI15_normal_and_reference_lines
        (Geo := Geo)
        pi rho
        l1 l2
        m1 m2
        B
        hBl1 hBl2
        hl12
        hParallel1
        hParallel2
        hPlanesNe
    with
    ⟨n, G, q1, q2,
     hBn,
     hNormalRho,
     hGq1,
     hq1rho,
     hq1m1,
     hGq2,
     hq2rho,
     hq2m2⟩

  --------------------------------------------------------------------
  -- First direction: prove l1 || q1.
  --------------------------------------------------------------------

  have hParallelL1Q1 :
      HilbertSpaceLinesParallel Geo l1.1 q1 := by

    rcases hq1m1 with hq1eq | hParallelM1Q1

    · simpa [hq1eq] using hParallel1

    · have hL1Q1ne :
          Ne l1.1 q1 := by
        intro hEq

        have hBq1 :
            H.OnLine B.1 q1 := by
          rw [← hEq]
          exact hBl1

        exact
          hBoffRho
            (hq1rho B.1 hBq1)

      exact
        hilbert_XI15_spaceParallel_transitive_distinct
          (Geo := Geo)
          l1.1 m1.1 q1
          hParallel1
          hParallelM1Q1
          hL1Q1ne

  --------------------------------------------------------------------
  -- Second direction: prove l2 || q2.
  --------------------------------------------------------------------

  have hParallelL2Q2 :
      HilbertSpaceLinesParallel Geo l2.1 q2 := by

    rcases hq2m2 with hq2eq | hParallelM2Q2

    · simpa [hq2eq] using hParallel2

    · have hL2Q2ne :
          Ne l2.1 q2 := by
        intro hEq

        have hBq2 :
            H.OnLine B.1 q2 := by
          rw [← hEq]
          exact hBl2

        exact
          hBoffRho
            (hq2rho B.1 hBq2)

      exact
        hilbert_XI15_spaceParallel_transitive_distinct
          (Geo := Geo)
          l2.1 m2.1 q2
          hParallel2
          hParallelM2Q2
          hL2Q2ne

  --------------------------------------------------------------------
  -- Transport the two perpendicularities from rho back to pi.
  --------------------------------------------------------------------

  have hPerpNL1 :
      HilbertLinesPerpendicularAt
        Geo n l1.1 B.1 :=
    hilbert_XI15_plane_normal_perpendicular_to_parallel_line
      (Geo := Geo)
      rho
      n q1 l1.1
      G B.1
      hNormalRho
      hq1rho
      hGq1
      hParallelL1Q1
      hBl1
      hBn

  have hPerpNL2 :
      HilbertLinesPerpendicularAt
        Geo n l2.1 B.1 :=
    hilbert_XI15_plane_normal_perpendicular_to_parallel_line
      (Geo := Geo)
      rho
      n q2 l2.1
      G B.1
      hNormalRho
      hq2rho
      hGq2
      hParallelL2Q2
      hBl2
      hBn

  --------------------------------------------------------------------
  -- XI.4: n is perpendicular to pi at B.
  --------------------------------------------------------------------

  have hNormalPi :
      HilbertLinePerpendicularPlaneAt
        Geo n pi B.1 :=
    euclid_proposition_11_4
      (Geo := Geo)
      pi
      l1 l2
      n
      B
      hl12
      hPerpNL1
      hPerpNL2

  --------------------------------------------------------------------
  -- XI.14: the same line n is perpendicular to both planes.
  --------------------------------------------------------------------

  exact
    euclid_proposition_11_14
      (Geo := Geo)
      pi rho
      n
      B.1 G
      hPlanesNe
      hNormalPi
      hNormalRho

/--
Euclid XI.15 -- public spatial line/plane formulation.

Let `l1,l2` be two distinct lines of the plane `pi`, meeting at `B`.
Let `m1,m2` be two lines of the plane `rho`. Suppose the corresponding
pairs are spatially parallel:

    l1 || m1,
    l2 || m2.

Assume that the four lines are not all contained in one ambient plane.

Then the planes `pi` and `rho` are parallel.

The formal statement is slightly stronger than Euclid's literal wording:
Euclid also describes `m1,m2` as meeting. That extra intersection datum
is not required by the present proof once the first pair `l1,l2` meets
and the two corresponding spatial parallelisms are given.

The proof is a thin source-facing wrapper:

    four lines not coplanar
          |
          v
       pi != rho
          |
          v
    XI.15 normalized core
          |
          v
       pi || rho
-/
theorem euclid_proposition_11_15
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (hl12 : Ne l1 l2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hNoCommonPlane :
      Not (exists omega : S.Plane,
        HilbertLineInPlane Geo l1.1 omega /\
        HilbertLineInPlane Geo l2.1 omega /\
        HilbertLineInPlane Geo m1.1 omega /\
        HilbertLineInPlane Geo m2.1 omega)) :
    HilbertSpacePlanesParallel Geo pi rho := by

  --------------------------------------------------------------------
  -- The source condition "the four lines are not in one plane"
  -- immediately implies that the two displayed carrier planes differ.
  --------------------------------------------------------------------

  have hPlanesNe :
      Ne pi rho := by
    intro hPiRho

    have hm1pi :
        HilbertLineInPlane Geo m1.1 pi := by
      rw [hPiRho]
      exact m1.2

    have hm2pi :
        HilbertLineInPlane Geo m2.1 pi := by
      rw [hPiRho]
      exact m2.2

    exact
      hNoCommonPlane
        (Exists.intro pi
          (And.intro
            l1.2
            (And.intro
              l2.2
              (And.intro
                hm1pi
                hm2pi))))

  --------------------------------------------------------------------
  -- All substantial geometry is already isolated in the normalized core.
  --------------------------------------------------------------------

  exact
    euclid_proposition_11_15_normalized
      (Geo := Geo)
      pi rho
      l1 l2
      m1 m2
      B
      hBl1 hBl2
      hl12
      hParallel1
      hParallel2
      hPlanesNe


/--
A source-style corollary making the second displayed intersection explicit.

This version adds a point `E` lying on both `m1` and `m2`, together with
`m1 != m2`, exactly matching Euclid's description of a second pair of
intersecting straight lines.

The extra data are mathematically compatible with XI.15 but are not needed
by the stronger public core above.
-/
theorem euclid_proposition_11_15_intersecting_pairs
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l1 l2 : PlaneLine Geo pi)
    (m1 m2 : PlaneLine Geo rho)
    (B : PlanePoint Geo pi)
    (_E : PlanePoint Geo rho)
    (hBl1 : H.OnLine B.1 l1.1)
    (hBl2 : H.OnLine B.1 l2.1)
    (_hEm1 : H.OnLine _E.1 m1.1)
    (_hEm2 : H.OnLine _E.1 m2.1)
    (hl12 : Ne l1 l2)
    (_hm12 : Ne m1 m2)
    (hParallel1 :
      HilbertSpaceLinesParallel Geo l1.1 m1.1)
    (hParallel2 :
      HilbertSpaceLinesParallel Geo l2.1 m2.1)
    (hNoCommonPlane :
      Not (exists omega : S.Plane,
        HilbertLineInPlane Geo l1.1 omega /\
        HilbertLineInPlane Geo l2.1 omega /\
        HilbertLineInPlane Geo m1.1 omega /\
        HilbertLineInPlane Geo m2.1 omega)) :
    HilbertSpacePlanesParallel Geo pi rho := by

  exact
    euclid_proposition_11_15
      (Geo := Geo)
      pi rho
      l1 l2
      m1 m2
      B
      hBl1 hBl2
      hl12
      hParallel1
      hParallel2
      hNoCommonPlane

end Geometry

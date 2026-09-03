import CGJteamLab.Proposition11_13

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A point `F` is a perpendicular foot of `P` on the plane `pi`
when there is an ambient line through `P` perpendicular to `pi` at `F`.

The incidence of `F` with the line and the plane is already contained in
`HilbertLinePerpendicularPlaneAt`.
-/
def PerpendicularToPlaneThrough
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (F P : Geo.Point) : Prop :=
  exists l : Geo.Line,
    H.OnLine P l /\
    HilbertLinePerpendicularPlaneAt Geo l pi F

/--
Relational definition of reflection in an ambient plane.

Points on the mirror plane are fixed.  A point off the plane is reflected
across its perpendicular foot, which is the midpoint of the original point
and its image.

At this stage this is only the relation.  Existence and uniqueness will be
proved separately, exactly as for `IsLineReflection`.
-/
def IsPlaneReflection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P P' : Geo.Point) : Prop :=
  (S.OnPlane P pi /\ P' = P) \/
  (Not (S.OnPlane P pi) /\
    exists F : Geo.Point,
      PerpendicularToPlaneThrough Geo pi F P /\
      HilbertIsMidpoint Geo F P P')

/--
A point on the mirror plane satisfies the plane-reflection relation with
itself.
-/
theorem plane_reflection_relation_fixed_on_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P : Geo.Point)
    (hPpi : S.OnPlane P pi) :
    IsPlaneReflection Geo pi P P := by
  exact Or.inl <| And.intro hPpi rfl

/--
XI.11 supplies a perpendicular foot for every point outside the plane.

This is the first existence component needed for plane reflection.
-/
theorem plane_perpendicular_foot_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point)
    (hPpi : Not (S.OnPlane P pi)) :
    exists F : Geo.Point,
      PerpendicularToPlaneThrough Geo pi F P := by

  cases
      euclid_proposition_11_11
        (Geo := Geo)
        pi P hPpi with
  | intro l hRest =>
      cases hRest with
      | intro F hData =>
          exact
            Exists.intro F
              (Exists.intro l
                (And.intro hData.1 hData.2))


/--
For every point outside a plane, construct a point on the opposite side
of the perpendicular foot so that the foot is the midpoint of the
original point and the constructed point.

The construction is reduced to the already available planar theorem
`hilbert_extend_segment_beyond` inside one ambient plane containing
the normal line. The final plane-to-ambient transport is performed
through the explicit `planeGeo_between` and `planeGeo_congruent` bridges.
-/
theorem plane_reflection_midpoint_exists_off_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point)
    (hPpi : Not (S.OnPlane P pi)) :
    exists F P' : Geo.Point,
      PerpendicularToPlaneThrough Geo pi F P /\
      HilbertIsMidpoint Geo F P P' := by

  rcases
      euclid_proposition_11_11
        (Geo := Geo)
        pi P hPpi with
    ⟨l, F, hPl, hPerp⟩

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hFl : H.OnLine F l := hInc.1
  have hFpi : S.OnPlane F pi := hInc.2

  have hPF : Ne P F := by
    intro hEq
    apply hPpi
    rw [hEq]
    exact hFpi

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨Q, hQl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l Q hQl with
    ⟨sigma, hlsigma, _hQsigma, _hUniqueSigma⟩

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hlsigma P hPl⟩

  let Fp : PlanePoint Geo sigma :=
    ⟨F, hlsigma F hFl⟩

  have hPFp : Ne Pp Fp := by
    intro hEq
    apply hPF
    exact congrArg Subtype.val hEq

  rcases
      hilbert_extend_segment_beyond
        (PlaneGeo Geo sigma)
        Pp Fp hPFp with
    ⟨Pp', hPFP', hPF_FP'⟩

  let P' : Geo.Point := Pp'.1

  have hBetweenAmbient :
      Geo.Between Pp.1 Fp.1 Pp'.1 :=
    (planeGeo_between
      (Geo := Geo)
      sigma Pp Fp Pp').mp
      hPFP'

  have hCongAmbient :
      Geo.Congruent Pp.1 Fp.1 Fp.1 Pp'.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      sigma Pp Fp Fp Pp').mp
      hPF_FP'

  have hBetween : Geo.Between P F P' := by
    simpa [Pp, Fp, P'] using hBetweenAmbient

  have hCong : Geo.Congruent P F F P' := by
    simpa [Pp, Fp, P'] using hCongAmbient

  have hMid : HilbertIsMidpoint Geo F P P' :=
    ⟨hBetween, hCong⟩

  have hPerpThrough :
      PerpendicularToPlaneThrough Geo pi F P :=
    ⟨l, hPl, hPerp⟩

  exact ⟨F, P', hPerpThrough, hMid⟩


/--
Every ambient point has a reflection with respect to a fixed plane.

Points on the mirror plane are fixed. For points outside the plane,
`plane_reflection_midpoint_exists_off_plane` supplies the
perpendicular foot and the opposite point with that foot as midpoint.
-/
theorem plane_reflection_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point) :
    exists P' : Geo.Point,
      IsPlaneReflection Geo pi P P' := by

  by_cases hPpi : S.OnPlane P pi

  · exact
      ⟨P,
       Or.inl
         ⟨hPpi, rfl⟩⟩

  · rcases
      plane_reflection_midpoint_exists_off_plane
        (Geo := Geo)
        pi P hPpi with
    ⟨F, P', hPerp, hMid⟩

    exact
      ⟨P',
       Or.inr
         ⟨hPpi,
          ⟨F,
           hPerp,
           hMid⟩⟩⟩


/--
The perpendicular foot of a fixed point on a fixed plane is unique.

If two distinct feet F and G existed, the corresponding normal lines
would be parallel by Euclid XI.6. But both lines pass through P, so they
would meet at P, contradicting the disjointness contained in spatial
parallelism.
-/
theorem plane_perpendicular_foot_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (P F G : Geo.Point)
    (hPerpF :
      PerpendicularToPlaneThrough Geo pi F P)
    (hPerpG :
      PerpendicularToPlaneThrough Geo pi G P) :
    F = G := by

  rcases hPerpF with
    ⟨l, hPl, hLperp⟩

  rcases hPerpG with
    ⟨m, hPm, hMperp⟩

  by_contra hFG

  have hParallel :
      HilbertSpaceLinesParallel Geo l m :=
    euclid_proposition_11_6
      (Geo := Geo)
      pi l m
      F G
      hFG
      hLperp
      hMperp

  rcases hParallel with
    ⟨_sigma, _hlsigma, _hmsigma, hDisjoint⟩

  exact
    hDisjoint
      ⟨P, hPl, hPm⟩


/--
A reflected point across a fixed plane is unique.

For points outside the plane:
1. the perpendicular feet coincide by `plane_perpendicular_foot_unique`;
2. both candidate reflected points lie on the common normal line;
3. inside one plane containing that normal, the two midpoint conditions
   imply equal total distances from P;
4. planar segment-construction uniqueness identifies the two points.
-/
theorem plane_reflection_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P P1 P2 : Geo.Point)
    (hRef1 : IsPlaneReflection Geo pi P P1)
    (hRef2 : IsPlaneReflection Geo pi P P2) :
    P1 = P2 := by

  rcases hRef1 with hFixed1 | hOff1
  · rcases hFixed1 with ⟨hPpi, hP1⟩
    rcases hRef2 with hFixed2 | hOff2
    · rcases hFixed2 with ⟨_hPpi2, hP2⟩
      simp [hP1, hP2]
    · exact False.elim (hOff2.1 hPpi)

  · rcases hRef2 with hFixed2 | hOff2
    · exact False.elim (hOff1.1 hFixed2.1)

    · rcases hOff1 with
        ⟨_hPoff1, F, hPerpF, hMid1⟩
      rcases hOff2 with
        ⟨_hPoff2, G, hPerpG, hMid2⟩

      ------------------------------------------------------------------
      -- The two perpendicular feet coincide.
      ------------------------------------------------------------------

      have hFG : F = G :=
        plane_perpendicular_foot_unique
          (Geo := Geo)
          pi P F G
          hPerpF hPerpG

      subst G

      ------------------------------------------------------------------
      -- Use the first normal line as the common carrier.
      ------------------------------------------------------------------

      rcases hPerpF with
        ⟨l, hPl, hLperp⟩

      have hInc :=
        HilbertLinePerpendicularPlaneAt.incidence
          (Geo := Geo) hLperp

      have hFl : H.OnLine F l := hInc.1

      have hData1 :=
        HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          P F P1 hMid1.1

      have hData2 :=
        HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          P F P2 hMid2.1

      have hPF : Ne P F := hData1.1

      have hP1l : H.OnLine P1 l :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hPF
          hPl hFl
          hData1.2.2.2.1

      have hP2l : H.OnLine P2 l :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hPF
          hPl hFl
          hData2.2.2.2.1

      ------------------------------------------------------------------
      -- Put the whole one-dimensional configuration in one PlaneGeo.
      ------------------------------------------------------------------

      rcases
          hilbert_point_off_line
            (Geo := Geo) l with
        ⟨Q, hQl⟩

      rcases
          hilbert_plane_through_line_and_external_point
            (Geo := Geo)
            l Q hQl with
        ⟨sigma, hlsigma, _hQsigma, _hUniqueSigma⟩

      let Pp : PlanePoint Geo sigma :=
        ⟨P, hlsigma P hPl⟩

      let Fp : PlanePoint Geo sigma :=
        ⟨F, hlsigma F hFl⟩

      let P1p : PlanePoint Geo sigma :=
        ⟨P1, hlsigma P1 hP1l⟩

      let P2p : PlanePoint Geo sigma :=
        ⟨P2, hlsigma P2 hP2l⟩

      have hBetween1 :
          (PlaneGeo Geo sigma).Between Pp Fp P1p :=
        (planeGeo_between
          (Geo := Geo)
          sigma Pp Fp P1p).mpr
          hMid1.1

      have hBetween2 :
          (PlaneGeo Geo sigma).Between Pp Fp P2p :=
        (planeGeo_between
          (Geo := Geo)
          sigma Pp Fp P2p).mpr
          hMid2.1

      have hCong1 :
          (PlaneGeo Geo sigma).Congruent Pp Fp Fp P1p :=
        (planeGeo_congruent
          (Geo := Geo)
          sigma Pp Fp Fp P1p).mpr
          hMid1.2

      have hCong2 :
          (PlaneGeo Geo sigma).Congruent Pp Fp Fp P2p :=
        (planeGeo_congruent
          (Geo := Geo)
          sigma Pp Fp Fp P2p).mpr
          hMid2.2

      ------------------------------------------------------------------
      -- Both reflected candidates lie on the same ray P-F.
      ------------------------------------------------------------------

      have hRay1 :
          HilbertSameRay
            (PlaneGeo Geo sigma) Pp Fp P1p :=
        hilbert_sameRay_of_between
          (PlaneGeo Geo sigma)
          Pp Fp P1p
          hBetween1

      have hRay2 :
          HilbertSameRay
            (PlaneGeo Geo sigma) Pp Fp P2p :=
        hilbert_sameRay_of_between
          (PlaneGeo Geo sigma)
          Pp Fp P2p
          hBetween2

      ------------------------------------------------------------------
      -- III.2: FP1 and FP2 are congruent because both are congruent PF.
      ------------------------------------------------------------------

      have hFP1_FP2 :
          (PlaneGeo Geo sigma).Congruent
            Fp P1p Fp P2p :=
        HilbertCongruence.segment_congruence_common
          (Geo := PlaneGeo Geo sigma)
          Pp Fp
          Fp P1p
          Fp P2p
          hCong1 hCong2

      ------------------------------------------------------------------
      -- III.3: therefore the total segments PP1 and PP2 are congruent.
      ------------------------------------------------------------------

      have hPP1_PP2 :
          (PlaneGeo Geo sigma).Congruent
            Pp P1p Pp P2p :=
        HilbertCongruence.segment_additivity
          (Geo := PlaneGeo Geo sigma)
          Pp Fp P1p
          Pp Fp P2p
          hBetween1
          hBetween2
          (hilbert_congruent_reflexive
            (PlaneGeo Geo sigma) Pp Fp)
          hFP1_FP2

      ------------------------------------------------------------------
      -- Uniqueness on the prescribed ray.
      -- Use PP2 as the reference segment; P2 and P1 are both copies.
      ------------------------------------------------------------------

      have hP2P1 :
          P2p = P1p :=
        hilbert_segment_construction_unique
          (PlaneGeo Geo sigma)
          Pp P2p
          Pp Fp
          P2p P1p
          hRay2
          hRay1
          (hilbert_congruent_reflexive
            (PlaneGeo Geo sigma) Pp P2p)
          hPP1_PP2

      exact
        (congrArg Subtype.val hP2P1).symm


/--
Plane reflection is symmetric as a geometric relation.

For an off-plane point, the same normal line carries the reflected point.
The midpoint condition is reversed using spatial order and ambient
segment-congruence symmetry.
-/
theorem plane_reflection_symmetric
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (P P' : Geo.Point)
    (hRef : IsPlaneReflection Geo pi P P') :
    IsPlaneReflection Geo pi P' P := by

  rcases hRef with hFixed | hOff

  ----------------------------------------------------------------------
  -- Point on the mirror plane: fixed.
  ----------------------------------------------------------------------

  · rcases hFixed with ⟨hPpi, hEq⟩
    subst P'
    exact Or.inl ⟨hPpi, rfl⟩

  ----------------------------------------------------------------------
  -- Point outside the mirror plane.
  ----------------------------------------------------------------------

  · rcases hOff with
      ⟨hPoff, F, hPerp, hMid⟩

    rcases hPerp with
      ⟨l, hPl, hLperp⟩

    have hInc :=
      HilbertLinePerpendicularPlaneAt.incidence
        (Geo := Geo) hLperp

    have hFl : H.OnLine F l := hInc.1
    have hFpi : S.OnPlane F pi := hInc.2

    have hBetweenData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        P F P' hMid.1

    have hFP' : Ne F P' :=
      hBetweenData.2.1

    have hPF : Ne P F :=
      hBetweenData.1

    have hPFP'col :
        PrimCollinear Geo P F P' :=
      hBetweenData.2.2.2.1

    --------------------------------------------------------------------
    -- P' lies on the same normal line l.
    --------------------------------------------------------------------

    have hP'l : H.OnLine P' l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hPFP'col

    --------------------------------------------------------------------
    -- P' cannot lie in pi: l meets pi only at its perpendicular foot F.
    --------------------------------------------------------------------

    have hP'off : Not (S.OnPlane P' pi) := by
      intro hP'pi

      have hEq :
          P' = F :=
        hilbert_XI12_perpendicular_foot_unique
          (Geo := Geo)
          pi l F P'
          hLperp
          hP'l
          hP'pi

      exact hFP' hEq.symm

    --------------------------------------------------------------------
    -- The same normal line witnesses perpendicularity for P'.
    --------------------------------------------------------------------

    have hPerp' :
        PerpendicularToPlaneThrough Geo pi F P' :=
      ⟨l, hP'l, hLperp⟩

    --------------------------------------------------------------------
    -- Reverse the midpoint relation.
    --------------------------------------------------------------------

    have hBetween' : Geo.Between P' F P :=
      hBetweenData.2.2.2.2

    have hCongSym :
        Geo.Congruent F P' P F :=
      hilbert_space_congruent_symmetry
        (Geo := Geo)
        P F F P'
        hPF
        hMid.2

    have hCongFirst :
        Geo.Congruent P' F P F :=
      (Geometry.Geo.congruent_reverse_first
        Geo
        F P'
        P F).mp
        hCongSym

    have hCong' :
        Geo.Congruent P' F F P :=
      (Geometry.Geo.congruent_reverse_second
        Geo
        P' F
        P F).mp
        hCongFirst

    have hMid' :
        HilbertIsMidpoint Geo F P' P :=
      ⟨hBetween', hCong'⟩

    exact
      Or.inr
        ⟨hP'off,
         ⟨F, hPerp', hMid'⟩⟩


/--
The reflected point across a fixed plane.

Existence and uniqueness have already been proved, so
`IsPlaneReflection` determines an actual point transformation.
-/
noncomputable def planeReflect
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point) : Geo.Point :=
  Classical.choose
    (plane_reflection_exists
      (Geo := Geo) pi P)


/--
Specification theorem for `planeReflect`.
-/
theorem planeReflect_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point) :
    IsPlaneReflection Geo pi P
      (planeReflect Geo pi P) :=
  Classical.choose_spec
    (plane_reflection_exists
      (Geo := Geo) pi P)


/--
Reflection in a plane is an involution.
-/
theorem planeReflect_involutive
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
    (P : Geo.Point) :
    planeReflect Geo pi
      (planeReflect Geo pi P) = P := by

  have hForward :
      IsPlaneReflection Geo pi P
        (planeReflect Geo pi P) :=
    planeReflect_spec
      (Geo := Geo) pi P

  have hBackward :
      IsPlaneReflection Geo pi
        (planeReflect Geo pi P) P :=
    plane_reflection_symmetric
      (Geo := Geo)
      pi P
      (planeReflect Geo pi P)
      hForward

  have hSecond :
      IsPlaneReflection Geo pi
        (planeReflect Geo pi P)
        (planeReflect Geo pi
          (planeReflect Geo pi P)) :=
    planeReflect_spec
      (Geo := Geo)
      pi
      (planeReflect Geo pi P)

  have hUnique :
      P =
        planeReflect Geo pi
          (planeReflect Geo pi P) :=
    plane_reflection_unique
      (Geo := Geo)
      pi
      (planeReflect Geo pi P)
      P
      (planeReflect Geo pi
        (planeReflect Geo pi P))
      hBackward
      hSecond

  exact hUnique.symm


/--
Reflection in a Hilbert plane, viewed as a permutation of the ambient
point set.

The inverse is the same reflection, by involutivity.
-/
noncomputable def planeReflectEquiv
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane) :
    Equiv Geo.Point Geo.Point where

  toFun :=
    planeReflect Geo pi

  invFun :=
    planeReflect Geo pi

  left_inv :=
    planeReflect_involutive
      (Geo := Geo) pi

  right_inv :=
    planeReflect_involutive
      (Geo := Geo) pi


@[simp]
theorem planeReflectEquiv_apply
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
    (P : Geo.Point) :
    planeReflectEquiv Geo pi P =
      planeReflect Geo pi P := by

  rfl


@[simp]
theorem planeReflectEquiv_apply_twice
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
    (P : Geo.Point) :
    planeReflectEquiv Geo pi
      (planeReflectEquiv Geo pi P) = P := by

  exact
    planeReflect_involutive
      (Geo := Geo) pi P


/--
The fixed points of the plane-reflection relation are exactly the
points of the mirror plane.
-/
theorem plane_reflection_fixed_iff_on_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (P : Geo.Point) :
    Iff
      (IsPlaneReflection Geo pi P P)
      (S.OnPlane P pi) := by

  constructor

  · intro hRef
    rcases hRef with hFixed | hOff

    · exact hFixed.1

    · rcases hOff with
        ⟨_hPoff, F, _hPerp, hMid⟩

      have hPP : Ne P P :=
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          P F P hMid.1).2.2.1

      exact False.elim (hPP rfl)

  · intro hPpi
    exact
      Or.inl
        ⟨hPpi, rfl⟩


/--
Every point of the mirror plane is fixed by `planeReflect`.
-/
@[simp]
theorem planeReflect_of_on_plane
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
    (P : Geo.Point)
    (hPpi : S.OnPlane P pi) :
    planeReflect Geo pi P = P := by

  have hId :
      IsPlaneReflection Geo pi P P :=
    Or.inl
      ⟨hPpi, rfl⟩

  have hSpec :
      IsPlaneReflection Geo pi P
        (planeReflect Geo pi P) :=
    planeReflect_spec
      (Geo := Geo) pi P

  exact
    plane_reflection_unique
      (Geo := Geo)
      pi P
      (planeReflect Geo pi P)
      P
      hSpec
      hId


/--
A point is fixed by the actual transformation `planeReflect`
if and only if it lies in the mirror plane.
-/
@[simp]
theorem planeReflect_fixed_iff_on_plane
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
    (P : Geo.Point) :
    Iff
      (planeReflect Geo pi P = P)
      (S.OnPlane P pi) := by

  constructor

  · intro hEq

    have hSpec :
        IsPlaneReflection Geo pi P
          (planeReflect Geo pi P) :=
      planeReflect_spec
        (Geo := Geo) pi P

    rw [hEq] at hSpec

    exact
      (plane_reflection_fixed_iff_on_plane
        (Geo := Geo)
        pi P).1 hSpec

  · intro hPpi
    exact
      planeReflect_of_on_plane
        (Geo := Geo)
        pi P hPpi


/--
Characterization of plane reflection by a perpendicular midpoint.

If P is outside pi, F is the perpendicular foot of P on pi, and
F is the midpoint of P and Q, then reflection in pi sends P to Q.
-/
theorem planeReflect_eq_of_perpendicular_midpoint
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
    (P F Q : Geo.Point)
    (hPpi : Not (S.OnPlane P pi))
    (hPerp :
      PerpendicularToPlaneThrough Geo pi F P)
    (hMid :
      HilbertIsMidpoint Geo F P Q) :
    planeReflect Geo pi P = Q := by

  have hQ :
      IsPlaneReflection Geo pi P Q :=
    Or.inr
      <| ⟨hPpi,
          ⟨F, hPerp, hMid⟩⟩

  have hSpec :
      IsPlaneReflection Geo pi P
        (planeReflect Geo pi P) :=
    planeReflect_spec
      (Geo := Geo) pi P

  exact
    plane_reflection_unique
      (Geo := Geo)
      pi P
      (planeReflect Geo pi P)
      Q
      hSpec
      hQ


/--
The same perpendicular-midpoint configuration gives the reverse image.

Once reflection sends P to Q, involutivity gives reflection of Q back
to P.
-/
theorem planeReflect_swap_of_perpendicular_midpoint
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
    (P F Q : Geo.Point)
    (hPpi : Not (S.OnPlane P pi))
    (hPerp :
      PerpendicularToPlaneThrough Geo pi F P)
    (hMid :
      HilbertIsMidpoint Geo F P Q) :
    planeReflect Geo pi Q = P := by

  have hPQ :
      planeReflect Geo pi P = Q :=
    planeReflect_eq_of_perpendicular_midpoint
      (Geo := Geo)
      pi P F Q
      hPpi hPerp hMid

  have hInv :
      planeReflect Geo pi
        (planeReflect Geo pi P) = P :=
    planeReflect_involutive
      (Geo := Geo) pi P

  rw [hPQ] at hInv
  exact hInv

/--
The relational and functional descriptions of plane reflection agree.
-/
theorem isPlaneReflection_iff_eq_planeReflect
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
    (P Q : Geo.Point) :
    IsPlaneReflection Geo pi P Q <->
      Q = planeReflect Geo pi P := by

  constructor

  · intro hRef
    exact
      plane_reflection_unique
        (Geo := Geo)
        pi P
        Q
        (planeReflect Geo pi P)
        hRef
        (planeReflect_spec
          (Geo := Geo) pi P)

  · intro hEq
    subst Q
    exact
      planeReflect_spec
        (Geo := Geo) pi P


/--
A point outside the mirror plane is not fixed by plane reflection.
-/
theorem planeReflect_ne_of_off_plane
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
    (P : Geo.Point)
    (hPoff : Not (S.OnPlane P pi)) :
    Ne (planeReflect Geo pi P) P := by

  intro hEq

  have hPpi :
      S.OnPlane P pi :=
    (planeReflect_fixed_iff_on_plane
      (Geo := Geo)
      pi P).1 hEq

  exact hPoff hPpi


/--
Plane reflection preserves the complement of the mirror plane:
a point outside pi is reflected to another point outside pi.
-/
theorem planeReflect_off_plane
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
    (P : Geo.Point)
    (hPoff : Not (S.OnPlane P pi)) :
    Not (S.OnPlane (planeReflect Geo pi P) pi) := by

  intro hImageOn

  have hFixedImage :
      planeReflect Geo pi
        (planeReflect Geo pi P) =
      planeReflect Geo pi P :=
    planeReflect_of_on_plane
      (Geo := Geo)
      pi
      (planeReflect Geo pi P)
      hImageOn

  have hInv :
      planeReflect Geo pi
        (planeReflect Geo pi P) = P :=
    planeReflect_involutive
      (Geo := Geo) pi P

  have hFixedP :
      planeReflect Geo pi P = P := by
    calc
      planeReflect Geo pi P =
          planeReflect Geo pi
            (planeReflect Geo pi P) :=
        hFixedImage.symm
      _ = P := hInv

  exact
    (planeReflect_ne_of_off_plane
      (Geo := Geo)
      pi P hPoff) hFixedP


end Geometry

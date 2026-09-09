import CGJteamLab.Coxeter.E4NormalUniqueness
import CGJteamLab.Coxeter.Reflection

/-!
# Corrected E4 hyperplane reflection core

Production promotion of the validated corrected E4 reflection relation,
symmetry/uniqueness, external-normal existence, reflection existence,
canonical reflection function, specification, and involutivity.

This module imports no `AffineFlat4D_testNN` or `*_fixN` module.
Known proof-local `letI` linter warnings are removed using ordinary
`let` bindings.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection uniqueness

The corrected E4 reflection relation from test51 is now functional.

For an off-hyperplane point P, test63 identifies the two perpendicular
feet.  Once the common foot F is known, both candidate reflected points
P1 and P2 lie on the same line P-F.

We place that line in one concrete ambient 2-plane pi by choosing a
point R off the line.  The marked plane P,F,R carries the ordinary
HilbertCongruence structure reconstructed in tests56-60.

Inside PlaneGeo pi the remaining argument is exactly the standard
Hilbert uniqueness of segment construction on a prescribed ray:

  P --- F --- P1
  P --- F --- P2
  PF ~= FP1
  PF ~= FP2

hence P1 = P2.

No global HilbertCongruence Geo is introduced.
-/

/--
The relational corrected E4 reflection in a fixed hyperplane has at
most one image.
-/
theorem hyperplaneReflection4_unique_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (P P1 P2 : Geo.Point)
    (hRef1 :
      IsHyperplaneReflection4_corrected
        Geo Sigma P P1)
    (hRef2 :
      IsHyperplaneReflection4_corrected
        Geo Sigma P P2) :
    P1 = P2 := by

  rcases hRef1 with hFixed1 | hOff1

  · rcases hRef2 with hFixed2 | hOff2

    · calc
        P1 = P := hFixed1.2
        _ = P2 := Eq.symm hFixed2.2

    · exact
        False.elim
          (hOff2.1 hFixed1.1)

  · rcases hRef2 with hFixed2 | hOff2

    · exact
        False.elim
          (hOff1.1 hFixed2.1)

    · rcases hOff1 with
        ⟨hPoff, F, hPerpF, hMid1⟩

      rcases hOff2 with
        ⟨_hPoff2, G, hPerpG, hMid2⟩

      ------------------------------------------------------------------
      -- The perpendicular foot is unique.
      ------------------------------------------------------------------

      have hFG : F = G :=
        hyperplane_perpendicular_foot_unique4_corrected
          (Geo := Geo)
          Sigma
          P F G
          hPerpF hPerpG

      subst G

      ------------------------------------------------------------------
      -- Use one normal line only to obtain the line PF.
      ------------------------------------------------------------------

      rcases hPerpF with
        ⟨l, hPl, hLNormal⟩

      have hFl : H.OnLine F l :=
        hLNormal.1

      have hFSigma : Q.OnHyperplane F Sigma :=
        hLNormal.2.1

      have hPF : Ne P F := by
        intro hEq
        apply hPoff
        rw [hEq]
        exact hFSigma

      ------------------------------------------------------------------
      -- Both candidate reflected points lie on l.
      ------------------------------------------------------------------

      have hColPFP1 :
          PrimCollinear Geo P F P1 :=
        (H4O.between_incidence
          P F P1 hMid1.1).2.2.2.1

      have hP1l : H.OnLine P1 l :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hPF
          hPl hFl
          hColPFP1

      have hColPFP2 :
          PrimCollinear Geo P F P2 :=
        (H4O.between_incidence
          P F P2 hMid2.1).2.2.2.1

      have hP2l : H.OnLine P2 l :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hPF
          hPl hFl
          hColPFP2

      ------------------------------------------------------------------
      -- Choose a point R outside l and form one marked 2-plane pi.
      ------------------------------------------------------------------

      rcases
          hilbert_point_off_line
            (Geo := Geo)
            l with
        ⟨R, hRl⟩

      rcases
          hilbert4D_plane_through_line_and_external_point
            (Geo := Geo)
            l R hRl with
        ⟨pi, hlpi, hRpi⟩

      have hPpi :
          Q.toHilbertSpacePrimitive.OnPlane P pi :=
        hlpi P hPl

      have hFpi :
          Q.toHilbertSpacePrimitive.OnPlane F pi :=
        hlpi F hFl

      have hP1pi :
          Q.toHilbertSpacePrimitive.OnPlane P1 pi :=
        hlpi P1 hP1l

      have hP2pi :
          Q.toHilbertSpacePrimitive.OnPlane P2 pi :=
        hlpi P2 hP2l

      have hPFR :
          Not (PrimCollinear Geo P F R) := by

        intro hCol

        have hRl' : H.OnLine R l :=
          hilbert_on_line_of_primCollinear_with_two_on_line
            (Geo := Geo)
            hPF
            hPl hFl
            hCol

        exact hRl hRl'

      ------------------------------------------------------------------
      -- Work only inside this concrete PlaneGeo(pi).
      ------------------------------------------------------------------

      let Pp : PlanePoint Geo pi :=
        ⟨P, hPpi⟩

      let Fp : PlanePoint Geo pi :=
        ⟨F, hFpi⟩

      let P1p : PlanePoint Geo pi :=
        ⟨P1, hP1pi⟩

      let P2p : PlanePoint Geo pi :=
        ⟨P2, hP2pi⟩

      let Rp : PlanePoint Geo pi :=
        ⟨R, hRpi⟩

      let : HilbertCongruence (PlaneGeo Geo pi) :=
        planeGeoHilbertCongruence4_corrected
          (Geo := Geo)
          pi
          P F R
          hPpi hFpi hRpi
          hPFR

      have hBetween1 :
          (PlaneGeo Geo pi).Between
            Pp Fp P1p := by

        apply
          (planeGeo_between
            (Geo := Geo)
            pi Pp Fp P1p).mpr

        simpa [Pp, Fp, P1p] using hMid1.1

      have hBetween2 :
          (PlaneGeo Geo pi).Between
            Pp Fp P2p := by

        apply
          (planeGeo_between
            (Geo := Geo)
            pi Pp Fp P2p).mpr

        simpa [Pp, Fp, P2p] using hMid2.1

      have hCong1 :
          (PlaneGeo Geo pi).Congruent
            Pp Fp Fp P1p := by

        apply
          (planeGeo_congruent
            (Geo := Geo)
            pi Pp Fp Fp P1p).mpr

        simpa [Pp, Fp, P1p] using hMid1.2

      have hCong2 :
          (PlaneGeo Geo pi).Congruent
            Pp Fp Fp P2p := by

        apply
          (planeGeo_congruent
            (Geo := Geo)
            pi Pp Fp Fp P2p).mpr

        simpa [Pp, Fp, P2p] using hMid2.2

      ------------------------------------------------------------------
      -- Standard Hilbert segment-construction uniqueness in pi.
      ------------------------------------------------------------------

      have hRay1 :
          HilbertSameRay
            (PlaneGeo Geo pi)
            Pp Fp P1p :=
        hilbert_sameRay_of_between
          (PlaneGeo Geo pi)
          Pp Fp P1p
          hBetween1

      have hRay2 :
          HilbertSameRay
            (PlaneGeo Geo pi)
            Pp Fp P2p :=
        hilbert_sameRay_of_between
          (PlaneGeo Geo pi)
          Pp Fp P2p
          hBetween2

      have hFP1_PF :
          (PlaneGeo Geo pi).Congruent
            Fp P1p Pp Fp :=
        hilbert_congruent_symmetry
          (PlaneGeo Geo pi)
          Pp Fp Fp P1p
          hCong1

      have hFP1_FP2 :
          (PlaneGeo Geo pi).Congruent
            Fp P1p Fp P2p :=
        hilbert_congruent_transitivity
          (PlaneGeo Geo pi)
          Fp P1p
          Pp Fp
          Fp P2p
          hFP1_PF
          hCong2

      have hPP1_PP2 :
          (PlaneGeo Geo pi).Congruent
            Pp P1p Pp P2p :=
        HilbertCongruence.segment_additivity
          (Geo := PlaneGeo Geo pi)
          Pp Fp P1p
          Pp Fp P2p
          hBetween1
          hBetween2
          (hilbert_congruent_reflexive
            (PlaneGeo Geo pi)
            Pp Fp)
          hFP1_FP2

      have hPP2_PP1 :
          (PlaneGeo Geo pi).Congruent
            Pp P2p Pp P1p :=
        hilbert_congruent_symmetry
          (PlaneGeo Geo pi)
          Pp P1p
          Pp P2p
          hPP1_PP2

      have hPlaneEq : P1p = P2p :=
        hilbert_segment_construction_unique
          (PlaneGeo Geo pi)
          Pp P1p
          Pp Fp
          P1p P2p
          hRay1
          hRay2
          (hilbert_congruent_reflexive
            (PlaneGeo Geo pi)
            Pp P1p)
          hPP2_PP1

      exact
        congrArg Subtype.val hPlaneEq

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection: symmetry

Test64 proved that the corrected relational hyperplane reflection is
functional.

This file proves the complementary relational fact: reflection is
symmetric.  If P reflects to P' in Sigma, then P' reflects to P.

For an off-hyperplane point, the same normal line is reused.  The only
nontrivial step is reversal of the midpoint relation.  That reversal is
performed inside one concrete PlaneGeo containing the normal line, so no
global HilbertCongruence Geo or old ambient 3D hierarchy is introduced.
-/

/--
Corrected E4 hyperplane reflection is symmetric as a relation.
-/
theorem hyperplane_reflection_symmetric4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (P P' : Geo.Point)
    (hRef :
      IsHyperplaneReflection4_corrected
        Geo Sigma P P') :
    IsHyperplaneReflection4_corrected
      Geo Sigma P' P := by

  rcases hRef with hFixed | hOff

  ----------------------------------------------------------------------
  -- Fixed point on the mirror.
  ----------------------------------------------------------------------

  · rcases hFixed with
      ⟨hPSigma, hEq⟩

    subst P'

    exact
      Or.inl
        ⟨hPSigma, rfl⟩

  ----------------------------------------------------------------------
  -- Point off the mirror.
  ----------------------------------------------------------------------

  · rcases hOff with
      ⟨hPoff, F, hPerp, hMid⟩

    rcases hPerp with
      ⟨l, hPl, hNormal⟩

    have hFl :
        H.OnLine F l :=
      hNormal.1

    have hFSigma :
        Q.OnHyperplane F Sigma :=
      hNormal.2.1

    have hBetweenData :=
      H4O.between_incidence
        P F P' hMid.1

    have hPF : Ne P F :=
      hBetweenData.1

    have hFP' : Ne F P' :=
      hBetweenData.2.1

    have hPFP'col :
        PrimCollinear Geo P F P' :=
      hBetweenData.2.2.2.1

    --------------------------------------------------------------------
    -- P' lies on the same normal line.
    --------------------------------------------------------------------

    have hP'l :
        H.OnLine P' l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hPFP'col

    --------------------------------------------------------------------
    -- P' cannot lie on Sigma.
    --------------------------------------------------------------------

    have hP'off :
        Not (Q.OnHyperplane P' Sigma) := by

      intro hP'Sigma

      have hlSigma :
          HilbertLineInHyperplane4 Geo l Sigma :=
        H4I.line_in_hyperplane
          F P' hFP'
          l hFl hP'l
          Sigma hFSigma hP'Sigma

      exact
        (HilbertLinePerpendicularHyperplaneAt4_corrected.not_line_in_hyperplane
          (Geo := Geo)
          hNormal)
          hlSigma

    have hPerp' :
        PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P' :=
      ⟨l, hP'l, hNormal⟩

    --------------------------------------------------------------------
    -- Put the normal line into one concrete marked plane.
    --------------------------------------------------------------------

    rcases
        hilbert_point_off_line
          (Geo := Geo)
          l with
      ⟨R, hRl⟩

    rcases
        hilbert4D_plane_through_line_and_external_point
          (Geo := Geo)
          l R hRl with
      ⟨pi, hlpi, hRpi⟩

    have hPpi :
        Q.toHilbertSpacePrimitive.OnPlane P pi :=
      hlpi P hPl

    have hFpi :
        Q.toHilbertSpacePrimitive.OnPlane F pi :=
      hlpi F hFl

    have hP'pi :
        Q.toHilbertSpacePrimitive.OnPlane P' pi :=
      hlpi P' hP'l

    have hPFR :
        Not (PrimCollinear Geo P F R) := by

      intro hCol

      have hRl' :
          H.OnLine R l :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hPF
          hPl hFl
          hCol

      exact hRl hRl'

    let Pp : PlanePoint Geo pi :=
      ⟨P, hPpi⟩

    let Fp : PlanePoint Geo pi :=
      ⟨F, hFpi⟩

    let P'p : PlanePoint Geo pi :=
      ⟨P', hP'pi⟩

    let Rp : PlanePoint Geo pi :=
      ⟨R, hRpi⟩

    let : HilbertCongruence (PlaneGeo Geo pi) :=
      planeGeoHilbertCongruence4_corrected
        (Geo := Geo)
        pi
        P F R
        hPpi hFpi hRpi
        hPFR

    --------------------------------------------------------------------
    -- Reverse the midpoint relation inside PlaneGeo(pi).
    --------------------------------------------------------------------

    have hBetweenPlane :
        (PlaneGeo Geo pi).Between
          Pp Fp P'p := by

      apply
        (planeGeo_between
          (Geo := Geo)
          pi Pp Fp P'p).mpr

      simpa [Pp, Fp, P'p] using hMid.1

    have hCongPlane :
        (PlaneGeo Geo pi).Congruent
          Pp Fp Fp P'p := by

      apply
        (planeGeo_congruent
          (Geo := Geo)
          pi Pp Fp Fp P'p).mpr

      simpa [Pp, Fp, P'p] using hMid.2

    have hMidPlane :
        HilbertIsMidpoint
          (PlaneGeo Geo pi)
          Fp Pp P'p :=
      ⟨hBetweenPlane, hCongPlane⟩

    have hMidPlaneRev :
        HilbertIsMidpoint
          (PlaneGeo Geo pi)
          Fp P'p Pp :=
      MidpointSymmetry
        (PlaneGeo Geo pi)
        Fp Pp P'p
        hMidPlane

    have hBetweenRev :
        Geo.Between P' F P := by

      apply
        (planeGeo_between
          (Geo := Geo)
          pi P'p Fp Pp).mp

      exact hMidPlaneRev.1

    have hCongRev :
        Geo.Congruent
          P' F F P := by

      apply
        (planeGeo_congruent
          (Geo := Geo)
          pi P'p Fp Fp Pp).mp

      exact hMidPlaneRev.2

    have hMidRev :
        HilbertIsMidpoint Geo F P' P :=
      ⟨hBetweenRev, hCongRev⟩

    exact
      Or.inr
        ⟨hP'off,
         ⟨F, hPerp', hMidRev⟩⟩

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection as an involution

Tests62-65 proved, without any new normal-existence axiom:

* uniqueness of the normal line at a fixed foot;
* uniqueness of the perpendicular foot from a fixed point;
* uniqueness of the reflected point;
* symmetry of the reflection relation.

The only remaining construction gap is existence of a normal from an
external point to a hyperplane.  We isolate exactly that XI.11-type
existence statement below.

Under this one temporary existence class, reflection exists for every
point, hence can be packaged as a genuine function.  Functionality and
symmetry then imply involutivity.
-/

/--
Corrected E4 analogue of Euclid XI.11:

from a point outside a hyperplane, a perpendicular to the hyperplane
exists.

This class is intentionally only an existence boundary.  It contains no
uniqueness statement; uniqueness has already been derived in test63.
-/
class Hilbert4DNormalFromExternalPointExistence_corrected
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo] : Prop where

  normal_from_external_point :
    forall Sigma : Q.Hyperplane,
      forall P : Geo.Point,
        Not (Q.OnHyperplane P Sigma) ->
        exists F : Geo.Point,
          PerpendicularToHyperplaneThrough4_corrected
            Geo Sigma F P

/--
Under the corrected XI.11-type existence clause, every external point
has a perpendicular foot.
-/
theorem hyperplane_perpendicular_foot_exists4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (hPSigma : Not (Q.OnHyperplane P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P := by

  exact
    Hilbert4DNormalFromExternalPointExistence_corrected.normal_from_external_point
        (Geo := Geo)
        Sigma P hPSigma

/--
Under corrected XI.11 existence, the perpendicular foot exists uniquely.
-/
theorem hyperplane_perpendicular_foot_exists_unique4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (hPSigma : Not (Q.OnHyperplane P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P /\
      forall G : Geo.Point,
        PerpendicularToHyperplaneThrough4_corrected
            Geo Sigma G P ->
        G = F := by

  rcases
      Hilbert4DNormalFromExternalPointExistence_corrected.normal_from_external_point
          (Geo := Geo)
          Sigma P hPSigma with
    ⟨F, hF⟩

  refine
    ⟨F, hF, ?_⟩

  intro G hG

  exact
    hyperplane_perpendicular_foot_unique4_corrected
      (Geo := Geo)
      Sigma
      P G F
      hG hF

/--
Given an external point and its corrected hyperplane normal, construct
the point on the opposite side of the foot so that the foot is the
midpoint.

The midpoint construction itself is purely planar: one puts the normal
line into a concrete ambient 2-plane and uses the local PlaneGeo
HilbertCongruence reconstructed in tests56-60.
-/
theorem hyperplane_reflection_midpoint_exists_off4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (hPSigma : Not (Q.OnHyperplane P Sigma)) :
    exists F P' : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P /\
      HilbertIsMidpoint Geo F P P' := by

  rcases
      Hilbert4DNormalFromExternalPointExistence_corrected.normal_from_external_point
          (Geo := Geo)
          Sigma P hPSigma with
    ⟨F, hPerp⟩

  rcases hPerp with
    ⟨l, hPl, hLNormal⟩

  have hFl :
      H.OnLine F l :=
    hLNormal.1

  have hFSigma :
      Q.OnHyperplane F Sigma :=
    hLNormal.2.1

  have hPF : Ne P F := by
    intro hEq
    apply hPSigma
    rw [hEq]
    exact hFSigma

  ----------------------------------------------------------------------
  -- Put the normal line in one concrete marked 2-plane.
  ----------------------------------------------------------------------

  rcases
      hilbert_point_off_line
        (Geo := Geo)
        l with
    ⟨R, hRl⟩

  rcases
      hilbert4D_plane_through_line_and_external_point
        (Geo := Geo)
        l R hRl with
    ⟨pi, hlpi, hRpi⟩

  have hPpi :
      Q.toHilbertSpacePrimitive.OnPlane P pi :=
    hlpi P hPl

  have hFpi :
      Q.toHilbertSpacePrimitive.OnPlane F pi :=
    hlpi F hFl

  have hPFR :
      Not (PrimCollinear Geo P F R) := by

    intro hCol

    have hRl' :
        H.OnLine R l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hCol

    exact hRl hRl'

  let Pp : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let Fp : PlanePoint Geo pi :=
    ⟨F, hFpi⟩

  let Rp : PlanePoint Geo pi :=
    ⟨R, hRpi⟩

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi
      P F R
      hPpi hFpi hRpi
      hPFR

  have hPFp : Ne Pp Fp := by
    intro hEq
    apply hPF
    exact congrArg Subtype.val hEq

  ----------------------------------------------------------------------
  -- Extend PF beyond F by a congruent segment.
  ----------------------------------------------------------------------

  rcases
      hilbert_extend_segment_beyond
        (PlaneGeo Geo pi)
        Pp Fp hPFp with
    ⟨Pp', hPFP', hPF_FP'⟩

  let P' : Geo.Point :=
    Pp'.1

  have hBetween :
      Geo.Between P F P' := by

    exact
      (planeGeo_between
        (Geo := Geo)
        pi Pp Fp Pp').mp
        hPFP'

  have hCong :
      Geo.Congruent P F F P' := by

    exact
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Fp Fp Pp').mp
        hPF_FP'

  have hMid :
      HilbertIsMidpoint Geo F P P' :=
    ⟨hBetween, hCong⟩

  have hPerpThrough :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P :=
    ⟨l, hPl, hLNormal⟩

  exact
    ⟨F, P', hPerpThrough, hMid⟩

/--
The corrected XI.11-type existence clause suffices to construct a
reflection of every ambient point.

Points on Sigma are fixed.  Points outside Sigma use the preceding
normal-plus-midpoint construction.
-/
theorem hyperplane_reflection_exists4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    exists P' : Geo.Point,
      IsHyperplaneReflection4_corrected
        Geo Sigma P P' := by

  by_cases hPSigma :
      Q.OnHyperplane P Sigma

  · exact
      ⟨P,
       Or.inl
         ⟨hPSigma, rfl⟩⟩

  · rcases
        hyperplane_reflection_midpoint_exists_off4_corrected
          (Geo := Geo)
          Sigma P hPSigma with
      ⟨F, P', hPerp, hMid⟩

    exact
      ⟨P',
       Or.inr
         ⟨hPSigma,
          ⟨F, hPerp, hMid⟩⟩⟩

/--
The reflected point in a corrected E4 hyperplane.
-/
noncomputable def hyperplaneReflect4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    Geo.Point :=
  Classical.choose
    (hyperplane_reflection_exists4_corrected
      (Geo := Geo)
      Sigma P)

/--
Specification theorem for `hyperplaneReflect4_corrected`.
-/
theorem hyperplaneReflect4_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    IsHyperplaneReflection4_corrected
      Geo Sigma P
      (hyperplaneReflect4_corrected Geo Sigma P) :=
  Classical.choose_spec
    (hyperplane_reflection_exists4_corrected
      (Geo := Geo)
      Sigma P)

/--
Corrected E4 hyperplane reflection is an involution.
-/
theorem hyperplaneReflect4_corrected_involutive
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    hyperplaneReflect4_corrected Geo Sigma
      (hyperplaneReflect4_corrected Geo Sigma P) = P := by

  have hForward :
      IsHyperplaneReflection4_corrected
        Geo Sigma P
        (hyperplaneReflect4_corrected Geo Sigma P) :=
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma P

  have hBackward :
      IsHyperplaneReflection4_corrected
        Geo Sigma
        (hyperplaneReflect4_corrected Geo Sigma P)
        P :=
    hyperplane_reflection_symmetric4_corrected
      (Geo := Geo)
      Sigma
      P
      (hyperplaneReflect4_corrected Geo Sigma P)
      hForward

  have hSecond :
      IsHyperplaneReflection4_corrected
        Geo Sigma
        (hyperplaneReflect4_corrected Geo Sigma P)
        (hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma P)) :=
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma
      (hyperplaneReflect4_corrected Geo Sigma P)

  have hUnique :
      P =
        hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma P) :=
    hyperplaneReflection4_unique_corrected
      (Geo := Geo)
      Sigma
      (hyperplaneReflect4_corrected Geo Sigma P)
      P
      (hyperplaneReflect4_corrected Geo Sigma
        (hyperplaneReflect4_corrected Geo Sigma P))
      hBackward
      hSecond

  exact hUnique.symm

end Geometry

import CGJteamLab.Coxeter.E4Order

/-!
# Corrected E4 congruence layer

Production promotion of the validated corrected E4 Group III chain:
segment congruence, ray/angle transport, same-side transport, and the
local `HilbertSpaceCongruence` reconstruction inside each hyperplane.

No workshop module is imported by this file.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hierarchy repair: ambient congruence, segment part

Test45 reconstructed local `HilbertSpaceOrder` inside every E4
hyperplane without assuming ambient `HilbertSpaceOrder Geo`.

Now we repair Group III.

The old `HilbertSpaceCongruence Geo` has mathematically suitable fields,
but its typeclass signature depends on the old ambient
`HilbertSpaceIncidence Geo` and `HilbertSpaceOrder Geo`.

This file introduces the corrected ambient E4 congruence class and
tests the segment half of the transfer:

* same-ray bridge;
* III.1 segment construction;
* III.2 common congruence;
* III.3 segment additivity.

The angle clauses are already included in the new ambient class, but
their local transfer is postponed to the next test.
-/

/--
Group III for genuine ambient E4.

The mathematical fields are the same as in `HilbertSpaceCongruence`,
but the dependencies are the corrected E4 incidence/order layers.
-/
class Hilbert4DAmbientCongruence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo] : Prop where

  segment_construction :
    forall A B O R : Geo.Point,
      Ne O R ->
      exists X : Geo.Point,
        HilbertSameRay Geo O R X /\
        Geo.Congruent O X A B

  segment_congruence_common :
    forall A B A' B' A'' B'' : Geo.Point,
      Geo.Congruent A B A' B' ->
      Geo.Congruent A B A'' B'' ->
      Geo.Congruent A' B' A'' B''

  segment_additivity :
    forall A B C A' B' C' : Geo.Point,
      Geo.Between A B C ->
      Geo.Between A' B' C' ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent B C B' C' ->
      Geo.Congruent A C A' C'

  angle_construction_in_plane :
    forall A B C A' B' T : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Ne A' B' ->
      forall pi : Q.toHilbertSpacePrimitive.Plane,
        forall l : Geo.Line,
          HilbertLineInPlane Geo l pi ->
          H.OnLine A' l ->
          H.OnLine B' l ->
          Q.toHilbertSpacePrimitive.OnPlane T pi ->
          Not (H.OnLine T l) ->
          exists C' : Geo.Point,
            HilbertSameSideInPlane Geo C' T l pi /\
            Geo.AngleCongruent A B C A' B' C' /\
            forall D' : Geo.Point,
              HilbertSameSideInPlane Geo D' T l pi ->
              Geo.AngleCongruent A B C A' B' D' ->
              HilbertSameRay Geo B' C' D'

  angle_congruence_reflexive :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Geo.AngleCongruent A B C A B C

  sas :
    forall A B C A' B' C' : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Not (PrimCollinear Geo A' B' C') ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent A C A' C' ->
      Geo.AngleCongruent B A C B' A' C' ->
      Geo.AngleCongruent A B C A' B' C'

/--
The same-ray predicate in a corrected hyperplane slice is exactly the
ambient same-ray predicate on underlying points.
-/
theorem hyperplaneGeo4_sameRay_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (O P R : HyperplanePoint4 Geo Sigma) :
    HilbertSameRay
        (HyperplaneGeo4 Geo Sigma) O P R <->
      HilbertSameRay Geo O.1 P.1 R.1 := by

  unfold HilbertSameRay

  constructor

  · rintro ⟨hPO, hRO, hCol, hNotBetween⟩

    have hPOval : Ne P.1 O.1 := by
      intro h
      apply hPO
      exact Subtype.ext h

    have hROval : Ne R.1 O.1 := by
      intro h
      apply hRO
      exact Subtype.ext h

    have hColAmbient :
        PrimCollinear Geo O.1 P.1 R.1 :=
      hyperplaneGeo4_primCollinear_to_ambient
        (Geo := Geo)
        Sigma O P R hCol

    exact
      ⟨hPOval,
       hROval,
       hColAmbient,
       hNotBetween⟩

  · rintro ⟨hPO, hRO, hCol, hNotBetween⟩

    have hPOslice : Ne P O := by
      intro h
      exact hPO (congrArg Subtype.val h)

    have hROslice : Ne R O := by
      intro h
      exact hRO (congrArg Subtype.val h)

    have hOP : Ne O.1 P.1 :=
      hPO.symm

    have hColSlice :
        PrimCollinear
          (HyperplaneGeo4 Geo Sigma)
          O P R :=
      hyperplaneGeo4_primCollinear_of_ambient_of_ne_corrected
        (Geo := Geo)
        Sigma O P R
        hOP hCol

    exact
      ⟨hPOslice,
       hROslice,
       hColSlice,
       hNotBetween⟩

/--
A point on an ambient same ray from two points of Sigma also lies in
Sigma.  This uses only corrected E4 incidence.
-/
theorem hilbert4D_sameRay_preserves_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane)
    (O R X : Geo.Point)
    (hOSigma : Q.OnHyperplane O Sigma)
    (hRSigma : Q.OnHyperplane R Sigma)
    (hRay : HilbertSameRay Geo O R X) :
    Q.OnHyperplane X Sigma := by

  have hOR : Ne O R :=
    hRay.1.symm

  rcases hRay.2.2.1 with
    ⟨l, hOl, hRl, hXl⟩

  have hlSigma :
      HilbertLineInHyperplane4 Geo l Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      O R hOR
      l hOl hRl
      Sigma hOSigma hRSigma

  exact
    hlSigma X hXl

/--
Corrected III.1 restricted to one hyperplane.
-/
theorem hyperplaneGeo4_segment_construction_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (A B O R : HyperplanePoint4 Geo Sigma)
    (hOR : Ne O R) :
    exists X : HyperplanePoint4 Geo Sigma,
      HilbertSameRay
        (HyperplaneGeo4 Geo Sigma) O R X /\
      (HyperplaneGeo4 Geo Sigma).Congruent O X A B := by

  have hORval : Ne O.1 R.1 := by
    intro h
    apply hOR
    exact Subtype.ext h

  rcases
      Hilbert4DAmbientCongruence.segment_construction
        (Geo := Geo)
        A.1 B.1 O.1 R.1
        hORval with
    ⟨X, hRayAmbient, hCongAmbient⟩

  have hXSigma :
      Q.OnHyperplane X Sigma :=
    hilbert4D_sameRay_preserves_hyperplane_corrected
      (Geo := Geo)
      Sigma
      O.1 R.1 X
      O.2 R.2
      hRayAmbient

  let Xp : HyperplanePoint4 Geo Sigma :=
    ⟨X, hXSigma⟩

  have hRaySlice :
      HilbertSameRay
        (HyperplaneGeo4 Geo Sigma)
        O R Xp := by

    apply
      (hyperplaneGeo4_sameRay_iff_ambient_corrected
        (Geo := Geo)
        Sigma O R Xp).mpr

    simpa [Xp] using hRayAmbient

  have hCongSlice :
      (HyperplaneGeo4 Geo Sigma).Congruent
        O Xp A B := by

    apply
      (hyperplaneGeo4_congruent
        (Geo := Geo)
        Sigma O Xp A B).mpr

    simpa [Xp] using hCongAmbient

  exact
    ⟨Xp, hRaySlice, hCongSlice⟩

/--
Corrected III.2 restricted to one hyperplane.
-/
theorem hyperplaneGeo4_segment_congruence_common_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (A B A' B' A'' B'' : HyperplanePoint4 Geo Sigma)
    (h1 :
      (HyperplaneGeo4 Geo Sigma).Congruent
        A B A' B')
    (h2 :
      (HyperplaneGeo4 Geo Sigma).Congruent
        A B A'' B'') :
    (HyperplaneGeo4 Geo Sigma).Congruent
      A' B' A'' B'' := by

  have h1Ambient :
      Geo.Congruent
        A.1 B.1 A'.1 B'.1 :=
    (hyperplaneGeo4_congruent
      (Geo := Geo)
      Sigma A B A' B').mp h1

  have h2Ambient :
      Geo.Congruent
        A.1 B.1 A''.1 B''.1 :=
    (hyperplaneGeo4_congruent
      (Geo := Geo)
      Sigma A B A'' B'').mp h2

  have hResult :
      Geo.Congruent
        A'.1 B'.1 A''.1 B''.1 :=
    Hilbert4DAmbientCongruence.segment_congruence_common
      (Geo := Geo)
      A.1 B.1
      A'.1 B'.1
      A''.1 B''.1
      h1Ambient h2Ambient

  exact
    (hyperplaneGeo4_congruent
      (Geo := Geo)
      Sigma A' B' A'' B'').mpr
      hResult

/--
Corrected III.3 restricted to one hyperplane.
-/
theorem hyperplaneGeo4_segment_additivity_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane)
    (A B C A' B' C' : HyperplanePoint4 Geo Sigma)
    (hABC :
      (HyperplaneGeo4 Geo Sigma).Between A B C)
    (hA'B'C' :
      (HyperplaneGeo4 Geo Sigma).Between A' B' C')
    (hAB :
      (HyperplaneGeo4 Geo Sigma).Congruent
        A B A' B')
    (hBC :
      (HyperplaneGeo4 Geo Sigma).Congruent
        B C B' C') :
    (HyperplaneGeo4 Geo Sigma).Congruent
      A C A' C' := by

  have hABAmbient :
      Geo.Congruent A.1 B.1 A'.1 B'.1 :=
    (hyperplaneGeo4_congruent
      (Geo := Geo)
      Sigma A B A' B').mp hAB

  have hBCAmbient :
      Geo.Congruent B.1 C.1 B'.1 C'.1 :=
    (hyperplaneGeo4_congruent
      (Geo := Geo)
      Sigma B C B' C').mp hBC

  have hResult :
      Geo.Congruent A.1 C.1 A'.1 C'.1 :=
    Hilbert4DAmbientCongruence.segment_additivity
      (Geo := Geo)
      A.1 B.1 C.1
      A'.1 B'.1 C'.1
      hABC hA'B'C'
      hABAmbient hBCAmbient

  exact
    (hyperplaneGeo4_congruent
      (Geo := Geo)
      Sigma A C A' C').mpr
      hResult

/--
Sanity bundle for the segment half of Group III.
-/
theorem hyperplaneGeo4_groupIII_segments_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane) :
    (forall A B O R : HyperplanePoint4 Geo Sigma,
      Ne O R ->
      exists X : HyperplanePoint4 Geo Sigma,
        HilbertSameRay
          (HyperplaneGeo4 Geo Sigma) O R X /\
        (HyperplaneGeo4 Geo Sigma).Congruent O X A B) /\
    (forall A B A' B' A'' B'' :
        HyperplanePoint4 Geo Sigma,
      (HyperplaneGeo4 Geo Sigma).Congruent A B A' B' ->
      (HyperplaneGeo4 Geo Sigma).Congruent A B A'' B'' ->
      (HyperplaneGeo4 Geo Sigma).Congruent A' B' A'' B'') := by

  constructor

  · intro A B O R hOR
    exact
      hyperplaneGeo4_segment_construction_corrected
        (Geo := Geo)
        Sigma A B O R hOR

  · intro A B A' B' A'' B'' h1 h2
    exact
      hyperplaneGeo4_segment_congruence_common_corrected
        (Geo := Geo)
        Sigma A B A' B' A'' B''
        h1 h2

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hierarchy repair: ray and angle bridges

Test47 closed the segment part of Group III under the corrected E4
hierarchy.

This file rebuilds the ray and angle-congruence bridge without assuming
ambient `HilbertSpaceIncidence Geo`, `HilbertSpaceOrder Geo`, or
`HilbertSpaceCongruence Geo`.

The goal is to show that the angle language of one fixed hyperplane is
still exactly the ambient angle language on underlying points.
-/

/--
The elementary same-direction relation in one induced E4 hyperplane is
exactly the ambient relation on underlying points.
-/
theorem hyperplaneGeo4_sameDirectionStep_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (O P R : HyperplanePoint4 Geo Sigma) :
    (HyperplaneGeo4 Geo Sigma).SameDirectionStep O P R <->
      Geo.SameDirectionStep O.1 P.1 R.1 := by

  unfold Geometry.Geo.SameDirectionStep

  constructor

  · rintro ⟨hPO, hRO, hCases⟩

    have hPOval : Ne P.1 O.1 := by
      intro h
      apply hPO
      exact Subtype.ext h

    have hROval : Ne R.1 O.1 := by
      intro h
      apply hRO
      exact Subtype.ext h

    rcases hCases with hPR | hOPR | hORP

    · exact
        ⟨hPOval,
         hROval,
         Or.inl (congrArg Subtype.val hPR)⟩

    · exact
        ⟨hPOval,
         hROval,
         Or.inr (Or.inl hOPR)⟩

    · exact
        ⟨hPOval,
         hROval,
         Or.inr (Or.inr hORP)⟩

  · rintro ⟨hPO, hRO, hCases⟩

    have hPOslice : Ne P O := by
      intro h
      exact hPO (congrArg Subtype.val h)

    have hROslice : Ne R O := by
      intro h
      exact hRO (congrArg Subtype.val h)

    rcases hCases with hPR | hOPR | hORP

    · exact
        ⟨hPOslice,
         hROslice,
         Or.inl (Subtype.ext hPR)⟩

    · exact
        ⟨hPOslice,
         hROslice,
         Or.inr (Or.inl hOPR)⟩

    · exact
        ⟨hPOslice,
         hROslice,
         Or.inr (Or.inr hORP)⟩

/--
One ambient same-direction step whose origin and starting point lie in
`Sigma` stays in `Sigma`.
-/
theorem hilbert4D_sameDirectionStep_preserves_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O P R : Geo.Point)
    (hOSigma : Q.OnHyperplane O Sigma)
    (hPSigma : Q.OnHyperplane P Sigma)
    (hStep : Geo.SameDirectionStep O P R) :
    Q.OnHyperplane R Sigma := by

  unfold Geometry.Geo.SameDirectionStep at hStep

  rcases hStep with
    ⟨hPO, _hRO, hCases⟩

  have hOP : Ne O P :=
    hPO.symm

  rcases hCases with hPR | hOPR | hORP

  · rw [← hPR]
    exact hPSigma

  · have hCol :
        PrimCollinear Geo O P R :=
      (Hilbert4DAmbientOrder.between_incidence
        (Geo := Geo)
        O P R hOPR).2.2.2.1

    rcases hCol with
      ⟨l, hOl, hPl, hRl⟩

    have hlSigma :
        HilbertLineInHyperplane4 Geo l Sigma :=
      Hilbert4DAmbientIncidence.line_in_hyperplane
        (Geo := Geo)
        O P hOP
        l hOl hPl
        Sigma hOSigma hPSigma

    exact hlSigma R hRl

  · have hColORP :
        PrimCollinear Geo O R P :=
      (Hilbert4DAmbientOrder.between_incidence
        (Geo := Geo)
        O R P hORP).2.2.2.1

    have hColOPR :
        PrimCollinear Geo O P R :=
      PrimCollinearRotate
        Geo O R P hColORP

    rcases hColOPR with
      ⟨l, hOl, hPl, hRl⟩

    have hlSigma :
        HilbertLineInHyperplane4 Geo l Sigma :=
      Hilbert4DAmbientIncidence.line_in_hyperplane
        (Geo := Geo)
        O P hOP
        l hOl hPl
        Sigma hOSigma hPSigma

    exact hlSigma R hRl

/--
Every endpoint of an ambient same-direction chain beginning in `Sigma`
remains in `Sigma`.
-/
theorem hilbert4D_reflTransGen_sameDirection_preserves_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O A X : Geo.Point)
    (hOSigma : Q.OnHyperplane O Sigma)
    (hASigma : Q.OnHyperplane A Sigma)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O)
        A X) :
    Q.OnHyperplane X Sigma := by

  induction hChain with

  | refl =>
      exact hASigma

  | tail hAB hBX ih =>
      exact
        hilbert4D_sameDirectionStep_preserves_hyperplane_corrected
          (Geo := Geo)
          Sigma
          O _ _
          hOSigma
          ih
          hBX

/--
A same-direction chain inside `HyperplaneGeo4` gives the corresponding
ambient chain.
-/
theorem hyperplaneGeo4_reflTransGen_sameDirection_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (O A X : HyperplanePoint4 Geo Sigma)
    (hChain :
      Relation.ReflTransGen
        ((HyperplaneGeo4 Geo Sigma).SameDirectionStep O)
        A X) :
    Relation.ReflTransGen
      (Geo.SameDirectionStep O.1)
      A.1 X.1 := by

  induction hChain with

  | refl =>
      exact Relation.ReflTransGen.refl

  | tail hAB hBX ih =>
      exact
        Relation.ReflTransGen.tail
          ih
          ((hyperplaneGeo4_sameDirectionStep_iff_ambient_corrected
              (Geo := Geo)
              Sigma O _ _).mp hBX)

/--
An ambient same-direction chain beginning at a hyperplane point can be
lifted to a chain in `HyperplaneGeo4`.
-/
theorem hyperplaneGeo4_exists_reflTransGen_sameDirection_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O A : HyperplanePoint4 Geo Sigma)
    (X : Geo.Point)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X) :
    exists Xp : HyperplanePoint4 Geo Sigma,
      Xp.1 = X /\
      Relation.ReflTransGen
        ((HyperplaneGeo4 Geo Sigma).SameDirectionStep O)
        A Xp := by

  induction hChain with

  | refl =>
      exact
        ⟨A,
         rfl,
         Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>

      rcases ih with
        ⟨Bp, hBp, hSliceAB⟩

      have hBSigma :
          Q.OnHyperplane B Sigma := by
        simpa [hBp] using Bp.2

      have hCSigma :
          Q.OnHyperplane C Sigma :=
        hilbert4D_sameDirectionStep_preserves_hyperplane_corrected
          (Geo := Geo)
          Sigma
          O.1 B C
          O.2
          hBSigma
          hBC

      let Cp : HyperplanePoint4 Geo Sigma :=
        ⟨C, hCSigma⟩

      have hSliceBC :
          (HyperplaneGeo4 Geo Sigma).SameDirectionStep O Bp Cp := by

        apply
          (hyperplaneGeo4_sameDirectionStep_iff_ambient_corrected
            (Geo := Geo)
            Sigma O Bp Cp).mpr

        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hSliceAB
           hSliceBC⟩

/--
The existential chain lift specializes to an already given hyperplane
endpoint.
-/
theorem hyperplaneGeo4_reflTransGen_sameDirection_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O A X : HyperplanePoint4 Geo Sigma)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1) :
    Relation.ReflTransGen
      ((HyperplaneGeo4 Geo Sigma).SameDirectionStep O)
      A X := by

  rcases
      hyperplaneGeo4_exists_reflTransGen_sameDirection_of_ambient_corrected
        (Geo := Geo)
        Sigma O A X.1 hChain with
    ⟨Xp, hXpVal, hSliceChain⟩

  have hXpX : Xp = X := by
    apply Subtype.ext
    exact hXpVal

  simpa [hXpX] using hSliceChain

/--
Ray membership in `HyperplaneGeo4` is exactly ambient ray membership.
-/
theorem hyperplaneGeo4_mem_ray_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O A X : HyperplanePoint4 Geo Sigma) :
    X ∈ (HyperplaneGeo4 Geo Sigma).ray O A <->
      X.1 ∈ Geo.ray O.1 A.1 := by

  change
    (X = O \/
      Relation.ReflTransGen
        ((HyperplaneGeo4 Geo Sigma).SameDirectionStep O)
        A X) <->
    (X.1 = O.1 \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1)

  constructor

  · rintro (hXO | hAX)

    · exact Or.inl
        (congrArg Subtype.val hXO)

    · exact Or.inr
        (hyperplaneGeo4_reflTransGen_sameDirection_to_ambient_corrected
          (Geo := Geo)
          Sigma O A X hAX)

  · rintro (hXO | hAX)

    · exact Or.inl
        (Subtype.ext hXO)

    · exact Or.inr
        (hyperplaneGeo4_reflTransGen_sameDirection_of_ambient_corrected
          (Geo := Geo)
          Sigma O A X hAX)

/--
Every ambient point of a ray determined by two hyperplane points still
lies in the same hyperplane.
-/
theorem hilbert4D_onHyperplane_of_mem_ray_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O A : HyperplanePoint4 Geo Sigma)
    (X : Geo.Point)
    (hX : X ∈ Geo.ray O.1 A.1) :
    Q.OnHyperplane X Sigma := by

  change
    X = O.1 \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X at hX

  rcases hX with hXO | hAX

  · rw [hXO]
    exact O.2

  · exact
      hilbert4D_reflTransGen_sameDirection_preserves_hyperplane_corrected
        (Geo := Geo)
        Sigma
        O.1 A.1 X
        O.2 A.2
        hAX

/--
Forgetting hyperplane-membership proofs sends a ray of
`HyperplaneGeo4` exactly to the corresponding ambient ray.
-/
theorem hyperplaneGeo4_ray_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (O A : HyperplanePoint4 Geo Sigma) :
    hyperplanePointSetToAmbient4
        (Geo := Geo)
        (Sigma := Sigma)
        ((HyperplaneGeo4 Geo Sigma).ray O A) =
      Geo.ray O.1 A.1 := by

  apply Set.ext
  intro X

  constructor

  · rintro ⟨Xp, hXpRay, rfl⟩

    exact
      (hyperplaneGeo4_mem_ray_iff_ambient_corrected
        (Geo := Geo)
        Sigma O A Xp).mp hXpRay

  · intro hXRay

    have hXSigma :
        Q.OnHyperplane X Sigma :=
      hilbert4D_onHyperplane_of_mem_ray_corrected
        (Geo := Geo)
        Sigma O A X hXRay

    let Xp : HyperplanePoint4 Geo Sigma :=
      ⟨X, hXSigma⟩

    have hXpRay :
        Xp ∈ (HyperplaneGeo4 Geo Sigma).ray O A := by

      apply
        (hyperplaneGeo4_mem_ray_iff_ambient_corrected
          (Geo := Geo)
          Sigma O A Xp).mpr

      simpa [Xp] using hXRay

    exact
      ⟨Xp, hXpRay, rfl⟩

/--
The induced hyperplane angle maps exactly to the ambient angle.
-/
theorem hyperplaneGeo4_angle_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma) :
    ( ((HyperplaneGeo4 Geo Sigma).Angle A B C).1.1,
      mapUnorderedPair
        (hyperplanePointSetToAmbient4
          (Geo := Geo) (Sigma := Sigma))
        ((HyperplaneGeo4 Geo Sigma).Angle A B C).2 ) =
      Geo.Angle A.1 B.1 C.1 := by

  change
    ( B.1,
      mapUnorderedPair
        (hyperplanePointSetToAmbient4
          (Geo := Geo) (Q := Q) (Sigma := Sigma))
        (UnorderedPair.mk
          ((HyperplaneGeo4
            (Geo := Geo) (H := H) (Q := Q) Sigma).ray B A)
          ((HyperplaneGeo4
            (Geo := Geo) (H := H) (Q := Q) Sigma).ray B C)) ) =
    ( B.1,
      UnorderedPair.mk
        (Geo.ray B.1 A.1)
        (Geo.ray B.1 C.1) )

  have hMap :
      mapUnorderedPair
          (hyperplanePointSetToAmbient4
            (Geo := Geo) (Q := Q) (Sigma := Sigma))
          (UnorderedPair.mk
            ((HyperplaneGeo4
              (Geo := Geo) (H := H) (Q := Q) Sigma).ray B A)
            ((HyperplaneGeo4
              (Geo := Geo) (H := H) (Q := Q) Sigma).ray B C)) =
        UnorderedPair.mk
          (hyperplanePointSetToAmbient4
            (Geo := Geo) (Q := Q) (Sigma := Sigma)
            ((HyperplaneGeo4
              (Geo := Geo) (H := H) (Q := Q) Sigma).ray B A))
          (hyperplanePointSetToAmbient4
            (Geo := Geo) (Q := Q) (Sigma := Sigma)
            ((HyperplaneGeo4
              (Geo := Geo) (H := H) (Q := Q) Sigma).ray B C)) := by
    exact
      mapUnorderedPair_mk
        (hyperplanePointSetToAmbient4
          (Geo := Geo) (Q := Q) (Sigma := Sigma))
        ((HyperplaneGeo4
          (Geo := Geo) (H := H) (Q := Q) Sigma).ray B A)
        ((HyperplaneGeo4
          (Geo := Geo) (H := H) (Q := Q) Sigma).ray B C)

  rw [hMap]

  rw [
    hyperplaneGeo4_ray_to_ambient_corrected
      (Geo := Geo) Sigma B A,
    hyperplaneGeo4_ray_to_ambient_corrected
      (Geo := Geo) Sigma B C
  ]

/--
Forget the hyperplane subtype from arbitrary angle data.
-/
def hyperplaneGeo4AngleToAmbient_corrected
    [Q : Hilbert4DPrimitive Geo]
    {Sigma : Q.Hyperplane}
    (a :
      HyperplanePoint4 Geo Sigma ×
        UnorderedPair (Set (HyperplanePoint4 Geo Sigma))) :
    Geo.Point × UnorderedPair (Set Geo.Point) :=
  ( a.1.1,
    mapUnorderedPair
      (hyperplanePointSetToAmbient4
        (Geo := Geo) (Sigma := Sigma))
      a.2 )

/--
The primitive angle relation of `HyperplaneGeo4` is ambient closed angle
congruence on forgotten angle data.
-/
theorem hyperplaneGeo4_unorientedAngleCongruent_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (a b :
      HyperplanePoint4 Geo Sigma ×
        UnorderedPair (Set (HyperplanePoint4 Geo Sigma))) :
    (HyperplaneGeo4 Geo Sigma).UnorientedAngleCongruent a b <->
      Relation.EqvGen
        Geo.UnorientedAngleCongruent
        (hyperplaneGeo4AngleToAmbient_corrected
          (Geo := Geo) a)
        (hyperplaneGeo4AngleToAmbient_corrected
          (Geo := Geo) b) := by
  rfl

/--
The generic forgetting map sends an actual hyperplane angle to the
corresponding ambient angle.
-/
theorem hyperplaneGeo4AngleToAmbient_corrected_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma) :
    hyperplaneGeo4AngleToAmbient_corrected
        (Geo := Geo)
        ((HyperplaneGeo4 Geo Sigma).Angle A B C) =
      Geo.Angle A.1 B.1 C.1 := by

  exact
    hyperplaneGeo4_angle_to_ambient_corrected
      (Geo := Geo)
      Sigma A B C

/--
Angle congruence inside `HyperplaneGeo4` implies ambient angle
congruence.
-/
theorem hyperplaneGeo4_angleCongruent_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (A B C D E F : HyperplanePoint4 Geo Sigma)
    (h :
      (HyperplaneGeo4 Geo Sigma).AngleCongruent
        A B C D E F) :
    Geo.AngleCongruent
      A.1 B.1 C.1 D.1 E.1 F.1 := by

  unfold Geometry.Geo.AngleCongruent at h ⊢

  have hMap :
      forall
        {x y :
          HyperplanePoint4 Geo Sigma ×
            UnorderedPair (Set (HyperplanePoint4 Geo Sigma))},
        Relation.EqvGen
          (HyperplaneGeo4 Geo Sigma).UnorientedAngleCongruent
          x y ->
        Relation.EqvGen
          Geo.UnorientedAngleCongruent
          (hyperplaneGeo4AngleToAmbient_corrected
            (Geo := Geo) x)
          (hyperplaneGeo4AngleToAmbient_corrected
            (Geo := Geo) y) := by

    intro x y hxy

    induction hxy with

    | rel x y hxy =>
        exact
          (hyperplaneGeo4_unorientedAngleCongruent_iff_ambient_corrected
            (Geo := Geo)
            Sigma x y).mp hxy

    | refl x =>
        exact
          Relation.EqvGen.refl
            (hyperplaneGeo4AngleToAmbient_corrected
              (Geo := Geo) x)

    | symm x y _hxy ih =>
        exact
          Relation.EqvGen.symm
            (hyperplaneGeo4AngleToAmbient_corrected
              (Geo := Geo) x)
            (hyperplaneGeo4AngleToAmbient_corrected
              (Geo := Geo) y)
            ih

    | trans x y z _hxy _hyz ihxy ihyz =>
        exact
          Relation.EqvGen.trans
            (hyperplaneGeo4AngleToAmbient_corrected
              (Geo := Geo) x)
            (hyperplaneGeo4AngleToAmbient_corrected
              (Geo := Geo) y)
            (hyperplaneGeo4AngleToAmbient_corrected
              (Geo := Geo) z)
            ihxy ihyz

  have hAmbientMapped :=
    hMap h

  rw [
    hyperplaneGeo4AngleToAmbient_corrected_angle
      (Geo := Geo) Sigma A B C,
    hyperplaneGeo4AngleToAmbient_corrected_angle
      (Geo := Geo) Sigma D E F
  ] at hAmbientMapped

  exact hAmbientMapped

/--
Ambient angle congruence between angles lying in `Sigma` implies angle
congruence inside `HyperplaneGeo4`.
-/
theorem hyperplaneGeo4_angleCongruent_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (A B C D E F : HyperplanePoint4 Geo Sigma)
    (h :
      Geo.AngleCongruent
        A.1 B.1 C.1 D.1 E.1 F.1) :
    (HyperplaneGeo4 Geo Sigma).AngleCongruent
      A B C D E F := by

  unfold Geometry.Geo.AngleCongruent at h ⊢

  apply
    Relation.EqvGen.rel
      ((HyperplaneGeo4 Geo Sigma).Angle A B C)
      ((HyperplaneGeo4 Geo Sigma).Angle D E F)

  apply
    (hyperplaneGeo4_unorientedAngleCongruent_iff_ambient_corrected
      (Geo := Geo)
      Sigma
      ((HyperplaneGeo4 Geo Sigma).Angle A B C)
      ((HyperplaneGeo4 Geo Sigma).Angle D E F)).mpr

  rw [
    hyperplaneGeo4AngleToAmbient_corrected_angle
      (Geo := Geo) Sigma A B C,
    hyperplaneGeo4AngleToAmbient_corrected_angle
      (Geo := Geo) Sigma D E F
  ]

  exact h

/--
For angles entirely contained in one E4 hyperplane, induced and ambient
angle congruence are equivalent.
-/
theorem hyperplaneGeo4_angleCongruent_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (A B C D E F : HyperplanePoint4 Geo Sigma) :
    (HyperplaneGeo4 Geo Sigma).AngleCongruent
        A B C D E F <->
      Geo.AngleCongruent
        A.1 B.1 C.1 D.1 E.1 F.1 := by

  constructor

  · exact
      hyperplaneGeo4_angleCongruent_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C D E F

  · exact
      hyperplaneGeo4_angleCongruent_of_ambient_corrected
        (Geo := Geo)
        Sigma A B C D E F

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hierarchy repair: complete local Group III

Test47 transferred the segment part of Group III.
Test48 rebuilt rays and angle congruence under the corrected E4 hierarchy.

This file adds the same-side bridge and constructs the complete local

  HilbertSpaceCongruence (HyperplaneGeo4 Geo Sigma)

without assuming ambient `HilbertSpaceIncidence Geo`,
`HilbertSpaceOrder Geo`, or `HilbertSpaceCongruence Geo`.
-/

/--
One same-side step in an internal plane of a fixed E4 hyperplane is
equivalent to the corresponding ambient plane-local same-side step.
-/
theorem hyperplaneGeo4_sameSideStep_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (P R : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma) :
    HilbertSameSideStepInPlane
        (HyperplaneGeo4 Geo Sigma) P R l pi <->
      HilbertSameSideStepInPlane
        Geo P.1 R.1 l.1 pi.1 := by

  unfold HilbertSameSideStepInPlane

  constructor

  · rintro
      ⟨hPpi, hRpi, hPl, hRl, hNoMeet⟩

    refine
      ⟨hPpi, hRpi, hPl, hRl, ?_⟩

    intro hMeetAmbient

    apply hNoMeet

    exact
      hyperplaneGeo4_segmentMeetsLine_of_ambient_corrected
        (Geo := Geo)
        Sigma P R l
        hMeetAmbient

  · rintro
      ⟨hPpi, hRpi, hPl, hRl, hNoMeet⟩

    refine
      ⟨hPpi, hRpi, hPl, hRl, ?_⟩

    intro hMeetSlice

    apply hNoMeet

    exact
      hyperplaneGeo4_segmentMeetsLine_to_ambient_corrected
        (Geo := Geo)
        Sigma P R l
        hMeetSlice

/--
A local same-side chain maps to the corresponding ambient chain.
-/
theorem hyperplaneGeo4_sameSideChain_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (P R : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma)
    (hChain :
      Relation.ReflTransGen
        (fun X Y =>
          HilbertSameSideStepInPlane
            (HyperplaneGeo4 Geo Sigma)
            X Y l pi)
        P R) :
    Relation.ReflTransGen
      (fun X Y =>
        HilbertSameSideStepInPlane
          Geo X Y l.1 pi.1)
      P.1 R.1 := by

  induction hChain with

  | refl =>
      exact Relation.ReflTransGen.refl

  | tail hAB hBR ih =>
      exact
        Relation.ReflTransGen.tail
          ih
          ((hyperplaneGeo4_sameSideStep_iff_ambient_corrected
            (Geo := Geo)
            Sigma _ _ l pi).mp hBR)

/--
An ambient same-side chain in an internal plane can be lifted to the
fixed hyperplane slice.
-/
theorem hyperplaneGeo4_exists_sameSideChain_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (P : HyperplanePoint4 Geo Sigma)
    (R : Geo.Point)
    (l : HyperplaneLine4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma)
    (hChain :
      Relation.ReflTransGen
        (fun X Y =>
          HilbertSameSideStepInPlane
            Geo X Y l.1 pi.1)
        P.1 R) :
    exists Rp : HyperplanePoint4 Geo Sigma,
      Rp.1 = R /\
      Relation.ReflTransGen
        (fun X Y =>
          HilbertSameSideStepInPlane
            (HyperplaneGeo4 Geo Sigma)
            X Y l pi)
        P Rp := by

  induction hChain with

  | refl =>
      exact
        ⟨P,
         rfl,
         Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>

      rcases ih with
        ⟨Bp, hBp, hSliceAB⟩

      have hCpi :
          Q.toHilbertSpacePrimitive.OnPlane C pi.1 :=
        hBC.2.1

      have hCSigma :
          Q.OnHyperplane C Sigma :=
        pi.2 C hCpi

      let Cp : HyperplanePoint4 Geo Sigma :=
        ⟨C, hCSigma⟩

      have hSliceBC :
          HilbertSameSideStepInPlane
            (HyperplaneGeo4 Geo Sigma)
            Bp Cp l pi := by

        apply
          (hyperplaneGeo4_sameSideStep_iff_ambient_corrected
            (Geo := Geo)
            Sigma Bp Cp l pi).mpr

        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hSliceAB
           hSliceBC⟩

/--
Ambient same-side chains between two already known hyperplane points
lift to the hyperplane slice.
-/
theorem hyperplaneGeo4_sameSideChain_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (P R : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma)
    (hChain :
      Relation.ReflTransGen
        (fun X Y =>
          HilbertSameSideStepInPlane
            Geo X Y l.1 pi.1)
        P.1 R.1) :
    Relation.ReflTransGen
      (fun X Y =>
        HilbertSameSideStepInPlane
          (HyperplaneGeo4 Geo Sigma)
          X Y l pi)
      P R := by

  rcases
      hyperplaneGeo4_exists_sameSideChain_of_ambient_corrected
        (Geo := Geo)
        Sigma P R.1 l pi hChain with
    ⟨Rp, hRp, hSlice⟩

  have hRpR : Rp = R := by
    apply Subtype.ext
    exact hRp

  simpa [hRpR] using hSlice

/--
Same-side in one internal plane is exactly ambient plane-local
same-side.
-/
theorem hyperplaneGeo4_sameSide_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (P R : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma) :
    HilbertSameSideInPlane
        (HyperplaneGeo4 Geo Sigma) P R l pi <->
      HilbertSameSideInPlane
        Geo P.1 R.1 l.1 pi.1 := by

  unfold HilbertSameSideInPlane

  constructor

  · rintro
      ⟨hPpi, hRpi, hPl, hRl, hChain⟩

    exact
      ⟨hPpi,
       hRpi,
       hPl,
       hRl,
       hyperplaneGeo4_sameSideChain_to_ambient_corrected
         (Geo := Geo)
         Sigma P R l pi hChain⟩

  · rintro
      ⟨hPpi, hRpi, hPl, hRl, hChain⟩

    exact
      ⟨hPpi,
       hRpi,
       hPl,
       hRl,
       hyperplaneGeo4_sameSideChain_of_ambient_corrected
         (Geo := Geo)
         Sigma P R l pi hChain⟩

/--
Every fixed E4 hyperplane inherits the complete old spatial congruence
interface from the corrected E4 ambient congruence layer.
-/
instance hyperplaneGeo4HilbertSpaceCongruence_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceCongruence
      (HyperplaneGeo4 Geo Sigma) where

  segment_construction := by
    intro A B O R hOR

    exact
      hyperplaneGeo4_segment_construction_corrected
        (Geo := Geo)
        Sigma A B O R hOR

  segment_congruence_common := by
    intro A B A' B' A'' B''
      h1 h2

    exact
      hyperplaneGeo4_segment_congruence_common_corrected
        (Geo := Geo)
        Sigma
        A B A' B' A'' B''
        h1 h2

  segment_additivity := by
    intro A B C A' B' C'
      hABC hA'B'C'
      hAB hBC

    exact
      hyperplaneGeo4_segment_additivity_corrected
        (Geo := Geo)
        Sigma
        A B C A' B' C'
        hABC hA'B'C'
        hAB hBC

  angle_construction_in_plane := by
    intro A B C A' B' T
      hABC hA'B'
      pi
      l hlpi
      hA'l hB'l
      hTpi hTl

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C hABC

    have hA'B'val :
        Ne A'.1 B'.1 := by
      intro h
      apply hA'B'
      exact Subtype.ext h

    have hlpiAmbient :
        HilbertLineInPlane Geo l.1 pi.1 :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Sigma l pi hlpi

    rcases
        Hilbert4DAmbientCongruence.angle_construction_in_plane
          (Geo := Geo)
          A.1 B.1 C.1
          A'.1 B'.1 T.1
          hABCAmbient
          hA'B'val
          pi.1
          l.1
          hlpiAmbient
          hA'l
          hB'l
          hTpi
          hTl with
      ⟨C0,
       hSameSideAmbient,
       hAngleAmbient,
       hUniqueAmbient⟩

    have hC0pi :
        Q.toHilbertSpacePrimitive.OnPlane C0 pi.1 :=
      hSameSideAmbient.1

    have hC0Sigma :
        Q.OnHyperplane C0 Sigma :=
      pi.2 C0 hC0pi

    let C0p : HyperplanePoint4 Geo Sigma :=
      ⟨C0, hC0Sigma⟩

    have hSameSideSlice :
        HilbertSameSideInPlane
          (HyperplaneGeo4 Geo Sigma)
          C0p T l pi := by

      apply
        (hyperplaneGeo4_sameSide_iff_ambient_corrected
          (Geo := Geo)
          Sigma C0p T l pi).mpr

      simpa [C0p] using hSameSideAmbient

    have hAngleSlice :
        (HyperplaneGeo4 Geo Sigma).AngleCongruent
          A B C A' B' C0p := by

      apply
        (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
          (Geo := Geo)
          Sigma A B C A' B' C0p).mpr

      simpa [C0p] using hAngleAmbient

    refine
      ⟨C0p,
       hSameSideSlice,
       hAngleSlice,
       ?_⟩

    intro D'
      hSameSideD
      hAngleD

    have hSameSideDAmbient :
        HilbertSameSideInPlane
          Geo D'.1 T.1 l.1 pi.1 :=
      (hyperplaneGeo4_sameSide_iff_ambient_corrected
        (Geo := Geo)
        Sigma D' T l pi).mp
        hSameSideD

    have hAngleDAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A'.1 B'.1 D'.1 :=
      (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
        (Geo := Geo)
        Sigma A B C A' B' D').mp
        hAngleD

    have hRayAmbient :
        HilbertSameRay
          Geo B'.1 C0 D'.1 :=
      hUniqueAmbient
        D'.1
        hSameSideDAmbient
        hAngleDAmbient

    apply
      (hyperplaneGeo4_sameRay_iff_ambient_corrected
        (Geo := Geo)
        Sigma B' C0p D').mpr

    simpa [C0p] using hRayAmbient

  angle_congruence_reflexive := by
    intro A B C hABC

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C hABC

    have hAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A.1 B.1 C.1 :=
      Hilbert4DAmbientCongruence.angle_congruence_reflexive
        (Geo := Geo)
        A.1 B.1 C.1
        hABCAmbient

    exact
      (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
        (Geo := Geo)
        Sigma A B C A B C).mpr
        hAmbient

  sas := by
    intro A B C A' B' C'
      hABC hA'B'C'
      hAB hAC hAngle

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C hABC

    have hA'B'C'Ambient :
        Not (PrimCollinear Geo A'.1 B'.1 C'.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A' B' C' hA'B'C'

    have hABAmbient :
        Geo.Congruent
          A.1 B.1 A'.1 B'.1 :=
      (hyperplaneGeo4_congruent
        (Geo := Geo)
        Sigma A B A' B').mp hAB

    have hACAmbient :
        Geo.Congruent
          A.1 C.1 A'.1 C'.1 :=
      (hyperplaneGeo4_congruent
        (Geo := Geo)
        Sigma A C A' C').mp hAC

    have hAngleAmbient :
        Geo.AngleCongruent
          B.1 A.1 C.1
          B'.1 A'.1 C'.1 :=
      (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
        (Geo := Geo)
        Sigma B A C B' A' C').mp
        hAngle

    have hResultAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A'.1 B'.1 C'.1 :=
      Hilbert4DAmbientCongruence.sas
        (Geo := Geo)
        A.1 B.1 C.1
        A'.1 B'.1 C'.1
        hABCAmbient
        hA'B'C'Ambient
        hABAmbient
        hACAmbient
        hAngleAmbient

    exact
      (hyperplaneGeo4_angleCongruent_iff_ambient_corrected
        (Geo := Geo)
        Sigma A B C A' B' C').mpr
        hResultAmbient

/--
Critical sanity check: a fixed E4 hyperplane again satisfies the complete
old 3D incidence-order-congruence API, but the ambient E4 space does not
need any old 3D typeclass.
-/
example
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceCongruence
      (HyperplaneGeo4 Geo Sigma) := by

  infer_instance

end Geometry

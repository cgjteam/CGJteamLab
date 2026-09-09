import CGJteamLab.Coxeter.E4Incidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hierarchy repair: ambient order and local 3D order

Test44 recovered the full local 3D incidence structure inside each
hyperplane without assuming ambient `HilbertSpaceIncidence Geo`.

The next dependency to repair is Group II.

The old `HilbertSpaceOrder Geo` is mathematically dimension-independent
in content, but its typeclass signature depends on ambient
`HilbertSpaceIncidence Geo`.  Therefore it cannot be reused directly in
a genuine E4 ambient space.

This test introduces an E4 ambient order class with the same Group II
content but depending only on the corrected ambient E4 incidence core,
then reconstructs

  HilbertSpaceOrder (HyperplaneGeo4 Geo Sigma)

inside every fixed hyperplane.
-/

/--
Group II for genuine ambient E4.

II.1-II.3 are ambient line-order axioms.
II.4 is explicitly plane-local.

No ambient `HilbertSpaceIncidence Geo` is assumed.
-/
class Hilbert4DAmbientOrder
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo] : Prop where

  between_incidence :
    forall A B C : Geo.Point,
      Geo.Between A B C ->
      Ne A B /\
      Ne B C /\
      Ne A C /\
      PrimCollinear Geo A B C /\
      Geo.Between C B A

  between_extension :
    forall A C : Geo.Point,
      Ne A C ->
      exists B : Geo.Point,
        Geo.Between A C B

  between_unique :
    forall A B C : Geo.Point,
      PrimCollinear Geo A B C ->
      Geo.Between A B C ->
      Not (Geo.Between B A C) /\
      Not (Geo.Between A C B)

  pasch_in_plane :
    forall pi : Q.toHilbertSpacePrimitive.Plane,
      forall A B C : Geo.Point,
        Q.toHilbertSpacePrimitive.OnPlane A pi ->
        Q.toHilbertSpacePrimitive.OnPlane B pi ->
        Q.toHilbertSpacePrimitive.OnPlane C pi ->
        Not (PrimCollinear Geo A B C) ->
        forall l : Geo.Line,
          HilbertLineInPlane Geo l pi ->
          Not (H.OnLine A l) ->
          Not (H.OnLine B l) ->
          Not (H.OnLine C l) ->
          HilbertSegmentMeetsLine Geo A B l ->
          HilbertSegmentMeetsLine Geo A C l \/
          HilbertSegmentMeetsLine Geo B C l

/--
Internal betweenness is literally ambient betweenness.
-/
theorem hyperplaneGeo4_between_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma) :
    (HyperplaneGeo4 Geo Sigma).Between A B C <->
      Geo.Between A.1 B.1 C.1 := by
  rfl

/--
Internal segment-line intersection implies ambient segment-line
intersection.
-/
theorem hyperplaneGeo4_segmentMeetsLine_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma) :
    HilbertSegmentMeetsLine
        (HyperplaneGeo4 Geo Sigma) A B l ->
      HilbertSegmentMeetsLine Geo A.1 B.1 l.1 := by

  intro h

  rcases h with
    ⟨X, hAXB, hXl⟩

  exact
    ⟨X.1, hAXB, hXl⟩

/--
Ambient segment-line intersection between hyperplane points lifts back
to the hyperplane slice.

The only nontrivial point is proving that the intersection witness lies
in Sigma.  Betweenness gives a line through the two endpoints and the
witness; corrected E4 line-in-hyperplane incidence then puts the witness
in Sigma.
-/
theorem hyperplaneGeo4_segmentMeetsLine_of_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane)
    (A B : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma)
    (h :
      HilbertSegmentMeetsLine Geo A.1 B.1 l.1) :
    HilbertSegmentMeetsLine
      (HyperplaneGeo4 Geo Sigma) A B l := by

  rcases h with
    ⟨X, hAXB, hXl⟩

  have hData :=
    Hilbert4DAmbientOrder.between_incidence
      (Geo := Geo)
      A.1 X B.1 hAXB

  have hAB :
      Ne A.1 B.1 :=
    hData.2.2.1

  rcases hData.2.2.2.1 with
    ⟨k, hAk, hXk, hBk⟩

  have hkSigma :
      HilbertLineInHyperplane4
        Geo k Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      A.1 B.1 hAB
      k hAk hBk
      Sigma A.2 B.2

  have hXSigma :
      Q.OnHyperplane X Sigma :=
    hkSigma X hXk

  let Xp : HyperplanePoint4 Geo Sigma :=
    ⟨X, hXSigma⟩

  exact
    ⟨Xp, hAXB, hXl⟩

/--
A local line lying in a local plane also lies in the corresponding
ambient plane.
-/
theorem hyperplaneGeo4_lineInPlane_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (l : HyperplaneLine4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma)
    (hLocal :
      HilbertLineInPlane
        (HyperplaneGeo4 Geo Sigma)
        l pi) :
    HilbertLineInPlane Geo l.1 pi.1 := by

  intro X hXl

  have hXSigma :
      Q.OnHyperplane X Sigma :=
    l.2 X hXl

  let Xp : HyperplanePoint4 Geo Sigma :=
    ⟨X, hXSigma⟩

  exact
    hLocal Xp hXl

/--
Corrected local Group II instance.

No ambient `HilbertSpaceIncidence Geo` and no ambient
`HilbertSpaceOrder Geo` are assumed.
-/
instance hyperplaneGeo4HilbertSpaceOrder_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceOrder
      (HyperplaneGeo4 Geo Sigma) where

  between_incidence := by
    intro A B C hABC

    have hAmbient :
        Geo.Between A.1 B.1 C.1 :=
      hABC

    have hData :=
      Hilbert4DAmbientOrder.between_incidence
        (Geo := Geo)
        A.1 B.1 C.1
        hAmbient

    have hAB : Ne A B := by
      intro h
      exact hData.1
        (congrArg Subtype.val h)

    have hBC : Ne B C := by
      intro h
      exact hData.2.1
        (congrArg Subtype.val h)

    have hAC : Ne A C := by
      intro h
      exact hData.2.2.1
        (congrArg Subtype.val h)

    have hCol :
        PrimCollinear
          (HyperplaneGeo4 Geo Sigma)
          A B C :=
      hyperplaneGeo4_primCollinear_of_ambient_of_ne_corrected
        (Geo := Geo)
        Sigma A B C
        hData.1
        hData.2.2.2.1

    exact
      ⟨hAB,
       hBC,
       hAC,
       hCol,
       hData.2.2.2.2⟩

  between_extension := by
    intro A C hAC

    have hACval : Ne A.1 C.1 := by
      intro h
      apply hAC
      exact Subtype.ext h

    rcases
        Hilbert4DAmbientOrder.between_extension
          (Geo := Geo)
          A.1 C.1 hACval with
      ⟨B, hACB⟩

    have hData :=
      Hilbert4DAmbientOrder.between_incidence
        (Geo := Geo)
        A.1 C.1 B hACB

    rcases hData.2.2.2.1 with
      ⟨l, hAl, hCl, hBl⟩

    have hlSigma :
        HilbertLineInHyperplane4
          Geo l Sigma :=
      Hilbert4DAmbientIncidence.line_in_hyperplane
        (Geo := Geo)
        A.1 C.1 hACval
        l hAl hCl
        Sigma A.2 C.2

    have hBSigma :
        Q.OnHyperplane B Sigma :=
      hlSigma B hBl

    exact
      ⟨⟨B, hBSigma⟩, hACB⟩

  between_unique := by
    intro A B C hCol hABC

    have hAmbientCol :
        PrimCollinear Geo A.1 B.1 C.1 :=
      hyperplaneGeo4_primCollinear_to_ambient
        (Geo := Geo)
        Sigma A B C hCol

    have hUnique :=
      Hilbert4DAmbientOrder.between_unique
        (Geo := Geo)
        A.1 B.1 C.1
        hAmbientCol
        hABC

    exact hUnique

  pasch_in_plane := by
    intro pi
      A B C
      hApi hBpi hCpi
      hABC
      l hlpi
      hAl hBl hCl
      hABmeet

    have hAmbientABC :
        Not
          (PrimCollinear
            Geo A.1 B.1 C.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C hABC

    have hlpiAmbient :
        HilbertLineInPlane
          Geo l.1 pi.1 :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Sigma l pi hlpi

    have hABmeetAmbient :
        HilbertSegmentMeetsLine
          Geo A.1 B.1 l.1 :=
      hyperplaneGeo4_segmentMeetsLine_to_ambient_corrected
        (Geo := Geo)
        Sigma A B l hABmeet

    have hPasch :=
      Hilbert4DAmbientOrder.pasch_in_plane
        (Geo := Geo)
        pi.1
        A.1 B.1 C.1
        hApi hBpi hCpi
        hAmbientABC
        l.1 hlpiAmbient
        hAl hBl hCl
        hABmeetAmbient

    rcases hPasch with
      hACmeet | hBCmeet

    · exact
        Or.inl
          (hyperplaneGeo4_segmentMeetsLine_of_ambient_corrected
            (Geo := Geo)
            Sigma A C l hACmeet)

    · exact
        Or.inr
          (hyperplaneGeo4_segmentMeetsLine_of_ambient_corrected
            (Geo := Geo)
            Sigma B C l hBCmeet)

/--
Critical sanity check: Group II is recovered locally in every
hyperplane from the corrected ambient E4 order layer.
-/
example
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceOrder
      (HyperplaneGeo4 Geo Sigma) := by

  infer_instance

end Geometry

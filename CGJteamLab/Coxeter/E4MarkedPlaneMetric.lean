import CGJteamLab.Coxeter.E4NormalCore
import CGJteamLab.HilbertRightAngle
import CGJteamLab.Proposition11_4

/-!
# Corrected E4 marked-plane metric layer

Production promotion of the validated planar side, order, ray,
segment, angle, full congruence, and perpendicular-uniqueness machinery
for an ambient E4 plane.

Known proof-local `letI` linter warnings from the workshop chain are
removed here by using ordinary `let` bindings.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Planar kernel for E4 normal uniqueness

Test53 reduced the E4 same-foot normal problem to one ambient 2-plane.

This file isolates the planar uniqueness step in ordinary Hilbert
geometry.

If two lines through F contain rays FA and FC lying on the same side
of a base line n, and both rays form right angles with the same base
ray FX, then the two lines coincide.

The proof uses Hilbert III.4 uniqueness of angle construction together
with Hilbert Theorem 21 for right angles.
-/

/--
Two same-side right-angle rays erected from the same base ray determine
the same incidence line.
-/
theorem hilbert_perpendicular_lines_equal_of_same_side_witness
    [H : HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (l m n : Geo.Line)
    (F X A C : Geo.Point)
    (hFX : Ne F X)
    (hFn : H.OnLine F n)
    (hXn : H.OnLine X n)
    (hFl : H.OnLine F l)
    (hAl : H.OnLine A l)
    (hFm : H.OnLine F m)
    (hCm : H.OnLine C m)
    (hAF : Ne A F)
    (hCF : Ne C F)
    (hSame : HilbertSameSide Geo A C n)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightC : HilbertRightAngle Geo X F C) :
    l = m := by

  have hXFA :
      Not (PrimCollinear Geo X F A) :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      n
      hFX.symm
      hXn
      hFn
      hSame.1

  have hXFC :
      Not (PrimCollinear Geo X F C) :=
    hilbert_not_collinear_of_off_line
      Geo
      X F C
      n
      hFX.symm
      hXn
      hFn
      hSame.2.1

  have hCong :
      Geo.AngleCongruent X F A X F C :=
    hilbert_same_base_right_angles_congruent
      Geo
      A C F X
      n
      hFn
      hXn
      hFX
      hSame
      hRightA
      hRightC

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X F A
        X F A
        hXFA
        hFX.symm
        n
        hXn
        hFn
        hSame.1 with
    ⟨E, _hEASame, _hCopy, hUnique⟩

  have hAASame :
      HilbertSameSide Geo A A n :=
    hilbert_sameSide_refl
      Geo A n hSame.1

  have hRefl :
      Geo.AngleCongruent X F A X F A :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      X F A
      hXFA

  have hRayEA :
      HilbertSameRay Geo F E A :=
    hUnique
      A
      hAASame
      hRefl

  have hCASame :
      HilbertSameSide Geo C A n :=
    hilbert_sameSide_symm
      Geo A C n hSame

  have hRayEC :
      HilbertSameRay Geo F E C :=
    hUnique
      C
      hCASame
      hCong

  have hRayAC :
      HilbertSameRay Geo F A C :=
    hilbert_sameRay_of_common
      Geo
      F E A C
      hRayEA
      hRayEC

  have hCl :
      H.OnLine C l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAF.symm
      hFl
      hAl
      hRayAC.2.2.1

  exact
    HilbertPlaneIncidence.line_unique
      F C hCF.symm
      l m
      hFl hCl
      hFm hCm

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Planar side parity for E4 normal uniqueness

The same-foot perpendicular uniqueness proof has one remaining
orientation issue.

If A and B are on opposite sides of a line n, and B and C are also
on opposite sides of n, then A and C are on the same side of n,
provided A,B,C are noncollinear.

This is proved synthetically from Pasch/separation:
if A and C were also on opposite sides, n would meet the interiors
of all three sides of triangle ABC, contradicting the existing
third-side avoidance theorem.
-/

/--
For a nondegenerate triangle, two successive opposite-side relations
with respect to one line imply a same-side relation for the outer
vertices.
-/
theorem hilbert_sameSide_of_two_oppositeSides
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C : Geo.Point)
    (n : Geo.Line)
    (hAB :
      HilbertOppositeSide Geo A B n)
    (hBC :
      HilbertOppositeSide Geo B C n)
    (hABC :
      Not (PrimCollinear Geo A B C)) :
    HilbertSameSide Geo A C n := by

  by_contra hNotSame

  have hAC :
      HilbertOppositeSide Geo A C n :=
    hilbert_oppositeSide_of_not_sameSide
      Geo
      A C n
      hAB.1
      hBC.2.1
      hNotSame

  let X : Geo.Point :=
    Classical.choose hAB.2.2

  have hXData :
      Geo.Between A X B /\
      H.OnLine X n :=
    Classical.choose_spec hAB.2.2

  let Y : Geo.Point :=
    Classical.choose hBC.2.2

  have hYData :
      Geo.Between B Y C /\
      H.OnLine Y n :=
    Classical.choose_spec hBC.2.2

  have hBXA :
      Geo.Between B X A :=
    (HilbertOrder.between_incidence
      A X B hXData.1).2.2.2.2

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  have hNoMeetAC :
      Not (HilbertSegmentMeetsLine Geo A C n) :=
    hilbert_line_avoids_third_triangle_side
      Geo
      B A C
      X Y
      n
      hBAC
      hBXA
      hYData.1
      hXData.2
      hYData.2

  exact
    hNoMeetAC hAC.2.2

/--
If A and C are on opposite sides of n and D is obtained by extending
the line CF through F, where F lies on n, then A and D are on the same
side of n, as soon as A,C,D form a nondegenerate triangle and D is off n.
-/
theorem hilbert_sameSide_after_crossing_base_point
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A C D F : Geo.Point)
    (n : Geo.Line)
    (hAC :
      HilbertOppositeSide Geo A C n)
    (hCFD :
      Geo.Between C F D)
    (hFn :
      H.OnLine F n)
    (hDoff :
      Not (H.OnLine D n))
    (hACD :
      Not (PrimCollinear Geo A C D)) :
    HilbertSameSide Geo A D n := by

  have hCD :
      HilbertOppositeSide Geo C D n := by
    constructor
    exact hAC.2.1
    constructor
    exact hDoff
    exact
      Exists.intro
        F
        (And.intro hCFD hFn)

  exact
    hilbert_sameSide_of_two_oppositeSides
      Geo
      A C D
      n
      hAC
      hCD
      hACD

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 marked 2-plane: corrected planar incidence and order

The plane pi used in the same-foot normal argument is not an arbitrary
primitive plane: test53 constructs it from three explicit noncollinear
points.  That witness is exactly what is needed to recover the ordinary
2D Hilbert incidence/order API on PlaneGeo Geo pi without installing any
old ambient 3D class on Geo.

This file reconstructs:

  HilbertPlaneIncidence (PlaneGeo Geo pi)
  HilbertOrder          (PlaneGeo Geo pi)

from the corrected E4 ambient incidence/order classes and one explicit
nondegenerate triple in pi.
-/

/--
Two distinct points of a corrected E4 ambient 2-plane determine a line
of the induced PlaneGeo.
-/
theorem planePoint_line_through4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B : PlanePoint Geo pi)
    (hAB : Ne A B) :
    exists l : PlaneLine Geo pi,
      PlaneOnLine Geo A l /\
      PlaneOnLine Geo B l := by

  have hABval : Ne A.1 B.1 := by
    intro h
    apply hAB
    exact Subtype.ext h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A.1 B.1 hABval with
    ⟨l, hAl, hBl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    H4I.line_in_plane
      A.1 B.1 hABval
      l hAl hBl
      pi A.2 B.2

  exact
    ⟨⟨l, hlpi⟩, hAl, hBl⟩

/--
Ambient collinearity of three points of pi lifts to collinearity in
PlaneGeo pi as soon as two underlying points are distinct.
-/
theorem planeGeo_primCollinear_of_ambient_of_ne4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C : PlanePoint Geo pi)
    (hAB : Ne A.1 B.1)
    (hCol : PrimCollinear Geo A.1 B.1 C.1) :
    PrimCollinear (PlaneGeo Geo pi) A B C := by

  rcases hCol with
    ⟨l, hAl, hBl, hCl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    H4I.line_in_plane
      A.1 B.1 hAB
      l hAl hBl
      pi A.2 B.2

  exact
    ⟨⟨l, hlpi⟩, hAl, hBl, hCl⟩

/--
A marked nondegenerate E4 2-plane inherits ordinary planar Hilbert
incidence.  The marking A0,B0,C0 supplies the I.3 nondegeneracy clause.
-/
theorem planeGeoHilbertPlaneIncidence4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A0 B0 C0 : Geo.Point)
    (hA0pi : Q.toHilbertSpacePrimitive.OnPlane A0 pi)
    (hB0pi : Q.toHilbertSpacePrimitive.OnPlane B0 pi)
    (hC0pi : Q.toHilbertSpacePrimitive.OnPlane C0 pi)
    (hABC : Not (PrimCollinear Geo A0 B0 C0)) :
    HilbertPlaneIncidence (PlaneGeo Geo pi) := by

  let A : PlanePoint Geo pi :=
    ⟨A0, hA0pi⟩

  let B : PlanePoint Geo pi :=
    ⟨B0, hB0pi⟩

  let C : PlanePoint Geo pi :=
    ⟨C0, hC0pi⟩

  have hABval : Ne A0 B0 :=
    hilbert_noncollinear_ne_first
      Geo A0 B0 C0 hABC

  have hAB : Ne A B := by
    intro h
    apply hABval
    exact congrArg Subtype.val h

  refine
    {
      line_through := ?_
      line_unique := ?_
      two_points_on_line := ?_
      three_noncollinear := ?_
    }

  · intro P R hPR
    exact
      planePoint_line_through4_corrected
        (Geo := Geo)
        pi P R hPR

  · intro P R hPR l m hPl hRl hPm hRm
    exact
      planePoint_line_unique
        (Geo := Geo)
        pi P R hPR
        l m hPl hRl hPm hRm

  · rcases
        planePoint_line_through4_corrected
          (Geo := Geo)
          pi A B hAB with
      ⟨l, hAl, hBl⟩

    exact
      ⟨l, A, B, hAB, hAl, hBl⟩

  · refine ⟨A, B, C, ?_⟩
    intro hCol
    exact
      hABC
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi A B C hCol)

/--
A marked E4 2-plane also inherits ordinary planar Hilbert order.
Pasch is obtained only by specializing the corrected ambient E4
plane-local Pasch axiom to pi.
-/
theorem planeGeoHilbertOrder4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A0 B0 C0 : Geo.Point)
    (hA0pi : Q.toHilbertSpacePrimitive.OnPlane A0 pi)
    (hB0pi : Q.toHilbertSpacePrimitive.OnPlane B0 pi)
    (hC0pi : Q.toHilbertSpacePrimitive.OnPlane C0 pi)
    (hABC : Not (PrimCollinear Geo A0 B0 C0)) :
    HilbertOrder (PlaneGeo Geo pi) := by

  let : HilbertPlaneIncidence (PlaneGeo Geo pi) :=
    planeGeoHilbertPlaneIncidence4_corrected
      (Geo := Geo)
      pi A0 B0 C0
      hA0pi hB0pi hC0pi hABC

  refine
    {
      between_incidence := ?_
      between_extension := ?_
      between_unique := ?_
      pasch := ?_
    }

  · intro A B C hBetween

    have hData :=
      H4O.between_incidence
        A.1 B.1 C.1 hBetween

    rcases hData with
      ⟨hAB, hBC, hAC, hCol, hCBA⟩

    have hABplane : Ne A B := by
      intro h
      exact hAB (congrArg Subtype.val h)

    have hBCplane : Ne B C := by
      intro h
      exact hBC (congrArg Subtype.val h)

    have hACplane : Ne A C := by
      intro h
      exact hAC (congrArg Subtype.val h)

    have hColPlane :
        PrimCollinear (PlaneGeo Geo pi) A B C :=
      planeGeo_primCollinear_of_ambient_of_ne4_corrected
        (Geo := Geo)
        pi A B C hAB hCol

    exact
      ⟨hABplane,
       hBCplane,
       hACplane,
       hColPlane,
       hCBA⟩

  · intro A C hAC

    have hACval : Ne A.1 C.1 := by
      intro h
      apply hAC
      exact Subtype.ext h

    rcases
        H4O.between_extension
          A.1 C.1 hACval with
      ⟨B, hACB⟩

    have hData :=
      H4O.between_incidence
        A.1 C.1 B hACB

    rcases hData with
      ⟨_hAC, _hCB, _hAB, hCol, _hBCA⟩

    rcases hCol with
      ⟨l, hAl, hCl, hBl⟩

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      H4I.line_in_plane
        A.1 C.1 hACval
        l hAl hCl
        pi A.2 C.2

    have hBpi :
        Q.toHilbertSpacePrimitive.OnPlane B pi :=
      hlpi B hBl

    exact
      ⟨⟨B, hBpi⟩, hACB⟩

  · intro A B C hCol hBetween

    have hColAmbient :
        PrimCollinear Geo A.1 B.1 C.1 :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi A B C hCol

    exact
      H4O.between_unique
        A.1 B.1 C.1
        hColAmbient
        hBetween

  · intro A B C hABCplane l
      hAl hBl hCl hABmeet

    have hABplane : Ne A B :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        A B C hABCplane

    have hAB : Ne A.1 B.1 := by
      intro h
      apply hABplane
      exact Subtype.ext h

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) := by
      intro hCol
      exact
        hABCplane
          (planeGeo_primCollinear_of_ambient_of_ne4_corrected
            (Geo := Geo)
            pi A B C hAB hCol)

    have hABmeetAmbient :
        HilbertSegmentMeetsLine Geo A.1 B.1 l.1 :=
      (planeGeo_segmentMeetsLine_iff_ambient
        (Geo := Geo)
        pi A B l).mp hABmeet

    have hPasch :=
      H4O.pasch_in_plane
        pi
        A.1 B.1 C.1
        A.2 B.2 C.2
        hABCAmbient
        l.1 l.2
        hAl hBl hCl
        hABmeetAmbient

    rcases hPasch with hACmeet | hBCmeet

    · exact Or.inl
        ((planeGeo_segmentMeetsLine_iff_ambient
          (Geo := Geo)
          pi A C l).mpr hACmeet)

    · exact Or.inr
        ((planeGeo_segmentMeetsLine_iff_ambient
          (Geo := Geo)
          pi B C l).mpr hBCmeet)

/--
Sanity check: the marked plane from three explicit noncollinear points
really supplies the ordinary planar Group I-II API.
-/
theorem hilbert4D_marked_plane_order_recovered
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C : Geo.Point)
    (hApi : Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hBpi : Q.toHilbertSpacePrimitive.OnPlane B pi)
    (hCpi : Q.toHilbertSpacePrimitive.OnPlane C pi)
    (hABC : Not (PrimCollinear Geo A B C)) :
    Nonempty (HilbertOrder (PlaneGeo Geo pi)) := by

  exact
    ⟨planeGeoHilbertOrder4_corrected
      (Geo := Geo)
      pi A B C
      hApi hBpi hCpi hABC⟩

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 marked 2-plane: ray bridge and Group III.1

Test56 recovered ordinary Hilbert incidence and order on a concrete
marked ambient 2-plane.

This file adds the corrected same-ray bridge and tests the first
congruence axiom locally in that plane.

No global ambient HilbertSpaceIncidence, HilbertSpaceOrder, or
HilbertCongruence instance is introduced.
-/

/--
Ambient collinearity through two distinct points of pi forces the third
point to lie in pi.
-/
theorem hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4I : Hilbert4DAmbientIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O P X : Geo.Point)
    (hOP : Ne O P)
    (hOpi : Q.toHilbertSpacePrimitive.OnPlane O pi)
    (hPpi : Q.toHilbertSpacePrimitive.OnPlane P pi)
    (hCol : PrimCollinear Geo O P X) :
    Q.toHilbertSpacePrimitive.OnPlane X pi := by

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        O P hOP with
    ⟨l, hOl, hPl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    H4I.line_in_plane
      O P hOP
      l hOl hPl
      pi hOpi hPpi

  have hXl :
      H.OnLine X l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hOP
      hOl hPl
      hCol

  exact hlpi X hXl

/--
The Hilbert same-ray predicate in a corrected E4 marked plane is exactly
the ambient same-ray predicate on underlying points.
-/
theorem planeGeo_sameRay_iff_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O P X : PlanePoint Geo pi) :
    HilbertSameRay
        (PlaneGeo Geo pi) O P X <->
      HilbertSameRay Geo O.1 P.1 X.1 := by

  unfold HilbertSameRay

  constructor

  · rintro ⟨hPO, hXO, hCol, hNotBetween⟩

    have hPOval : Ne P.1 O.1 := by
      intro h
      apply hPO
      exact Subtype.ext h

    have hXOval : Ne X.1 O.1 := by
      intro h
      apply hXO
      exact Subtype.ext h

    have hColAmbient :
        PrimCollinear Geo O.1 P.1 X.1 :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi O P X hCol

    exact
      ⟨hPOval,
       hXOval,
       hColAmbient,
       hNotBetween⟩

  · rintro ⟨hPO, hXO, hCol, hNotBetween⟩

    have hPOplane : Ne P O := by
      intro h
      exact hPO (congrArg Subtype.val h)

    have hXOplane : Ne X O := by
      intro h
      exact hXO (congrArg Subtype.val h)

    have hOP : Ne O.1 P.1 :=
      hPO.symm

    have hColPlane :
        PrimCollinear
          (PlaneGeo Geo pi) O P X :=
      planeGeo_primCollinear_of_ambient_of_ne4_corrected
        (Geo := Geo)
        pi O P X
        hOP hCol

    exact
      ⟨hPOplane,
       hXOplane,
       hColPlane,
       hNotBetween⟩

/--
If two underlying points A,B of pi are distinct, ambient collinearity
of A,B,C lifts to PlaneGeo pi.  Therefore noncollinearity in PlaneGeo
implies ambient noncollinearity under the same explicit A != B datum.

The explicit inequality avoids introducing an arbitrary unmarked
HilbertPlaneIncidence instance on PlaneGeo pi.
-/
theorem planeGeo_not_primCollinear_to_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C : PlanePoint Geo pi)
    (hAB : Ne A.1 B.1)
    (hABC :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi) A B C)) :
    Not (PrimCollinear Geo A.1 B.1 C.1) := by

  intro hCol

  exact
    hABC
      (planeGeo_primCollinear_of_ambient_of_ne4_corrected
        (Geo := Geo)
        pi A B C
        hAB hCol)

/--
Corrected E4 Group III.1 restricted to one marked 2-plane.
-/
theorem planeGeo_segment_construction4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B O R : PlanePoint Geo pi)
    (hOR : Ne O R) :
    exists X : PlanePoint Geo pi,
      HilbertSameRay
        (PlaneGeo Geo pi) O R X /\
      (PlaneGeo Geo pi).Congruent
        O X A B := by

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

  have hXpi :
      Q.toHilbertSpacePrimitive.OnPlane X pi :=
    hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
      (Geo := Geo)
      pi
      O.1 R.1 X
      hORval
      O.2 R.2
      hRayAmbient.2.2.1

  let Xp : PlanePoint Geo pi :=
    ⟨X, hXpi⟩

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo pi) O R Xp := by

    apply
      (planeGeo_sameRay_iff_ambient4_corrected
        (Geo := Geo)
        pi O R Xp).mpr

    simpa [Xp] using hRayAmbient

  have hCongPlane :
      (PlaneGeo Geo pi).Congruent
        O Xp A B := by

    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi O Xp A B).mpr

    simpa [Xp] using hCongAmbient

  exact
    ⟨Xp,
     hRayPlane,
     hCongPlane⟩

/--
Sanity check for the first local congruence clause.
-/
theorem hilbert4D_marked_plane_segment_construction_recovered
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B O R : PlanePoint Geo pi)
    (hOR : Ne O R) :
    exists X : PlanePoint Geo pi,
      HilbertSameRay
        (PlaneGeo Geo pi) O R X /\
      (PlaneGeo Geo pi).Congruent
        O X A B := by

  exact
    planeGeo_segment_construction4_corrected
      (Geo := Geo)
      pi A B O R hOR

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 marked 2-plane: Group III.2 and III.3

Test57 recovered the same-ray bridge and the local segment
construction axiom on a marked ambient 2-plane.

This file transfers the next two segment-congruence clauses:

* III.2 common congruence;
* III.3 segment additivity.

Everything is reduced definitionally to the corrected ambient E4
congruence layer through `planeGeo_congruent` and `planeGeo_between`.
-/

/--
Corrected E4 Group III.2 restricted to one marked 2-plane.
-/
theorem planeGeo_segment_congruence_common4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B A1 B1 A2 B2 : PlanePoint Geo pi)
    (h1 :
      (PlaneGeo Geo pi).Congruent
        A B A1 B1)
    (h2 :
      (PlaneGeo Geo pi).Congruent
        A B A2 B2) :
    (PlaneGeo Geo pi).Congruent
      A1 B1 A2 B2 := by

  have h1Ambient :
      Geo.Congruent
        A.1 B.1 A1.1 B1.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi A B A1 B1).mp h1

  have h2Ambient :
      Geo.Congruent
        A.1 B.1 A2.1 B2.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi A B A2 B2).mp h2

  have hResult :
      Geo.Congruent
        A1.1 B1.1 A2.1 B2.1 :=
    Hilbert4DAmbientCongruence.segment_congruence_common
      (Geo := Geo)
      A.1 B.1
      A1.1 B1.1
      A2.1 B2.1
      h1Ambient
      h2Ambient

  exact
    (planeGeo_congruent
      (Geo := Geo)
      pi A1 B1 A2 B2).mpr
      hResult

/--
Corrected E4 Group III.3 restricted to one marked 2-plane.
-/
theorem planeGeo_segment_additivity4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C A1 B1 C1 : PlanePoint Geo pi)
    (hABC :
      (PlaneGeo Geo pi).Between A B C)
    (hA1B1C1 :
      (PlaneGeo Geo pi).Between A1 B1 C1)
    (hAB :
      (PlaneGeo Geo pi).Congruent
        A B A1 B1)
    (hBC :
      (PlaneGeo Geo pi).Congruent
        B C B1 C1) :
    (PlaneGeo Geo pi).Congruent
      A C A1 C1 := by

  have hABAmbient :
      Geo.Congruent
        A.1 B.1 A1.1 B1.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi A B A1 B1).mp hAB

  have hBCAmbient :
      Geo.Congruent
        B.1 C.1 B1.1 C1.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi B C B1 C1).mp hBC

  have hABCAmbient :
      Geo.Between A.1 B.1 C.1 :=
    (planeGeo_between
      (Geo := Geo)
      pi A B C).mp hABC

  have hA1B1C1Ambient :
      Geo.Between A1.1 B1.1 C1.1 :=
    (planeGeo_between
      (Geo := Geo)
      pi A1 B1 C1).mp hA1B1C1

  have hResult :
      Geo.Congruent
        A.1 C.1 A1.1 C1.1 :=
    Hilbert4DAmbientCongruence.segment_additivity
      (Geo := Geo)
      A.1 B.1 C.1
      A1.1 B1.1 C1.1
      hABCAmbient
      hA1B1C1Ambient
      hABAmbient
      hBCAmbient

  exact
    (planeGeo_congruent
      (Geo := Geo)
      pi A C A1 C1).mpr
      hResult

/--
Sanity bundle: the complete segment part III.1-III.3 is now available
on a marked corrected E4 2-plane.
-/
theorem hilbert4D_marked_plane_groupIII_segments_recovered
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B O R : PlanePoint Geo pi)
    (hOR : Ne O R) :
    exists X : PlanePoint Geo pi,
      HilbertSameRay
        (PlaneGeo Geo pi) O R X /\
      (PlaneGeo Geo pi).Congruent
        O X A B := by

  exact
    planeGeo_segment_construction4_corrected
      (Geo := Geo)
      pi A B O R hOR

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 marked 2-plane: corrected ray and angle bridge

The generic PlaneGeo bridge in Hilbert3DInterface was written for the
old ambient 3D hierarchy.  In genuine E4 we must not install those old
ambient typeclasses.

This file reconstructs only the representation bridge needed by Group III:

* ambient same-direction chains stay in a fixed ambient 2-plane;
* PlaneGeo ray membership is equivalent to ambient ray membership;
* forgetting PlaneGeo rays gives the ambient rays;
* PlaneGeo angle congruence is equivalent to ambient angle congruence.

The proof uses only the corrected E4 incidence/order hierarchy.
-/

/--
One ambient same-direction step starting from a point of pi stays in pi.
-/
theorem hilbert4D_sameDirectionStep_preserves_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O P X : Geo.Point)
    (hOpi : Q.toHilbertSpacePrimitive.OnPlane O pi)
    (hPpi : Q.toHilbertSpacePrimitive.OnPlane P pi)
    (hStep : Geo.SameDirectionStep O P X) :
    Q.toHilbertSpacePrimitive.OnPlane X pi := by

  unfold Geometry.Geo.SameDirectionStep at hStep

  rcases hStep with
    ⟨hPO, _hXO, hCases⟩

  have hOP : Ne O P :=
    hPO.symm

  rcases hCases with hPX | hOPX | hOXP

  · rw [← hPX]
    exact hPpi

  · have hCol :
        PrimCollinear Geo O P X :=
      (H4O.between_incidence
        O P X hOPX).2.2.2.1

    exact
      hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
        (Geo := Geo)
        pi O P X
        hOP hOpi hPpi hCol

  · have hColOXP :
        PrimCollinear Geo O X P :=
      (H4O.between_incidence
        O X P hOXP).2.2.2.1

    have hColOPX :
        PrimCollinear Geo O P X :=
      PrimCollinearRotate
        Geo O X P hColOXP

    exact
      hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
        (Geo := Geo)
        pi O P X
        hOP hOpi hPpi hColOPX

/--
Every endpoint of an ambient same-direction chain starting in pi
remains in pi.
-/
theorem hilbert4D_reflTransGen_sameDirection_preserves_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A X : Geo.Point)
    (hOpi : Q.toHilbertSpacePrimitive.OnPlane O pi)
    (hApi : Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O)
        A X) :
    Q.toHilbertSpacePrimitive.OnPlane X pi := by

  induction hChain with

  | refl =>
      exact hApi

  | tail hAB hBX ih =>
      exact
        hilbert4D_sameDirectionStep_preserves_plane_corrected
          (Geo := Geo)
          pi
          O _ _
          hOpi
          ih
          hBX

/--
A same-direction chain in PlaneGeo gives the ambient chain.
This direction is purely representational.
-/
theorem planeGeo_reflTransGen_sameDirection_to_ambient4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A X : PlanePoint Geo pi)
    (hChain :
      Relation.ReflTransGen
        ((PlaneGeo Geo pi).SameDirectionStep O)
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
          ((planeGeo_sameDirectionStep_iff_ambient
              (Geo := Geo)
              pi O _ _).mp hBX)

/--
Lift an ambient same-direction chain into PlaneGeo.
-/
theorem planeGeo_exists_reflTransGen_sameDirection_of_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A : PlanePoint Geo pi)
    (X : Geo.Point)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X) :
    exists Xp : PlanePoint Geo pi,
      Xp.1 = X /\
      Relation.ReflTransGen
        ((PlaneGeo Geo pi).SameDirectionStep O)
        A Xp := by

  induction hChain with

  | refl =>
      exact
        ⟨A,
         rfl,
         Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>

      rcases ih with
        ⟨Bp, hBp, hPlaneAB⟩

      have hBpi :
          Q.toHilbertSpacePrimitive.OnPlane B pi := by
        simpa [hBp] using Bp.2

      have hCpi :
          Q.toHilbertSpacePrimitive.OnPlane C pi :=
        hilbert4D_sameDirectionStep_preserves_plane_corrected
          (Geo := Geo)
          pi
          O.1 B C
          O.2
          hBpi
          hBC

      let Cp : PlanePoint Geo pi :=
        ⟨C, hCpi⟩

      have hPlaneBC :
          (PlaneGeo Geo pi).SameDirectionStep O Bp Cp := by

        apply
          (planeGeo_sameDirectionStep_iff_ambient
            (Geo := Geo)
            pi O Bp Cp).mpr

        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hPlaneAB
           hPlaneBC⟩

/--
Ambient same-direction chain with a prescribed PlaneGeo endpoint.
-/
theorem planeGeo_reflTransGen_sameDirection_of_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A X : PlanePoint Geo pi)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1) :
    Relation.ReflTransGen
      ((PlaneGeo Geo pi).SameDirectionStep O)
      A X := by

  rcases
      planeGeo_exists_reflTransGen_sameDirection_of_ambient4_corrected
        (Geo := Geo)
        pi O A X.1 hChain with
    ⟨Xp, hXpVal, hPlaneChain⟩

  have hXpX : Xp = X := by
    apply Subtype.ext
    exact hXpVal

  simpa [hXpX] using hPlaneChain

/--
Ray membership in PlaneGeo pi is exactly ambient ray membership.
-/
theorem planeGeo_mem_ray_iff_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A X : PlanePoint Geo pi) :
    X ∈ (PlaneGeo Geo pi).ray O A <->
      X.1 ∈ Geo.ray O.1 A.1 := by

  change
    (X = O \/
      Relation.ReflTransGen
        ((PlaneGeo Geo pi).SameDirectionStep O)
        A X) <->
    (X.1 = O.1 \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1)

  constructor

  · rintro (hXO | hAX)

    · exact
        Or.inl (congrArg Subtype.val hXO)

    · exact
        Or.inr
          (planeGeo_reflTransGen_sameDirection_to_ambient4_corrected
            (Geo := Geo)
            pi O A X hAX)

  · rintro (hXO | hAX)

    · exact
        Or.inl (Subtype.ext hXO)

    · exact
        Or.inr
          (planeGeo_reflTransGen_sameDirection_of_ambient4_corrected
            (Geo := Geo)
            pi O A X hAX)

/--
Every ambient point of a ray determined by two points of pi lies in pi.
-/
theorem hilbert4D_onPlane_of_mem_ray_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A : PlanePoint Geo pi)
    (X : Geo.Point)
    (hX : X ∈ Geo.ray O.1 A.1) :
    Q.toHilbertSpacePrimitive.OnPlane X pi := by

  change
    X = O.1 \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X at hX

  rcases hX with hXO | hAX

  · rw [hXO]
    exact O.2

  · exact
      hilbert4D_reflTransGen_sameDirection_preserves_plane_corrected
        (Geo := Geo)
        pi
        O.1 A.1 X
        O.2 A.2
        hAX

/--
Forgetting plane membership sends a PlaneGeo ray exactly to the
corresponding ambient ray.
-/
theorem planeGeo_ray_to_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (O A : PlanePoint Geo pi) :
    planePointSetToAmbient
        (Geo := Geo)
        (pi := pi)
        ((PlaneGeo Geo pi).ray O A) =
      Geo.ray O.1 A.1 := by

  apply Set.ext
  intro X

  constructor

  · rintro ⟨Xp, hXpRay, rfl⟩

    exact
      (planeGeo_mem_ray_iff_ambient4_corrected
        (Geo := Geo)
        pi O A Xp).mp hXpRay

  · intro hXRay

    have hXpi :
        Q.toHilbertSpacePrimitive.OnPlane X pi :=
      hilbert4D_onPlane_of_mem_ray_corrected
        (Geo := Geo)
        pi O A X hXRay

    let Xp : PlanePoint Geo pi :=
      ⟨X, hXpi⟩

    have hXpRay :
        Xp ∈ (PlaneGeo Geo pi).ray O A := by

      apply
        (planeGeo_mem_ray_iff_ambient4_corrected
          (Geo := Geo)
          pi O A Xp).mpr

      simpa [Xp] using hXRay

    exact
      ⟨Xp, hXpRay, rfl⟩

/--
The mapped angle of three PlaneGeo points is exactly the ambient angle.
-/
theorem planeGeo_angle_to_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C : PlanePoint Geo pi) :
    ( ((PlaneGeo Geo pi).Angle A B C).1.1,
      mapUnorderedPair
        (planePointSetToAmbient (Geo := Geo) (pi := pi))
        ((PlaneGeo Geo pi).Angle A B C).2 ) =
      Geo.Angle A.1 B.1 C.1 := by

  change
    ( B.1,
      mapUnorderedPair
        (planePointSetToAmbient (Geo := Geo) (pi := pi))
        (UnorderedPair.mk
          ((PlaneGeo Geo pi).ray B A)
          ((PlaneGeo Geo pi).ray B C)) ) =
    ( B.1,
      UnorderedPair.mk
        (Geo.ray B.1 A.1)
        (Geo.ray B.1 C.1) )

  have hMap :
      mapUnorderedPair
          (planePointSetToAmbient (Geo := Geo) (pi := pi))
          (UnorderedPair.mk
            ((PlaneGeo Geo pi).ray B A)
            ((PlaneGeo Geo pi).ray B C)) =
        UnorderedPair.mk
          (planePointSetToAmbient
            (Geo := Geo) (pi := pi)
            ((PlaneGeo Geo pi).ray B A))
          (planePointSetToAmbient
            (Geo := Geo) (pi := pi)
            ((PlaneGeo Geo pi).ray B C)) := by
    exact
      mapUnorderedPair_mk
        (planePointSetToAmbient (Geo := Geo) (pi := pi))
        ((PlaneGeo Geo pi).ray B A)
        ((PlaneGeo Geo pi).ray B C)

  rw [hMap]

  rw [
    planeGeo_ray_to_ambient4_corrected
      (Geo := Geo)
      pi B A,
    planeGeo_ray_to_ambient4_corrected
      (Geo := Geo)
      pi B C
  ]

/--
The generic forgetting map sends an actual PlaneGeo angle to the
ambient angle, in the corrected E4 hierarchy.
-/
theorem planeGeoAngleToAmbient_angle4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C : PlanePoint Geo pi) :
    planeGeoAngleToAmbient
        (Geo := Geo)
        ((PlaneGeo Geo pi).Angle A B C) =
      Geo.Angle A.1 B.1 C.1 := by
  exact
    planeGeo_angle_to_ambient4_corrected
      (Geo := Geo)
      pi A B C

/--
PlaneGeo angle congruence implies ambient angle congruence.
-/
theorem planeGeo_angleCongruent_to_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C D E F : PlanePoint Geo pi)
    (h :
      (PlaneGeo Geo pi).AngleCongruent
        A B C D E F) :
    Geo.AngleCongruent
      A.1 B.1 C.1 D.1 E.1 F.1 := by

  unfold Geometry.Geo.AngleCongruent at h ⊢

  have hMap :
      forall
        {x y :
          PlanePoint Geo pi ×
            UnorderedPair (Set (PlanePoint Geo pi))},
        Relation.EqvGen
          (PlaneGeo Geo pi).UnorientedAngleCongruent
          x y ->
        Relation.EqvGen
          Geo.UnorientedAngleCongruent
          (planeGeoAngleToAmbient
            (Geo := Geo) x)
          (planeGeoAngleToAmbient
            (Geo := Geo) y) := by

    intro x y hxy

    induction hxy with

    | rel x y hxy =>
        exact
          (planeGeo_unorientedAngleCongruent_iff_ambient
            (Geo := Geo)
            pi x y).mp hxy

    | refl x =>
        exact
          Relation.EqvGen.refl
            (planeGeoAngleToAmbient
              (Geo := Geo) x)

    | symm x y _hxy ih =>
        exact
          Relation.EqvGen.symm
            (planeGeoAngleToAmbient
              (Geo := Geo) x)
            (planeGeoAngleToAmbient
              (Geo := Geo) y)
            ih

    | trans x y z _hxy _hyz ihxy ihyz =>
        exact
          Relation.EqvGen.trans
            (planeGeoAngleToAmbient
              (Geo := Geo) x)
            (planeGeoAngleToAmbient
              (Geo := Geo) y)
            (planeGeoAngleToAmbient
              (Geo := Geo) z)
            ihxy ihyz

  have hAmbientMapped :=
    hMap h

  rw [
    planeGeoAngleToAmbient_angle4_corrected
      (Geo := Geo) pi A B C,
    planeGeoAngleToAmbient_angle4_corrected
      (Geo := Geo) pi D E F
  ] at hAmbientMapped

  exact hAmbientMapped

/--
Ambient angle congruence between angles lying in pi implies PlaneGeo
angle congruence.
-/
theorem planeGeo_angleCongruent_of_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C D E F : PlanePoint Geo pi)
    (h :
      Geo.AngleCongruent
        A.1 B.1 C.1 D.1 E.1 F.1) :
    (PlaneGeo Geo pi).AngleCongruent
      A B C D E F := by

  unfold Geometry.Geo.AngleCongruent at h ⊢

  apply
    Relation.EqvGen.rel
      ((PlaneGeo Geo pi).Angle A B C)
      ((PlaneGeo Geo pi).Angle D E F)

  apply
    (planeGeo_unorientedAngleCongruent_iff_ambient
      (Geo := Geo)
      pi
      ((PlaneGeo Geo pi).Angle A B C)
      ((PlaneGeo Geo pi).Angle D E F)).mpr

  rw [
    planeGeoAngleToAmbient_angle4_corrected
      (Geo := Geo) pi A B C,
    planeGeoAngleToAmbient_angle4_corrected
      (Geo := Geo) pi D E F
  ]

  exact h

/--
For angles whose points lie in pi, PlaneGeo angle congruence and
ambient angle congruence are equivalent in corrected E4.
-/
theorem planeGeo_angleCongruent_iff_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C D E F : PlanePoint Geo pi) :
    (PlaneGeo Geo pi).AngleCongruent
        A B C D E F <->
      Geo.AngleCongruent
        A.1 B.1 C.1 D.1 E.1 F.1 := by

  constructor

  · exact
      planeGeo_angleCongruent_to_ambient4_corrected
        (Geo := Geo)
        pi A B C D E F

  · exact
      planeGeo_angleCongruent_of_ambient4_corrected
        (Geo := Geo)
        pi A B C D E F

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 marked 2-plane: full local Group III

Tests56-59 recovered, for a concrete nondegenerate ambient 2-plane pi,

  * planar Hilbert incidence and order;
  * same-ray transport;
  * segment congruence III.1-III.3;
  * angle congruence transport.

The corrected ambient E4 congruence class already states III.4
plane-locally and SAS ambiently.  Therefore the complete ordinary
planar HilbertCongruence API can now be recovered on PlaneGeo Geo pi
without installing any global HilbertCongruence Geo instance.
-/

/--
A concrete E4 2-plane marked by three explicit noncollinear points
inherits the complete planar Hilbert congruence structure.
-/
theorem planeGeoHilbertCongruence4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A0 B0 C0 : Geo.Point)
    (hA0pi : Q.toHilbertSpacePrimitive.OnPlane A0 pi)
    (hB0pi : Q.toHilbertSpacePrimitive.OnPlane B0 pi)
    (hC0pi : Q.toHilbertSpacePrimitive.OnPlane C0 pi)
    (hABC0 : Not (PrimCollinear Geo A0 B0 C0)) :
    HilbertCongruence (PlaneGeo Geo pi) := by

  let : HilbertOrder (PlaneGeo Geo pi) :=
    planeGeoHilbertOrder4_corrected
      (Geo := Geo)
      pi A0 B0 C0
      hA0pi hB0pi hC0pi hABC0

  refine
    {
      toHilbertOrder := inferInstance
      segment_construction := ?_
      segment_congruence_common := ?_
      segment_additivity := ?_
      angle_construction := ?_
      angle_congruence_reflexive := ?_
      sas := ?_
    }

  · intro A B O R hOR

    exact
      planeGeo_segment_construction4_corrected
        (Geo := Geo)
        pi A B O R hOR

  · intro A B A1 B1 A2 B2 h1 h2

    exact
      planeGeo_segment_congruence_common4_corrected
        (Geo := Geo)
        pi
        A B A1 B1 A2 B2
        h1 h2

  · intro A B C A1 B1 C1
      hABC hA1B1C1 hAB hBC

    exact
      planeGeo_segment_additivity4_corrected
        (Geo := Geo)
        pi
        A B C A1 B1 C1
        hABC hA1B1C1
        hAB hBC

  · intro A B C A1 B1 T
      hABC hA1B1
      l hA1l hB1l hTl

    have hABplane : Ne A B :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        A B C hABC

    have hAB : Ne A.1 B.1 := by
      intro h
      apply hABplane
      exact Subtype.ext h

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        pi A B C
        hAB hABC

    have hA1B1val : Ne A1.1 B1.1 := by
      intro h
      apply hA1B1
      exact Subtype.ext h

    rcases
        Hilbert4DAmbientCongruence.angle_construction_in_plane
          (Geo := Geo)
          A.1 B.1 C.1
          A1.1 B1.1 T.1
          hABCAmbient
          hA1B1val
          pi
          l.1
          l.2
          hA1l
          hB1l
          T.2
          hTl with
      ⟨C2,
       hSameSideAmbient,
       hAngleAmbient,
       hUniqueAmbient⟩

    have hC2pi :
        Q.toHilbertSpacePrimitive.OnPlane C2 pi :=
      hSameSideAmbient.1

    let C2p : PlanePoint Geo pi :=
      ⟨C2, hC2pi⟩

    have hSameSidePlane :
        HilbertSameSide
          (PlaneGeo Geo pi)
          C2p T l := by

      apply
        (planeGeo_sameSide_iff_space
          (Geo := Geo)
          pi C2p T l).mpr

      simpa [C2p] using hSameSideAmbient

    have hAnglePlane :
        (PlaneGeo Geo pi).AngleCongruent
          A B C A1 B1 C2p := by

      apply
        (planeGeo_angleCongruent_iff_ambient4_corrected
          (Geo := Geo)
          pi A B C A1 B1 C2p).mpr

      simpa [C2p] using hAngleAmbient

    refine
      ⟨C2p,
       hSameSidePlane,
       hAnglePlane,
       ?_⟩

    intro D
      hSameSideDPlane
      hAngleDPlane

    have hSameSideDAmbient :
        HilbertSameSideInPlane
          Geo D.1 T.1 l.1 pi :=
      (planeGeo_sameSide_iff_space
        (Geo := Geo)
        pi D T l).mp
        hSameSideDPlane

    have hAngleDAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A1.1 B1.1 D.1 :=
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        pi A B C A1 B1 D).mp
        hAngleDPlane

    have hSameRayAmbient :
        HilbertSameRay
          Geo B1.1 C2 D.1 :=
      hUniqueAmbient
        D.1
        hSameSideDAmbient
        hAngleDAmbient

    apply
      (planeGeo_sameRay_iff_ambient4_corrected
        (Geo := Geo)
        pi B1 C2p D).mpr

    simpa [C2p] using hSameRayAmbient

  · intro A B C hABC

    have hABplane : Ne A B :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        A B C hABC

    have hAB : Ne A.1 B.1 := by
      intro h
      apply hABplane
      exact Subtype.ext h

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        pi A B C
        hAB hABC

    have hAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A.1 B.1 C.1 :=
      Hilbert4DAmbientCongruence.angle_congruence_reflexive
        (Geo := Geo)
        A.1 B.1 C.1
        hABCAmbient

    exact
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        pi A B C A B C).mpr
        hAmbient

  · intro A B C A1 B1 C1
      hABC hA1B1C1
      hAB hAC hAngle

    have hABplane : Ne A B :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        A B C hABC

    have hABval : Ne A.1 B.1 := by
      intro h
      apply hABplane
      exact Subtype.ext h

    have hA1B1plane : Ne A1 B1 :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        A1 B1 C1 hA1B1C1

    have hA1B1val : Ne A1.1 B1.1 := by
      intro h
      apply hA1B1plane
      exact Subtype.ext h

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        pi A B C
        hABval hABC

    have hA1B1C1Ambient :
        Not (PrimCollinear Geo A1.1 B1.1 C1.1) :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        pi A1 B1 C1
        hA1B1val hA1B1C1

    have hABAmbient :
        Geo.Congruent
          A.1 B.1 A1.1 B1.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A B A1 B1).mp hAB

    have hACAmbient :
        Geo.Congruent
          A.1 C.1 A1.1 C1.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A C A1 C1).mp hAC

    have hAngleAmbient :
        Geo.AngleCongruent
          B.1 A.1 C.1
          B1.1 A1.1 C1.1 :=
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        pi B A C B1 A1 C1).mp
        hAngle

    have hResultAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A1.1 B1.1 C1.1 :=
      Hilbert4DAmbientCongruence.sas
        (Geo := Geo)
        A.1 B.1 C.1
        A1.1 B1.1 C1.1
        hABCAmbient
        hA1B1C1Ambient
        hABAmbient
        hACAmbient
        hAngleAmbient

    exact
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        pi A B C A1 B1 C1).mpr
        hResultAmbient

/--
Sanity check: a marked corrected E4 2-plane carries the complete
ordinary planar Group III structure.
-/
theorem hilbert4D_marked_plane_full_congruence_recovered
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A B C : Geo.Point)
    (hApi : Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hBpi : Q.toHilbertSpacePrimitive.OnPlane B pi)
    (hCpi : Q.toHilbertSpacePrimitive.OnPlane C pi)
    (hABC : Not (PrimCollinear Geo A B C)) :
    Nonempty (HilbertCongruence (PlaneGeo Geo pi)) := by

  exact
    ⟨planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi A B C
      hApi hBpi hCpi hABC⟩

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 marked 2-plane: corrected perpendicular bridge and uniqueness

This file closes the local planar kernel needed for same-foot normals in E4.

It provides corrected E4 replacements for the old 3D bridge lemmas:

  planeGeo_rightAngle_iff_ambient4_corrected
  planeGeo_linesPerpendicularAt_iff_ambient4_corrected

and then proves the neutral planar statement:

  two lines through O perpendicular to the same line n at O are equal.

The final uniqueness proof uses the production neutral theorem
`hilbert_XI4_two_right_angles_same_first_arm_collinear`.
-/

/--
Right-angle transport between a marked corrected E4 plane and ambient E4.
-/
theorem planeGeo_rightAngle_iff_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A O B : PlanePoint Geo pi) :
    HilbertRightAngle
        (PlaneGeo Geo pi) A O B <->
      HilbertRightAngle
        Geo A.1 O.1 B.1 := by

  constructor

  · rintro ⟨C, hAOC, hAnglePlane⟩

    have hAngleAmbient :
        Geo.AngleCongruent
          A.1 O.1 B.1
          B.1 O.1 C.1 :=
      (planeGeo_angleCongruent_iff_ambient4_corrected
        (Geo := Geo)
        pi A O B B O C).mp
        hAnglePlane

    exact
      ⟨C.1,
       hAOC,
       hAngleAmbient⟩

  · rintro ⟨C, hAOC, hAngleAmbient⟩

    have hData :=
      H4O.between_incidence
        A.1 O.1 C hAOC

    have hAO :
        Ne A.1 O.1 :=
      hData.1

    have hCol :
        PrimCollinear Geo A.1 O.1 C :=
      hData.2.2.2.1

    have hCpi :
        Q.toHilbertSpacePrimitive.OnPlane C pi :=
      hilbert4D_onPlane_of_primCollinear_with_two_on_plane_corrected
        (Geo := Geo)
        pi
        A.1 O.1 C
        hAO
        A.2 O.2
        hCol

    let Cp : PlanePoint Geo pi :=
      ⟨C, hCpi⟩

    have hAnglePlane :
        (PlaneGeo Geo pi).AngleCongruent
          A O B B O Cp := by

      apply
        (planeGeo_angleCongruent_iff_ambient4_corrected
          (Geo := Geo)
          pi A O B B O Cp).mpr

      simpa [Cp] using hAngleAmbient

    exact
      ⟨Cp,
       hAOC,
       hAnglePlane⟩

/--
Corrected E4 bridge for line-line perpendicularity inside one ambient
2-plane.
-/
theorem planeGeo_linesPerpendicularAt_iff_ambient4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (l m : PlaneLine Geo pi)
    (O : PlanePoint Geo pi) :
    HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) l m O <->
      HilbertLinesPerpendicularAt
        Geo l.1 m.1 O.1 := by

  unfold HilbertLinesPerpendicularAt

  constructor

  · rintro
      ⟨hOl, hOm,
       A, B,
       hAO, hBO,
       hAl, hBm,
       hNonPlane,
       hRightPlane⟩

    have hAOval :
        Ne A.1 O.1 := by
      intro h
      apply hAO
      exact Subtype.ext h

    have hBOval :
        Ne B.1 O.1 := by
      intro h
      apply hBO
      exact Subtype.ext h

    have hNonAmbient :
        Not (PrimCollinear Geo A.1 O.1 B.1) :=
      planeGeo_not_primCollinear_to_ambient4_corrected
        (Geo := Geo)
        pi A O B
        hAOval
        hNonPlane

    have hRightAmbient :
        HilbertRightAngle
          Geo A.1 O.1 B.1 :=
      (planeGeo_rightAngle_iff_ambient4_corrected
        (Geo := Geo)
        pi A O B).mp
        hRightPlane

    exact
      ⟨hOl,
       hOm,
       A.1, B.1,
       hAOval,
       hBOval,
       hAl,
       hBm,
       hNonAmbient,
       hRightAmbient⟩

  · rintro
      ⟨hOl, hOm,
       A, B,
       hAO, hBO,
       hAl, hBm,
       hNonAmbient,
       hRightAmbient⟩

    have hApi :
        Q.toHilbertSpacePrimitive.OnPlane A pi :=
      l.2 A hAl

    have hBpi :
        Q.toHilbertSpacePrimitive.OnPlane B pi :=
      m.2 B hBm

    let Ap : PlanePoint Geo pi :=
      ⟨A, hApi⟩

    let Bp : PlanePoint Geo pi :=
      ⟨B, hBpi⟩

    have hAOp :
        Ne Ap O := by
      intro h
      exact hAO (congrArg Subtype.val h)

    have hBOp :
        Ne Bp O := by
      intro h
      exact hBO (congrArg Subtype.val h)

    have hNonPlane :
        Not (PrimCollinear
          (PlaneGeo Geo pi) Ap O Bp) := by
      intro hCol
      apply hNonAmbient
      have hAmbient :=
        planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi Ap O Bp hCol
      simpa [Ap, Bp] using hAmbient

    have hRightPlane :
        HilbertRightAngle
          (PlaneGeo Geo pi) Ap O Bp := by

      apply
        (planeGeo_rightAngle_iff_ambient4_corrected
          (Geo := Geo)
          pi Ap O Bp).mpr

      simpa [Ap, Bp] using hRightAmbient

    exact
      ⟨hOl,
       hOm,
       Ap, Bp,
       hAOp,
       hBOp,
       hAl,
       hBm,
       hNonPlane,
       hRightPlane⟩

/--
Neutral symmetry of line-line perpendicularity.
No spatial incidence axiom is used.
-/
theorem hilbert_linesPerpendicularAt_symm_neutral
    [H : HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (l m : Geo.Line)
    (O : Geo.Point)
    (hPerp :
      HilbertLinesPerpendicularAt Geo l m O) :
    HilbertLinesPerpendicularAt Geo m l O := by

  rcases hPerp with
    ⟨hOl, hOm,
     A, B,
     hAO, hBO,
     hAl, hBm,
     hNon,
     hRight⟩

  have hNonSwap :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hNon
        (PrimCollinearSymm
          Geo B O A h)

  have hRightSwap :
      HilbertRightAngle Geo B O A :=
    hilbert_XI4_right_angle_swap
      Geo
      A O B
      hNon
      hRight

  exact
    ⟨hOm, hOl,
     B, A,
     hBO, hAO,
     hBm, hAl,
     hNonSwap,
     hRightSwap⟩

/--
Neutral uniqueness of a perpendicular line through a fixed point,
inside one marked corrected E4 2-plane.

If l and m pass through O and are both perpendicular at O to n,
then l=m.
-/
theorem planeGeo_perpendicular_same_foot_unique4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (A0 B0 C0 : Geo.Point)
    (hA0pi : Q.toHilbertSpacePrimitive.OnPlane A0 pi)
    (hB0pi : Q.toHilbertSpacePrimitive.OnPlane B0 pi)
    (hC0pi : Q.toHilbertSpacePrimitive.OnPlane C0 pi)
    (hABC0 : Not (PrimCollinear Geo A0 B0 C0))
    (l m n : PlaneLine Geo pi)
    (O : PlanePoint Geo pi)
    (hLperp :
      HilbertLinesPerpendicularAt
        Geo l.1 n.1 O.1)
    (hMperp :
      HilbertLinesPerpendicularAt
        Geo m.1 n.1 O.1) :
    l = m := by

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi A0 B0 C0
      hA0pi hB0pi hC0pi hABC0

  have hLperpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) l n O :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi l n O).mpr
      hLperp

  have hMperpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) m n O :=
    (planeGeo_linesPerpendicularAt_iff_ambient4_corrected
      (Geo := Geo)
      pi m n O).mpr
      hMperp

  have hNperpL :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) n l O :=
    hilbert_linesPerpendicularAt_symm_neutral
      (PlaneGeo Geo pi)
      l n O
      hLperpPlane

  have hNperpM :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) n m O :=
    hilbert_linesPerpendicularAt_symm_neutral
      (PlaneGeo Geo pi)
      m n O
      hMperpPlane

  have hnl : Ne n l :=
    hilbert_linesPerpendicularAt_ne
      (PlaneGeo Geo pi)
      n l O hNperpL

  have hnm : Ne n m :=
    hilbert_linesPerpendicularAt_ne
      (PlaneGeo Geo pi)
      n m O hNperpM

  have hNperpM_saved := hNperpM

  rcases hNperpL with
    ⟨hOn, hOl,
     F, A,
     hFO, hAO,
     hFn, hAl,
     hNonFOA,
     hRightFOA⟩

  rcases hNperpM with
    ⟨_hOn2, hOm,
     G, C,
     _hGO, hCO,
     _hGn, hCm,
     _hNonGOC,
     _hRightGOC⟩

  have hFOC :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo pi)
      n m
      O F C
      hnm
      hNperpM_saved
      hFO
      hCO
      hFn
      hCm

  have hAOC :
      PrimCollinear
        (PlaneGeo Geo pi)
        A O C :=
    hilbert_XI4_two_right_angles_same_first_arm_collinear
      (PlaneGeo Geo pi)
      F O A C
      n
      hFO
      hFn hOn
      hNonFOA hFOC.1
      hRightFOA hFOC.2

  have hCl :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := PlaneGeo Geo pi)
      hAO
      hAl hOl
      hAOC

  exact
    HilbertPlaneIncidence.line_unique
      (Geo := PlaneGeo Geo pi)
      O C hCO.symm
      l m
      hOl hCl
      hOm hCm

end Geometry

import CGJteamLab.Coxeter.E4Euclidean

/-!
# Corrected E4 normal core

Production promotion of the validated corrected E4 normal definitions,
plane-hyperplane incidence, and the basic same-foot two-normal
configuration.

This module imports no `AffineFlat4D_testNN` or `*_fixN` module.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hierarchy repair: first genuine normal layer

Test50 completed the corrected Hilbert package:

  genuine E4 ambient geometry
      ->
  full old E3 Hilbert geometry locally inside every hyperplane.

We now return to the genuinely four-dimensional part.

This file deliberately rebuilds only the dimension-safe part of the old
test24:

* normal line to a hyperplane;
* perpendicular foot relation;
* relational hyperplane reflection;
* existence of a point outside a hyperplane.

No old ambient `HilbertSpaceIncidence Geo`, `HilbertSpaceOrder Geo`,
`HilbertSpaceCongruence Geo`, or `HilbertSpaceEuclidean Geo` is assumed.

Important: the old test25 must NOT simply be copied next.  Its proof that
normals at distinct feet are parallel applied Euclid XI.6 directly in the
ambient `Geo`.  That application is genuinely 3-dimensional and is not
available in corrected E4.
-/

/--
A line is perpendicular to an E4 hyperplane at F when it is
perpendicular at F to every line of the hyperplane through F.
-/
def HilbertLinePerpendicularHyperplaneAt4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (l : Geo.Line)
    (Sigma : Q.Hyperplane)
    (F : Geo.Point) : Prop :=
  H.OnLine F l /\
  Q.OnHyperplane F Sigma /\
  forall m : Geo.Line,
    HilbertLineInHyperplane4 Geo m Sigma ->
    H.OnLine F m ->
    HilbertLinesPerpendicularAt Geo l m F

namespace HilbertLinePerpendicularHyperplaneAt4_corrected

theorem incidence
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {l : Geo.Line}
    {Sigma : Q.Hyperplane}
    {F : Geo.Point}
    (h :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F) :
    H.OnLine F l /\
    Q.OnHyperplane F Sigma := by

  exact
    ⟨h.1, h.2.1⟩

theorem perpendicular_to_line
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {l : Geo.Line}
    {Sigma : Q.Hyperplane}
    {F : Geo.Point}
    (h :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (m : Geo.Line)
    (hmSigma :
      HilbertLineInHyperplane4 Geo m Sigma)
    (hFm : H.OnLine F m) :
    HilbertLinesPerpendicularAt Geo l m F := by

  exact
    h.2.2 m hmSigma hFm

theorem perpendicular_to_hyperplaneLine
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {l : Geo.Line}
    {Sigma : Q.Hyperplane}
    {F : Geo.Point}
    (h :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (m : HyperplaneLine4 Geo Sigma)
    (hFm : H.OnLine F m.1) :
    HilbertLinesPerpendicularAt Geo l m.1 F := by

  exact
    h.2.2 m.1 m.2 hFm

/--
A normal line cannot itself lie in the mirror hyperplane.
-/
theorem not_line_in_hyperplane
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {l : Geo.Line}
    {Sigma : Q.Hyperplane}
    {F : Geo.Point}
    (h :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F) :
    Not (HilbertLineInHyperplane4 Geo l Sigma) := by

  intro hlSigma

  have hPerpSelf :
      HilbertLinesPerpendicularAt Geo l l F :=
    h.2.2 l hlSigma h.1

  have hll : Ne l l :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l l F hPerpSelf

  exact
    hll rfl

end HilbertLinePerpendicularHyperplaneAt4_corrected

/--
F is a perpendicular foot of P on Sigma when a hyperplane-normal line
through P meets Sigma at F.
-/
def PerpendicularToHyperplaneThrough4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (F P : Geo.Point) : Prop :=
  exists l : Geo.Line,
    H.OnLine P l /\
    HilbertLinePerpendicularHyperplaneAt4_corrected
      Geo l Sigma F

theorem perpendicularToHyperplaneThrough4_foot_on_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {Sigma : Q.Hyperplane}
    {F P : Geo.Point}
    (h :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P) :
    Q.OnHyperplane F Sigma := by

  rcases h with
    ⟨l, _hPl, hPerp⟩

  exact
    hPerp.2.1

/--
Relational reflection in an E4 hyperplane.
-/
def IsHyperplaneReflection4_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (P P' : Geo.Point) : Prop :=
  (Q.OnHyperplane P Sigma /\ P' = P) \/
  (Not (Q.OnHyperplane P Sigma) /\
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P /\
      HilbertIsMidpoint Geo F P P')

theorem hyperplaneReflection4_fixed_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (hPSigma : Q.OnHyperplane P Sigma) :
    IsHyperplaneReflection4_corrected
      Geo Sigma P P := by

  exact
    Or.inl ⟨hPSigma, rfl⟩

/--
Every E4 hyperplane has an external point, now derived from the corrected
ambient incidence class.
-/
theorem hilbert4D_point_off_hyperplane_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane) :
    exists P : Geo.Point,
      Not (Q.OnHyperplane P Sigma) := by

  rcases
      Hilbert4DAmbientIncidence.five_nonhyperplanar
        (Geo := Geo) with
    ⟨A, B, C, D, E, hNonhyperplanar⟩

  by_cases hA : Q.OnHyperplane A Sigma

  · by_cases hB : Q.OnHyperplane B Sigma

    · by_cases hC : Q.OnHyperplane C Sigma

      · by_cases hD : Q.OnHyperplane D Sigma

        · by_cases hE : Q.OnHyperplane E Sigma

          · exact
              False.elim
                (hNonhyperplanar
                  ⟨Sigma, hA, hB, hC, hD, hE⟩)

          · exact ⟨E, hE⟩

        · exact ⟨D, hD⟩

      · exact ⟨C, hC⟩

    · exact ⟨B, hB⟩

  · exact ⟨A, hA⟩

/--
Sanity: the genuine normal/reflection language needs no old ambient 3D
typeclass.
-/
example
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : Q.Hyperplane) :
    exists P : Geo.Point,
      Not (Q.OnHyperplane P Sigma) := by

  exact
    hilbert4D_point_off_hyperplane_corrected
      (Geo := Geo)
      Sigma

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 incidence: plane-hyperplane intersection

Test51 returned to the genuine E4 normal layer.

The first new incidence phenomenon needed for normal uniqueness is not
3D plane-plane incidence.  In E4 it is the dimension-correct statement:

  if a 2-plane and a 3-hyperplane have one common point,
  then they have a second distinct common point.

Equivalently, a nonempty plane-hyperplane intersection has dimension at
least one.

This is the E4 analogue of the old Hilbert I.7 role, but it must not be
installed as ambient `HilbertSpaceIncidence Geo`.

The class below is intentionally a small testbed interface.  We do not
yet claim that it is the final primitive formulation for arbitrary En.
-/

/--
Candidate E4 incidence clause: a 2-plane and a hyperplane sharing a
point share another distinct point.
-/
class Hilbert4DPlaneHyperplaneIncidence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo] : Prop where

  plane_hyperplane_second_common_point :
    forall pi : Q.toHilbertSpacePrimitive.Plane,
      forall Sigma : Q.Hyperplane,
        forall A : Geo.Point,
          Q.toHilbertSpacePrimitive.OnPlane A pi ->
          Q.OnHyperplane A Sigma ->
          exists B : Geo.Point,
            Ne B A /\
            Q.toHilbertSpacePrimitive.OnPlane B pi /\
            Q.OnHyperplane B Sigma

/--
A plane and a hyperplane with a common point contain a common line.
-/
theorem hilbert4D_plane_hyperplane_common_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (Sigma : Q.Hyperplane)
    (A : Geo.Point)
    (hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hASigma :
      Q.OnHyperplane A Sigma) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInHyperplane4 Geo l Sigma := by

  rcases
      Hilbert4DPlaneHyperplaneIncidence.plane_hyperplane_second_common_point
        (Geo := Geo)
        pi Sigma A
        hApi hASigma with
    ⟨B, hBA, hBpi, hBSigma⟩

  have hAB : Ne A B :=
    hBA.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨l, hAl, hBl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    Hilbert4DAmbientIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      pi hApi hBpi

  have hlSigma :
      HilbertLineInHyperplane4 Geo l Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      Sigma hASigma hBSigma

  exact
    ⟨l, hAl, hlpi, hlSigma⟩

/--
If the plane is not contained in the hyperplane, their common line is
the exact intersection.

This is the dimension-correct E4 replacement for the old ambient
3D theorem `hilbert_plane_intersection_line`.
-/
theorem hilbert4D_plane_hyperplane_intersection_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (Sigma : Q.Hyperplane)
    (hNotContained :
      Not (HilbertPlaneInHyperplane4 Geo pi Sigma))
    (A : Geo.Point)
    (hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi)
    (hASigma :
      Q.OnHyperplane A Sigma) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInHyperplane4 Geo l Sigma /\
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X pi /\
         Q.OnHyperplane X Sigma) <->
        H.OnLine X l := by

  rcases
      Hilbert4DPlaneHyperplaneIncidence.plane_hyperplane_second_common_point
        (Geo := Geo)
        pi Sigma A
        hApi hASigma with
    ⟨B, hBA, hBpi, hBSigma⟩

  have hAB : Ne A B :=
    hBA.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨l, hAl, hBl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    Hilbert4DAmbientIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      pi hApi hBpi

  have hlSigma :
      HilbertLineInHyperplane4 Geo l Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      Sigma hASigma hBSigma

  refine
    ⟨l, hAl, hlpi, hlSigma, ?_⟩

  intro X

  constructor

  · rintro ⟨hXpi, hXSigma⟩

    by_contra hXl

    have hABX :
        Not (PrimCollinear Geo A B X) := by

      intro hCol

      exact
        hXl
          (hilbert_on_line_of_primCollinear_with_two_on_line
            (Geo := Geo)
            hAB
            hAl hBl
            hCol)

    have hPiInSigma :
        HilbertPlaneInHyperplane4
          Geo pi Sigma :=
      Hilbert4DHyperplaneLocal3DIncidence.plane_in_hyperplane
        (Geo := Geo)
        A B X
        hABX
        pi
        hApi hBpi hXpi
        Sigma
        hASigma hBSigma hXSigma

    exact
      hNotContained hPiInSigma

  · intro hXl

    exact
      ⟨hlpi X hXl,
       hlSigma X hXl⟩

/--
A normal line gives an immediate example of a plane not contained in
the mirror hyperplane: any ambient plane containing that normal line
cannot be contained in the mirror.
-/
theorem hilbert4D_plane_containing_normal_not_in_hyperplane
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {Sigma : Q.Hyperplane}
    {l : Geo.Line}
    {F : Geo.Point}
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (hlpi :
      HilbertLineInPlane Geo l pi) :
    Not (HilbertPlaneInHyperplane4 Geo pi Sigma) := by

  intro hPiSigma

  apply
    HilbertLinePerpendicularHyperplaneAt4_corrected.not_line_in_hyperplane
      (Geo := Geo)
      hNormal

  intro X hXl

  exact
    hPiSigma X (hlpi X hXl)

/--
Sanity check: under the one new E4 incidence clause, a plane containing
a normal line meets the mirror hyperplane in an exact line through the
normal foot.
-/
theorem hilbert4D_normal_plane_intersection_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    {Sigma : Q.Hyperplane}
    {l : Geo.Line}
    {F : Geo.Point}
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (hlpi :
      HilbertLineInPlane Geo l pi) :
    exists n : Geo.Line,
      H.OnLine F n /\
      HilbertLineInPlane Geo n pi /\
      HilbertLineInHyperplane4 Geo n Sigma /\
      forall X : Geo.Point,
        (Q.toHilbertSpacePrimitive.OnPlane X pi /\
         Q.OnHyperplane X Sigma) <->
        H.OnLine X n := by

  have hFpi :
      Q.toHilbertSpacePrimitive.OnPlane F pi :=
    hlpi F hNormal.1

  have hFSigma :
      Q.OnHyperplane F Sigma :=
    hNormal.2.1

  have hNotContained :
      Not (HilbertPlaneInHyperplane4 Geo pi Sigma) :=
    hilbert4D_plane_containing_normal_not_in_hyperplane
      (Geo := Geo)
      hNormal pi hlpi

  exact
    hilbert4D_plane_hyperplane_intersection_line
      (Geo := Geo)
      pi Sigma
      hNotContained
      F hFpi hFSigma

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normals: same-foot plane configuration

Test52 supplied the dimension-correct E4 plane-hyperplane intersection
theorem.

The next target is uniqueness of the normal line at a fixed foot.
We do not use the old ambient XI.13 proof, since that proof assumes
ambient 3D incidence.

Instead, assume two distinct normal lines l and m pass through the same
foot F.  The first step is purely incidence-theoretic:

* choose A on l, A != F;
* choose B on m, B != F;
* F,A,B are noncollinear, otherwise l = m by line uniqueness;
* hence F,A,B determine an ambient 2-plane pi containing both l and m;
* pi meets the mirror hyperplane Sigma in an exact line n through F;
* both l and m are perpendicular to n at F.

Thus the remaining contradiction is entirely planar inside pi:
two distinct lines of pi through F cannot both be perpendicular to n
at F.

No old ambient HilbertSpaceIncidence, HilbertSpaceOrder,
HilbertSpaceCongruence, or HilbertSpaceEuclidean instance is assumed.
-/

/--
Every ambient line has a point distinct from any prescribed point.
-/
theorem hilbert4D_other_point_on_line_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (l : Geo.Line)
    (F : Geo.Point) :
    exists A : Geo.Point,
      Ne A F /\
      H.OnLine A l := by

  rcases
      Hilbert4DAmbientIncidence.two_points_on_each_line
        (Geo := Geo)
        l with
    ⟨A, B, hAB, hAl, hBl⟩

  by_cases hAF : A = F

  · subst A
    exact
      ⟨B, hAB.symm, hBl⟩

  · exact
      ⟨A, hAF, hAl⟩

/--
If two distinct candidate normals pass through the same foot F, they
lie in one ambient 2-plane pi whose intersection with Sigma is a line n
through F.  Both candidate normals are perpendicular to n at F.

This is the dimension-correct configuration needed for normal
uniqueness in E4.
-/
theorem hilbert4D_two_normals_same_foot_plane_configuration_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    (Sigma : Q.Hyperplane)
    (l m : Geo.Line)
    (F : Geo.Point)
    (hLM : Ne l m)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma F) :
    exists pi : Q.toHilbertSpacePrimitive.Plane,
      exists n : Geo.Line,
        HilbertLineInPlane Geo l pi /\
        HilbertLineInPlane Geo m pi /\
        H.OnLine F n /\
        HilbertLineInPlane Geo n pi /\
        HilbertLineInHyperplane4 Geo n Sigma /\
        (forall X : Geo.Point,
          (Q.toHilbertSpacePrimitive.OnPlane X pi /\
           Q.OnHyperplane X Sigma) <->
          H.OnLine X n) /\
        HilbertLinesPerpendicularAt Geo l n F /\
        HilbertLinesPerpendicularAt Geo m n F := by

  rcases
      hilbert4D_other_point_on_line_corrected
        (Geo := Geo)
        l F with
    ⟨A, hAF, hAl⟩

  rcases
      hilbert4D_other_point_on_line_corrected
        (Geo := Geo)
        m F with
    ⟨B, hBF, hBm⟩

  have hFA : Ne F A :=
    hAF.symm

  have hFB : Ne F B :=
    hBF.symm

  have hFAB :
      Not (PrimCollinear Geo F A B) := by

    intro hCol

    have hBl :
        H.OnLine B l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hFA
        hLNormal.1
        hAl
        hCol

    have hEq :
        l = m :=
      HilbertPlaneIncidence.line_unique
        F B hFB
        l m
        hLNormal.1 hBl
        hMNormal.1 hBm

    exact
      hLM hEq

  rcases
      Hilbert4DAmbientIncidence.plane_through
        (Geo := Geo)
        F A B hFAB with
    ⟨pi, hFpi, hApi, hBpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    Hilbert4DAmbientIncidence.line_in_plane
      (Geo := Geo)
      F A hFA
      l
      hLNormal.1 hAl
      pi
      hFpi hApi

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    Hilbert4DAmbientIncidence.line_in_plane
      (Geo := Geo)
      F B hFB
      m
      hMNormal.1 hBm
      pi
      hFpi hBpi

  rcases
      hilbert4D_normal_plane_intersection_line
        (Geo := Geo)
        hLNormal
        pi hlpi with
    ⟨n, hFn, hnpi, hnSigma, hExact⟩

  have hLperpN :
      HilbertLinesPerpendicularAt Geo l n F :=
    hLNormal.2.2
      n hnSigma hFn

  have hMperpN :
      HilbertLinesPerpendicularAt Geo m n F :=
    hMNormal.2.2
      n hnSigma hFn

  exact
    ⟨pi, n,
     hlpi,
     hmpi,
     hFn,
     hnpi,
     hnSigma,
     hExact,
     hLperpN,
     hMperpN⟩

end Geometry

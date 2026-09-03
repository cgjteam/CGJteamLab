import CGJteamLab.Coxeter.CoxeterRelations3D
import CGJteamLab.Proposition11_4
import CGJteamLab.HilbertRightAngle
import CGJteamLab.Proposition07
import CGJteamLab.Proposition11_8
import CGJteamLab.Proposition11_12
import CGJteamLab.Proposition46


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 in 3D: from a regular tetrahedron to the mirror frame

This file isolates the remaining geometric issue behind the existence of
`CoxeterA3TetrahedralFrame`.

The main theorem proves:

    regular tetrahedron -> CoxeterA3TetrahedralFrame.

No coordinates are used.  For each edge AB:

* take its midpoint F;
* the two opposite vertices C,D are equidistant from A,B;
* therefore FC and FD are perpendicular to AB;
* the lines FC and FD determine a plane;
* Euclid XI.4 implies that AB is perpendicular to that plane at F.

Thus the plane through F,C,D is the perpendicular-bisector mirror of AB.
The same construction is repeated for BC and CD.
-/


/--
A synthetic regular tetrahedron in Hilbert 3-space.

All five remaining edges are congruent to the reference edge AB, and
the four vertices are genuinely noncoplanar.
-/
structure HilbertRegularTetrahedron3D
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] where

  A : Geo.Point
  B : Geo.Point
  C : Geo.Point
  D : Geo.Point

  noncoplanar :
    Not (HilbertCoplanar4 Geo A B C D)

  AC_eq_AB :
    Geo.Congruent A C A B

  AD_eq_AB :
    Geo.Congruent A D A B

  BC_eq_AB :
    Geo.Congruent B C A B

  BD_eq_AB :
    Geo.Congruent B D A B

  CD_eq_AB :
    Geo.Congruent C D A B


/--
If F is the midpoint of AB and A,B,C,D are noncoplanar, then F,C,D
are noncollinear.

Otherwise the plane through A,B,C would also contain F and the whole
line FC, hence D, contradicting noncoplanarity.
-/
theorem hilbert_noncoplanar4_midpoint_opposite_noncollinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (A B C D F : Geo.Point)
    (hNoncoplanar :
      Not (HilbertCoplanar4 Geo A B C D))
    (hMid :
      HilbertIsMidpoint Geo F A B) :
    Not (PrimCollinear Geo F C D) := by

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      A B C D
      hNoncoplanar

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨l, hAl, hBl⟩

  have hAFB :
      PrimCollinear Geo A F B :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A F B hMid.1).2.2.2.1

  have hABF :
      PrimCollinear Geo A B F :=
    PrimCollinearRotate
      Geo A F B hAFB

  have hFl :
      H.OnLine F l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAB
      hAl hBl
      hABF

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B C hABC with
    ⟨pi, hApi, hBpi, hCpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      pi hApi hBpi

  have hFpi :
      S.OnPlane F pi :=
    hlpi F hFl

  have hFC :
      Ne F C := by
    intro hFC
    apply hABC
    rw [← hFC]
    exact
      ⟨l, hAl, hBl, hFl⟩

  intro hFCD

  rcases hFCD with
    ⟨q, hFq, hCq, hDq⟩

  have hqpi :
      HilbertLineInPlane Geo q pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      F C hFC
      q hFq hCq
      pi hFpi hCpi

  have hDpi :
      S.OnPlane D pi :=
    hqpi D hDq

  exact
    hNoncoplanar
      ⟨pi, hApi, hBpi, hCpi, hDpi⟩


/--
Perpendicular-bisector plane through two equidistant anchor points.

Assume F is the midpoint of AB, C and D are each equidistant from A,B,
and A,B,C,D are noncoplanar.  Then there exists a plane through C,D
which is perpendicular to AB at F.  In particular it is a valid mirror
interchanging A and B.
-/
theorem hilbert_edge_mirror_plane_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D F : Geo.Point)
    (hNoncoplanar :
      Not (HilbertCoplanar4 Geo A B C D))
    (hMid :
      HilbertIsMidpoint Geo F A B)
    (hCA_CB :
      Geo.Congruent C A C B)
    (hDA_DB :
      Geo.Congruent D A D B) :
    exists pi : S.Plane,
      Not (S.OnPlane A pi) /\
      PerpendicularToPlaneThrough Geo pi F A /\
      S.OnPlane C pi /\
      S.OnPlane D pi := by

  have hMidData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A F B hMid.1

  have hAB :
      Ne A B :=
    hMidData.2.2.1

  have hAF :
      Ne A F :=
    hMidData.1

  have hFCD :
      Not (PrimCollinear Geo F C D) :=
    hilbert_noncoplanar4_midpoint_opposite_noncollinear
      (Geo := Geo)
      A B C D F
      hNoncoplanar
      hMid

  have hFC :
      Ne F C :=
    hilbert_noncollinear_ne_first
      Geo F C D hFCD

  have hFDC :
      Not (PrimCollinear Geo F D C) := by
    intro h
    exact
      hFCD
        (PrimCollinearRotate
          Geo F D C h)

  have hFD :
      Ne F D :=
    hilbert_noncollinear_ne_first
      Geo F D C hFDC

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨l, hAl, hBl⟩

  rcases
      hilbert_space_equidistant_perpendicular_to_fixed_line
        (Geo := Geo)
        A B F C
        l hAl hBl
        hMid
        hCA_CB
        hFC.symm with
    ⟨mC, hFmC, hCmC, hPerpC⟩

  rcases
      hilbert_space_equidistant_perpendicular_to_fixed_line
        (Geo := Geo)
        A B F D
        l hAl hBl
        hMid
        hDA_DB
        hFD.symm with
    ⟨mD, hFmD, hDmD, hPerpD⟩

  have hmCD :
      Ne mC mD := by
    intro hEq
    apply hFCD
    exact
      ⟨mC,
       hFmC,
       hCmC,
       by
         rw [hEq]
         exact hDmD⟩

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        mC mD hmCD
        F hFmC hFmD with
    ⟨pi, hmCpi, hmDpi, _hUniquePi⟩

  let mCp : PlaneLine Geo pi :=
    ⟨mC, hmCpi⟩

  let mDp : PlaneLine Geo pi :=
    ⟨mD, hmDpi⟩

  have hFpi :
      S.OnPlane F pi :=
    hmCpi F hFmC

  let Fp : PlanePoint Geo pi :=
    ⟨F, hFpi⟩

  have hmCp_mDp :
      Ne mCp mDp := by
    intro hEq
    apply hmCD
    exact congrArg Subtype.val hEq

  have hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi F :=
    euclid_proposition_11_4
      (Geo := Geo)
      pi
      mCp mDp
      l
      Fp
      hmCp_mDp
      hPerpC
      hPerpD

  have hAoff :
      Not (S.OnPlane A pi) := by
    intro hApi

    have hAF_eq :
        A = F :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        pi l F A
        hLperp
        hAl
        hApi

    exact hAF hAF_eq

  have hPerpThrough :
      PerpendicularToPlaneThrough Geo pi F A :=
    ⟨l, hAl, hLperp⟩

  exact
    ⟨pi,
     hAoff,
     hPerpThrough,
     hmCpi C hCmC,
     hmDpi D hDmD⟩


namespace HilbertRegularTetrahedron3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]


/--
In a regular tetrahedron, C is equidistant from A and B.
-/
theorem C_equidistant_AB
    (T : HilbertRegularTetrahedron3D Geo) :
    Geo.Congruent T.C T.A T.C T.B := by

  have hCA_AB :
      Geo.Congruent T.C T.A T.A T.B :=
    CongruentReverseFirst
      Geo T.A T.C T.A T.B
      T.AC_eq_AB

  have hCB_AB :
      Geo.Congruent T.C T.B T.A T.B :=
    CongruentReverseFirst
      Geo T.B T.C T.A T.B
      T.BC_eq_AB

  have hAB_CB :
      Geo.Congruent T.A T.B T.C T.B :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      T.C T.B T.A T.B
      hCB_AB

  exact
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      T.C T.A
      T.A T.B
      T.C T.B
      hCA_AB
      hAB_CB


/--
In a regular tetrahedron, D is equidistant from A and B.
-/
theorem D_equidistant_AB
    (T : HilbertRegularTetrahedron3D Geo) :
    Geo.Congruent T.D T.A T.D T.B := by

  have hDA_AB :
      Geo.Congruent T.D T.A T.A T.B :=
    CongruentReverseFirst
      Geo T.A T.D T.A T.B
      T.AD_eq_AB

  have hDB_AB :
      Geo.Congruent T.D T.B T.A T.B :=
    CongruentReverseFirst
      Geo T.B T.D T.A T.B
      T.BD_eq_AB

  have hAB_DB :
      Geo.Congruent T.A T.B T.D T.B :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      T.D T.B T.A T.B
      hDB_AB

  exact
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      T.D T.A
      T.A T.B
      T.D T.B
      hDA_AB
      hAB_DB


/--
In a regular tetrahedron, A is equidistant from B and C.
-/
theorem A_equidistant_BC
    (T : HilbertRegularTetrahedron3D Geo) :
    Geo.Congruent T.A T.B T.A T.C := by

  exact
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      T.A T.C T.A T.B
      T.AC_eq_AB


/--
In a regular tetrahedron, D is equidistant from B and C.
-/
theorem D_equidistant_BC
    (T : HilbertRegularTetrahedron3D Geo) :
    Geo.Congruent T.D T.B T.D T.C := by

  have hDB_AB :
      Geo.Congruent T.D T.B T.A T.B :=
    CongruentReverseFirst
      Geo T.B T.D T.A T.B
      T.BD_eq_AB

  have hDC_AB :
      Geo.Congruent T.D T.C T.A T.B :=
    CongruentReverseFirst
      Geo T.C T.D T.A T.B
      T.CD_eq_AB

  have hAB_DC :
      Geo.Congruent T.A T.B T.D T.C :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      T.D T.C T.A T.B
      hDC_AB

  exact
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      T.D T.B
      T.A T.B
      T.D T.C
      hDB_AB
      hAB_DC


/--
In a regular tetrahedron, A is equidistant from C and D.
-/
theorem A_equidistant_CD
    (T : HilbertRegularTetrahedron3D Geo) :
    Geo.Congruent T.A T.C T.A T.D := by

  have hAB_AD :
      Geo.Congruent T.A T.B T.A T.D :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      T.A T.D T.A T.B
      T.AD_eq_AB

  exact
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      T.A T.C
      T.A T.B
      T.A T.D
      T.AC_eq_AB
      hAB_AD


/--
In a regular tetrahedron, B is equidistant from C and D.
-/
theorem B_equidistant_CD
    (T : HilbertRegularTetrahedron3D Geo) :
    Geo.Congruent T.B T.C T.B T.D := by

  have hAB_BD :
      Geo.Congruent T.A T.B T.B T.D :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      T.B T.D T.A T.B
      T.BD_eq_AB

  exact
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      T.B T.C
      T.A T.B
      T.B T.D
      T.BC_eq_AB
      hAB_BD


/--
Every regular tetrahedron canonically supplies the three mirror planes
needed by the synthetic Coxeter A3 development.

This is a noncomputable definition because the current geometric API states
midpoint and mirror-plane existence propositionally.  `Classical.choose`
extracts canonical witnesses for the Coxeter frame; no new geometric axiom
is introduced.
-/
noncomputable def toCoxeterA3TetrahedralFrame
    (T : HilbertRegularTetrahedron3D Geo) :
    CoxeterA3TetrahedralFrame Geo := by

  classical

  have hABC :
      Not (PrimCollinear Geo T.A T.B T.C) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.A T.B T.C T.D
      T.noncoplanar

  have hAB :
      Ne T.A T.B :=
    hilbert_noncollinear_ne_first
      Geo T.A T.B T.C hABC

  have hBCA :
      Not (PrimCollinear Geo T.B T.C T.A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo T.C T.A T.B
          (PrimCollinearCycle
            Geo T.B T.C T.A h))

  have hBC :
      Ne T.B T.C :=
    hilbert_noncollinear_ne_first
      Geo T.B T.C T.A hBCA

  have hNonCDAB :
      Not (HilbertCoplanar4
        Geo T.C T.D T.A T.B) := by
    intro h
    rcases h with
      ⟨pi, hCpi, hDpi, hApi, hBpi⟩
    exact
      T.noncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hCDA :
      Not (PrimCollinear Geo T.C T.D T.A) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      T.C T.D T.A T.B
      hNonCDAB

  have hCD :
      Ne T.C T.D :=
    hilbert_noncollinear_ne_first
      Geo T.C T.D T.A hCDA

  have hMid1Exists :
      exists F1 : Geo.Point,
        HilbertIsMidpoint Geo F1 T.A T.B :=
    hilbert_space_midpoint_exists
      (Geo := Geo)
      T.A T.B hAB

  let F1 : Geo.Point :=
    Classical.choose hMid1Exists

  have hMid1 :
      HilbertIsMidpoint Geo F1 T.A T.B :=
    Classical.choose_spec hMid1Exists

  have hMid2Exists :
      exists F2 : Geo.Point,
        HilbertIsMidpoint Geo F2 T.B T.C :=
    hilbert_space_midpoint_exists
      (Geo := Geo)
      T.B T.C hBC

  let F2 : Geo.Point :=
    Classical.choose hMid2Exists

  have hMid2 :
      HilbertIsMidpoint Geo F2 T.B T.C :=
    Classical.choose_spec hMid2Exists

  have hMid3Exists :
      exists F3 : Geo.Point,
        HilbertIsMidpoint Geo F3 T.C T.D :=
    hilbert_space_midpoint_exists
      (Geo := Geo)
      T.C T.D hCD

  let F3 : Geo.Point :=
    Classical.choose hMid3Exists

  have hMid3 :
      HilbertIsMidpoint Geo F3 T.C T.D :=
    Classical.choose_spec hMid3Exists

  have hC_AB :
      Geo.Congruent T.C T.A T.C T.B :=
    C_equidistant_AB
      (Geo := Geo) T

  have hD_AB :
      Geo.Congruent T.D T.A T.D T.B :=
    D_equidistant_AB
      (Geo := Geo) T

  have hMirror1Exists :
      exists pi1 : S.Plane,
        Not (S.OnPlane T.A pi1) /\
        PerpendicularToPlaneThrough Geo pi1 F1 T.A /\
        S.OnPlane T.C pi1 /\
        S.OnPlane T.D pi1 :=
    hilbert_edge_mirror_plane_exists
      (Geo := Geo)
      T.A T.B T.C T.D F1
      T.noncoplanar
      hMid1
      hC_AB
      hD_AB

  let pi1 : S.Plane :=
    Classical.choose hMirror1Exists

  have hMirror1 :=
    Classical.choose_spec hMirror1Exists

  have hNonBCAD :
      Not (HilbertCoplanar4
        Geo T.B T.C T.A T.D) := by
    intro h
    rcases h with
      ⟨pi, hBpi, hCpi, hApi, hDpi⟩
    exact
      T.noncoplanar
        ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  have hA_BC :
      Geo.Congruent T.A T.B T.A T.C :=
    A_equidistant_BC
      (Geo := Geo) T

  have hD_BC :
      Geo.Congruent T.D T.B T.D T.C :=
    D_equidistant_BC
      (Geo := Geo) T

  have hMirror2Exists :
      exists pi2 : S.Plane,
        Not (S.OnPlane T.B pi2) /\
        PerpendicularToPlaneThrough Geo pi2 F2 T.B /\
        S.OnPlane T.A pi2 /\
        S.OnPlane T.D pi2 :=
    hilbert_edge_mirror_plane_exists
      (Geo := Geo)
      T.B T.C T.A T.D F2
      hNonBCAD
      hMid2
      hA_BC
      hD_BC

  let pi2 : S.Plane :=
    Classical.choose hMirror2Exists

  have hMirror2 :=
    Classical.choose_spec hMirror2Exists

  have hA_CD :
      Geo.Congruent T.A T.C T.A T.D :=
    A_equidistant_CD
      (Geo := Geo) T

  have hB_CD :
      Geo.Congruent T.B T.C T.B T.D :=
    B_equidistant_CD
      (Geo := Geo) T

  have hMirror3Exists :
      exists pi3 : S.Plane,
        Not (S.OnPlane T.C pi3) /\
        PerpendicularToPlaneThrough Geo pi3 F3 T.C /\
        S.OnPlane T.A pi3 /\
        S.OnPlane T.B pi3 :=
    hilbert_edge_mirror_plane_exists
      (Geo := Geo)
      T.C T.D T.A T.B F3
      hNonCDAB
      hMid3
      hA_CD
      hB_CD

  let pi3 : S.Plane :=
    Classical.choose hMirror3Exists

  have hMirror3 :=
    Classical.choose_spec hMirror3Exists

  exact
    {
      A := T.A
      B := T.B
      C := T.C
      D := T.D

      noncoplanar := T.noncoplanar

      pi1 := pi1
      F1 := F1
      A_off_pi1 := hMirror1.1
      AB_perp_pi1 := hMirror1.2.1
      F1_mid_AB := hMid1
      C_on_pi1 := hMirror1.2.2.1
      D_on_pi1 := hMirror1.2.2.2

      pi2 := pi2
      F2 := F2
      B_off_pi2 := hMirror2.1
      BC_perp_pi2 := hMirror2.2.1
      F2_mid_BC := hMid2
      A_on_pi2 := hMirror2.2.2.1
      D_on_pi2 := hMirror2.2.2.2

      pi3 := pi3
      F3 := F3
      C_off_pi3 := hMirror3.1
      CD_perp_pi3 := hMirror3.2.1
      F3_mid_CD := hMid3
      A_on_pi3 := hMirror3.2.2.1
      B_on_pi3 := hMirror3.2.2.2
    }


end HilbertRegularTetrahedron3D

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

A small ambient SAS convenience lemma.

The spatial congruence axiom III.5 compares triangles in different
planes, but its primitive conclusion is an angle congruence.  The
3D interface already contains the third-side form when the target
triangle is presented inside an explicit `PlaneGeo`.

Here we remove that technical target-plane argument: the plane through
the second noncollinear triangle is constructed automatically.
-/


/--
Ambient third-side form of spatial SAS.

Two nondegenerate ambient triangles with two corresponding sides and
the included angle congruent have congruent third sides.

The two triangles may lie in different planes.
-/
theorem hilbert_space_sas_third_side
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C A' B' C' : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear Geo A' B' C'))
    (hAB :
      Geo.Congruent A B A' B')
    (hAC :
      Geo.Congruent A C A' C')
    (hAngle :
      Geo.AngleCongruent B A C B' A' C') :
    Geo.Congruent B C B' C' := by

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A' B' C'
        hA'B'C' with
    ⟨sigma, hA'sigma, hB'sigma, hC'sigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨A', hA'sigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B', hB'sigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨C', hC'sigma⟩

  have hPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Cp) := by
    intro hCol
    have hAmbient :
        PrimCollinear Geo A' B' C' :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma
        Ap Bp Cp
        hCol
    exact hA'B'C' hAmbient

  have hResult :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      A B C
      Ap Bp Cp
      hABC
      hPlane
      hAB
      hAC
      hAngle

  simpa [Ap, Bp, Cp] using hResult.1


end Geometry


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Right-angle comparison inside one ambient plane.

The ambient 3D geometry deliberately has no global
`HilbertCongruence Geo` instance. Therefore Hilbert Theorem 21 must
not be applied directly to the ambient space.

When both angles lie in one explicit plane `pi`, however, `PlaneGeo`
carries the full planar Hilbert structure. We apply planar Hilbert 21
there and transport the conclusion back to the ambient geometry.
-/


/--
Two ambient right angles contained in the same explicit plane are
ambiently congruent.

This is the plane-slice form of Hilbert Theorem 21.
-/
theorem hilbert_space_coplanar_right_angles_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A O B A' O' B' : PlanePoint Geo pi)
    (hAOB :
      Not (PrimCollinear Geo A.1 O.1 B.1))
    (hA'OB' :
      Not (PrimCollinear Geo A'.1 O'.1 B'.1))
    (hRight :
      HilbertRightAngle Geo A.1 O.1 B.1)
    (hRight' :
      HilbertRightAngle Geo A'.1 O'.1 B'.1) :
    Geo.AngleCongruent
      A.1 O.1 B.1
      A'.1 O'.1 B'.1 := by

  have hAOBPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi) A O B) := by
    intro hCol
    exact hAOB
      (planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi A O B hCol)

  have hA'OB'Plane :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi) A' O' B') := by
    intro hCol
    exact hA'OB'
      (planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi A' O' B' hCol)

  have hRightPlane :
      HilbertRightAngle
        (PlaneGeo Geo pi) A O B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      pi A O B).mpr hRight

  have hRightPlane' :
      HilbertRightAngle
        (PlaneGeo Geo pi) A' O' B' :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      pi A' O' B').mpr hRight'

  have hAnglePlane :
      (PlaneGeo Geo pi).AngleCongruent
        A O B A' O' B' :=
    hilbert_all_right_angles_congruent
      (PlaneGeo Geo pi)
      A O B
      A' O' B'
      hAOBPlane
      hA'OB'Plane
      hRightPlane
      hRightPlane'

  exact
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      pi
      A O B
      A' O' B').mp
      hAnglePlane


/--
Coplanar right-triangle hypotenuse comparison.

If two nondegenerate right triangles lie in the same ambient plane,
their corresponding legs are congruent, and the right angles are at
the first vertices, then their hypotenuses are congruent.
-/
theorem hilbert_space_coplanar_right_triangles_hypotenuse
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C A' B' C' : PlanePoint Geo pi)
    (hABC :
      Not (PrimCollinear Geo A.1 B.1 C.1))
    (hA'B'C' :
      Not (PrimCollinear Geo A'.1 B'.1 C'.1))
    (hRight :
      HilbertRightAngle Geo B.1 A.1 C.1)
    (hRight' :
      HilbertRightAngle Geo B'.1 A'.1 C'.1)
    (hAB :
      Geo.Congruent A.1 B.1 A'.1 B'.1)
    (hAC :
      Geo.Congruent A.1 C.1 A'.1 C'.1) :
    Geo.Congruent B.1 C.1 B'.1 C'.1 := by

  have hAngle :
      Geo.AngleCongruent
        B.1 A.1 C.1
        B'.1 A'.1 C'.1 :=
    hilbert_space_coplanar_right_angles_congruent
      (Geo := Geo)
      pi
      B A C
      B' A' C'
      (by
        intro h
        exact hABC
          (PrimCollinearSwap
            Geo B.1 A.1 C.1 h))
      (by
        intro h
        exact hA'B'C'
          (PrimCollinearSwap
            Geo B'.1 A'.1 C'.1 h))
      hRight
      hRight'

  exact
    hilbert_space_sas_third_side
      (Geo := Geo)
      A.1 B.1 C.1
      A'.1 B'.1 C'.1
      hABC
      hA'B'C'
      hAB
      hAC
      hAngle


end Geometry


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Ambient ray/order bridges needed for the spatial version of
Hilbert Theorem 14.

The key architectural point is that no global planar `HilbertOrder Geo`
is installed on the ambient 3-space.  Whenever a planar order theorem is
needed, the relevant ambient line is placed inside an explicit plane and
the theorem is applied in `PlaneGeo`.
-/


/--
Ambient same-ray consequence of strict betweenness.

This uses only spatial Hilbert II.1 and II.3.
-/
theorem hilbert_space_sameRay_of_between
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O P Q : Geo.Point)
    (hOPQ : Geo.Between O P Q) :
    HilbertSameRay Geo O P Q := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      O P Q hOPQ

  exact
    ⟨hData.1.symm,
     hData.2.2.1.symm,
     hData.2.2.2.1,
     (HilbertSpaceOrder.between_unique
       (Geo := Geo)
       O P Q
       hData.2.2.2.1
       hOPQ).1⟩


/--
Ambient rays determined by two representatives of the same Hilbert ray
are extensionally equal.

The proof puts their common carrier line into one explicit ambient
plane and invokes the already established planar theorem in `PlaneGeo`.
-/
theorem hilbert_space_sameRay_ray_eq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O P Q : Geo.Point)
    (hRay : HilbertSameRay Geo O P Q) :
    Geo.ray O P = Geo.ray O Q := by

  rcases hRay.2.2.1 with
    ⟨l, hOl, hPl, hQl⟩

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨R, hRl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l R hRl with
    ⟨pi, hlpi, _hRpi, _hUniquePi⟩

  let Op : PlanePoint Geo pi :=
    ⟨O, hlpi O hOl⟩

  let Pp : PlanePoint Geo pi :=
    ⟨P, hlpi P hPl⟩

  let Qp : PlanePoint Geo pi :=
    ⟨Q, hlpi Q hQl⟩

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Pp Qp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Pp Qp).mpr
    simpa [Op, Pp, Qp] using hRay

  have hEqPlane :
      (PlaneGeo Geo pi).ray Op Pp =
      (PlaneGeo Geo pi).ray Op Qp :=
    hilbert_sameRay_ray_eq
      (PlaneGeo Geo pi)
      Op Pp Qp
      hRayPlane

  have hEqMapped :
      planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Pp) =
      planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Qp) :=
    congrArg
      (fun X : Set (PlanePoint Geo pi) =>
        planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          X)
      hEqPlane

  calc
    Geo.ray O P =
        planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Pp) := by
      symm
      simpa [Op, Pp] using
        (planeGeo_ray_to_ambient
          (Geo := Geo)
          pi Op Pp)
    _ =
        planePointSetToAmbient
          (Geo := Geo)
          (pi := pi)
          ((PlaneGeo Geo pi).ray Op Qp) :=
      hEqMapped
    _ = Geo.ray O Q := by
      simpa [Op, Qp] using
        (planeGeo_ray_to_ambient
          (Geo := Geo)
          pi Op Qp)


/--
Changing the first arm of an ambient angle to another representative of
the same Hilbert ray does not change the angle object.
-/
theorem hilbert_space_angle_eq_of_sameRay_first
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O A A' B : Geo.Point)
    (hAA' : HilbertSameRay Geo O A A') :
    Geo.Angle A O B =
    Geo.Angle A' O B := by

  unfold Geometry.Geo.Angle
  rw [
    hilbert_space_sameRay_ray_eq
      (Geo := Geo)
      O A A' hAA'
  ]


/--
Changing the second arm of an ambient angle to another representative
of the same Hilbert ray does not change the angle object.
-/
theorem hilbert_space_angle_eq_of_sameRay_second
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (O A B B' : Geo.Point)
    (hBB' : HilbertSameRay Geo O B B') :
    Geo.Angle A O B =
    Geo.Angle A O B' := by

  unfold Geometry.Geo.Angle
  rw [
    hilbert_space_sameRay_ray_eq
      (Geo := Geo)
      O B B' hBB'
  ]


/--
Ambient noncollinearity is preserved when both arms of an angle are
replaced by representatives of the same rays.

This is purely incidence-theoretic once the same-ray data are given.
-/
theorem hilbert_space_noncollinear_of_sameRays
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A O B X Y : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hAX : HilbertSameRay Geo O A X)
    (hBY : HilbertSameRay Geo O B Y) :
    Not (PrimCollinear Geo X O Y) := by

  intro hXOY

  have hAOX :
      PrimCollinear Geo A O X :=
    PrimCollinearRotate Geo A X O
      (PrimCollinearCycle
        Geo O A X hAX.2.2.1)

  have hOXY :
      PrimCollinear Geo O X Y :=
    PrimCollinearSwap
      Geo X O Y hXOY

  have hAOY :
      PrimCollinear Geo A O Y :=
    hilbert_primCollinear_trans
      Geo A O X Y
      hAX.2.1.symm
      hAOX hOXY

  have hOYB :
      PrimCollinear Geo O Y B :=
    PrimCollinearRotate
      Geo O B Y hBY.2.2.1

  exact
    hAOB
      (hilbert_primCollinear_trans
        Geo A O Y B
        hBY.2.1.symm
        hAOY hOYB)


/--
Ambient transport of strict betweenness along two Hilbert rays.

All five points lie on one ambient line.  That line is placed in an
explicit plane, the planar theorem is applied in `PlaneGeo`, and the
result is read back in the ambient geometry.
-/
theorem hilbert_space_between_transport_sameRays
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (A O C A' C' : Geo.Point)
    (hAOC : Geo.Between A O C)
    (hAA' : HilbertSameRay Geo O A A')
    (hCC' : HilbertSameRay Geo O C C') :
    Geo.Between A' O C' := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O C hAOC

  rcases hData.2.2.2.1 with
    ⟨l, hAl, hOl, hCl⟩

  have hA'l :
      H.OnLine A' l := by
    have hAOA' :
        PrimCollinear Geo A O A' :=
      PrimCollinearSwap
        Geo O A A'
        hAA'.2.2.1

    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hData.1
        hAl hOl
        hAOA'

  have hC'l :
      H.OnLine C' l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hData.2.1
      hOl hCl
      hCC'.2.2.1

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨R, hRl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        l R hRl with
    ⟨pi, hlpi, _hRpi, _hUniquePi⟩

  let Ap : PlanePoint Geo pi :=
    ⟨A, hlpi A hAl⟩

  let Op : PlanePoint Geo pi :=
    ⟨O, hlpi O hOl⟩

  let Cp : PlanePoint Geo pi :=
    ⟨C, hlpi C hCl⟩

  let A'p : PlanePoint Geo pi :=
    ⟨A', hlpi A' hA'l⟩

  let C'p : PlanePoint Geo pi :=
    ⟨C', hlpi C' hC'l⟩

  have hAOCPlane :
      (PlaneGeo Geo pi).Between
        Ap Op Cp := by
    apply
      (planeGeo_between
        (Geo := Geo)
        pi Ap Op Cp).mpr
    simpa [Ap, Op, Cp] using hAOC

  have hAA'Plane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Ap A'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Ap A'p).mpr
    simpa [Op, Ap, A'p] using hAA'

  have hCC'Plane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Op Cp C'p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Cp C'p).mpr
    simpa [Op, Cp, C'p] using hCC'

  have hResult :
      (PlaneGeo Geo pi).Between
        A'p Op C'p :=
    hilbert_between_transport_sameRays
      (PlaneGeo Geo pi)
      Ap Op Cp A'p C'p
      hAOCPlane
      hAA'Plane
      hCC'Plane

  have hResultAmbient :
      Geo.Between A' O C' :=
    (planeGeo_between
      (Geo := Geo)
      pi A'p Op C'p).mp
      hResult

  simpa [A'p, Op, C'p] using hResultAmbient


end Geometry


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Spatial Hilbert Theorem 14.

Angles adjacent to congruent angles are congruent, even when the two
linear pairs lie in different ambient planes.

The proof is the same synthetic Hilbert proof as in the planar library,
but all ambient order/ray operations use the explicit 3D bridges from
`test04`, and all triangle congruence steps use `HilbertSpaceCongruence`.
-/


/--
Spatial Hilbert Theorem 14.

If `A-O-C` and `A'-O'-C'` are two linear pairs and

    angle AOB ~= angle A'O'B',

then the adjacent angles satisfy

    angle BOC ~= angle B'O'C'.

The two configurations may lie in different planes.
-/
theorem hilbert_space_adjacent_angles_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A O B C A' O' B' C' : Geo.Point)
    (hAOC : Geo.Between A O C)
    (hA'O'C' : Geo.Between A' O' C')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'O'B' : Not (PrimCollinear Geo A' O' B'))
    (hAngle :
      Geo.AngleCongruent A O B A' O' B') :
    Geo.AngleCongruent B O C B' O' C' := by

  have hAOCData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A O C hAOC

  have hA'O'C'Data :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A' O' C' hA'O'C'

  have hOA : O ≠ A :=
    hAOCData.1.symm

  have hOC : O ≠ C :=
    hAOCData.2.1

  have hOB : O ≠ B := by
    have hBOA :
        Not (PrimCollinear Geo B O A) := by
      intro h
      exact
        hAOB
          (PrimCollinearRotate
            Geo A B O
            (PrimCollinearCycle
              Geo O A B
              (PrimCollinearCycle
                Geo B O A h)))
    exact
      (hilbert_noncollinear_ne_first
        Geo B O A hBOA).symm

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' A'
        O A
        hOA with
    ⟨X, hAX, hOX⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' B'
        O B
        hOB with
    ⟨Y, hBY, hOY⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        O' C'
        O C
        hOC with
    ⟨Z, hCZ, hOZ⟩

  have hXOY :
      Not (PrimCollinear Geo X O Y) :=
    hilbert_space_noncollinear_of_sameRays
      (Geo := Geo)
      A O B X Y
      hAOB hAX hBY

  have hAngleLeft :
      Geo.Angle A O B =
      Geo.Angle X O Y := by
    calc
      Geo.Angle A O B =
          Geo.Angle X O B :=
        hilbert_space_angle_eq_of_sameRay_first
          (Geo := Geo)
          O A X B hAX
      _ =
          Geo.Angle X O Y :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          O X B Y hBY

  have hAngleXOY :
      Geo.AngleCongruent
        X O Y
        A' O' B' := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢
    rw [← hAngleLeft]
    exact hAngle

  have hFirstAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      O X Y
      O' A' B'
      (by
        intro h
        exact hXOY
          (PrimCollinearSwap
            Geo O X Y h))
      (by
        intro h
        exact hA'O'B'
          (PrimCollinearSwap
            Geo O' A' B' h))
      hOX
      hOY
      hAngleXOY

  have hFirstSide :
      Geo.Congruent X Y A' B' :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      O X Y
      O' A' B'
      (by
        intro h
        exact hXOY
          (PrimCollinearSwap
            Geo O X Y h))
      (by
        intro h
        exact hA'O'B'
          (PrimCollinearSwap
            Geo O' A' B' h))
      hOX
      hOY
      hAngleXOY

  have hXOZ :
      Geo.Between X O Z :=
    hilbert_space_between_transport_sameRays
      (Geo := Geo)
      A O C
      X Z
      hAOC
      hAX
      hCZ

  have hXO :
      Geo.Congruent X O A' O' :=
    (Geo.congruent_reverse_second
      X O O' A').mp
      ((Geo.congruent_reverse_first
        O X O' A').mp hOX)

  have hXZ :
      Geo.Congruent X Z A' C' :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      X O Z
      A' O' C'
      hXOZ
      hA'O'C'
      hXO
      hOZ

  have hRayXOZ :
      HilbertSameRay Geo X O Z :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      X O Z hXOZ

  have hRayA'O'C' :
      HilbertSameRay Geo A' O' C' :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      A' O' C' hA'O'C'

  have hAtXLeft :
      Geo.Angle O X Y =
      Geo.Angle Y X Z := by
    calc
      Geo.Angle O X Y =
          Geo.Angle Y X O :=
        Geo.angle_swap O X Y
      _ =
          Geo.Angle Y X Z :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          X Y O Z hRayXOZ

  have hAtXRight :
      Geo.Angle O' A' B' =
      Geo.Angle B' A' C' := by
    calc
      Geo.Angle O' A' B' =
          Geo.Angle B' A' O' :=
        Geo.angle_swap O' A' B'
      _ =
          Geo.Angle B' A' C' :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          A' B' O' C' hRayA'O'C'

  have hAngleXYZ :
      Geo.AngleCongruent
        Y X Z
        B' A' C' := by
    unfold Geometry.Geo.AngleCongruent
      at hFirstAngles ⊢
    rw [← hAtXLeft, ← hAtXRight]
    exact hFirstAngles.1

  have hXYZ :
      Not (PrimCollinear Geo X Y Z) := by
    intro h

    have hOXZ :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ).2.2.2.1

    have hXZY :
        PrimCollinear Geo X Z Y :=
      PrimCollinearRotate
        Geo X Y Z h

    have hOXY :
        PrimCollinear Geo O X Y :=
      hilbert_primCollinear_trans
        Geo O X Z Y
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          X O Z hXOZ).2.2.1
        (PrimCollinearSwap
          Geo X O Z hOXZ)
        hXZY

    exact
      hXOY
        (PrimCollinearSwap
          Geo O X Y hOXY)

  have hA'B'C' :
      Not (PrimCollinear Geo A' B' C') := by
    intro h

    have hO'A'C' :
        PrimCollinear Geo O' A' C' :=
      PrimCollinearSwap
        Geo A' O' C'
        hA'O'C'Data.2.2.2.1

    have hA'C'B' :
        PrimCollinear Geo A' C' B' :=
      PrimCollinearRotate
        Geo A' B' C' h

    have hO'A'B' :
        PrimCollinear Geo O' A' B' :=
      hilbert_primCollinear_trans
        Geo O' A' C' B'
        hA'O'C'Data.2.2.1
        hO'A'C'
        hA'C'B'

    exact
      hA'O'B'
        (PrimCollinearSwap
          Geo O' A' B' hO'A'B')

  have hSecondSide :
      Geo.Congruent Y Z B' C' :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      X Y Z
      A' B' C'
      hXYZ
      hA'B'C'
      hFirstSide
      hXZ
      hAngleXYZ

  have hSecondAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      X Y Z
      A' B' C'
      hXYZ
      hA'B'C'
      hFirstSide
      hXZ
      hAngleXYZ

  have hZOX :
      Geo.Between Z O X :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X O Z hXOZ).2.2.2.2

  have hRayZOX :
      HilbertSameRay Geo Z O X :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      Z O X hZOX

  have hC'O'A' :
      Geo.Between C' O' A' :=
    hA'O'C'Data.2.2.2.2

  have hRayC'O'A' :
      HilbertSameRay Geo C' O' A' :=
    hilbert_space_sameRay_of_between
      (Geo := Geo)
      C' O' A' hC'O'A'

  have hAngleZOY :
      Geo.AngleCongruent
        O Z Y
        O' C' B' := by

    have hLeft :
        Geo.Angle O Z Y =
        Geo.Angle X Z Y :=
      hilbert_space_angle_eq_of_sameRay_first
        (Geo := Geo)
        Z O X Y hRayZOX

    have hRight :
        Geo.Angle O' C' B' =
        Geo.Angle A' C' B' :=
      hilbert_space_angle_eq_of_sameRay_first
        (Geo := Geo)
        C' O' A' B' hRayC'O'A'

    unfold Geometry.Geo.AngleCongruent
      at hSecondAngles ⊢

    rw [hLeft, hRight]
    exact hSecondAngles.2

  have hZO :
      Geo.Congruent Z O C' O' :=
    (Geo.congruent_reverse_second
      Z O O' C').mp
      ((Geo.congruent_reverse_first
        O Z O' C').mp hOZ)

  have hZY :
      Geo.Congruent Z Y C' B' :=
    (Geo.congruent_reverse_second
      Z Y B' C').mp
      ((Geo.congruent_reverse_first
        Y Z B' C').mp hSecondSide)

  have hZOY :
      Not (PrimCollinear Geo Z O Y) := by
    intro h

    have hXOZCol :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X O Z hXOZ).2.2.2.1

    exact
      hXOY
        (hilbert_primCollinear_trans
          Geo X O Z Y
          (HilbertSpaceOrder.between_incidence
            (Geo := Geo)
            X O Z hXOZ).2.1
          hXOZCol
          (PrimCollinearSwap
            Geo Z O Y h))

  have hC'O'B' :
      Not (PrimCollinear Geo C' O' B') := by
    intro h

    have hO'C'B' :
        PrimCollinear Geo O' C' B' :=
      PrimCollinearSwap
        Geo C' O' B' h

    exact
      hA'O'B'
        (hilbert_primCollinear_trans
          Geo A' O' C' B'
          hA'O'C'Data.2.1
          hA'O'C'Data.2.2.2.1
          hO'C'B')

  have hFinal :
      Geo.AngleCongruent
        Z O Y
        C' O' B' :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      Z O Y
      C' O' B'
      hZOY
      hC'O'B'
      hZO
      hZY
      hAngleZOY

  have hTargetLeft :
      Geo.Angle B O C =
      Geo.Angle Z O Y := by
    calc
      Geo.Angle B O C =
          Geo.Angle C O B :=
        Geo.angle_swap B O C
      _ =
          Geo.Angle Z O B :=
        hilbert_space_angle_eq_of_sameRay_first
          (Geo := Geo)
          O C Z B hCZ
      _ =
          Geo.Angle Z O Y :=
        hilbert_space_angle_eq_of_sameRay_second
          (Geo := Geo)
          O Z B Y hBY

  have hTargetRight :
      Geo.Angle B' O' C' =
      Geo.Angle C' O' B' :=
    Geo.angle_swap B' O' C'

  unfold Geometry.Geo.AngleCongruent
    at hFinal ⊢

  rw [hTargetLeft, hTargetRight]
  exact hFinal


end Geometry


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Spatial Hilbert Theorem 21: all ambient right angles are congruent.

The proof deliberately preserves the 2D/3D architecture:

1. choose the plane of the second right angle;
2. use spatial Hilbert III.4 to copy the first right angle into that plane;
3. use spatial Hilbert Theorem 14 (`test05`) to prove that the copied
   angle is again right;
4. compare the two right angles inside the common plane by the already
   proved `PlaneGeo` theorem from `test03`;
5. compose the angle congruences.

No global planar `HilbertCongruence Geo` instance is installed.
-/


/--
Spatial Hilbert Theorem 21.

Any two nondegenerate right angles in Hilbert 3-space are congruent,
even when they lie in different planes.
-/
theorem hilbert_space_all_right_angles_congruent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A O B A' O' B' : Geo.Point)
    (hAOB :
      Not (PrimCollinear Geo A O B))
    (hA'OB' :
      Not (PrimCollinear Geo A' O' B'))
    (hRight :
      HilbertRightAngle Geo A O B)
    (hRight' :
      HilbertRightAngle Geo A' O' B') :
    Geo.AngleCongruent
      A O B
      A' O' B' := by

  --------------------------------------------------------------------
  -- The target right angle determines an explicit ambient plane.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A' O' B'
        hA'OB' with
    ⟨pi, hA'pi, hO'pi, hB'pi⟩

  have hA'O' :
      Ne A' O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hA'OB'

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A' O' hA'O' with
    ⟨base, hA'base, hO'base⟩

  have hBasePi :
      HilbertLineInPlane Geo base pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A' O' hA'O'
      base
      hA'base hO'base
      pi
      hA'pi hO'pi

  have hB'off :
      Not (H.OnLine B' base) := by
    intro hB'base
    exact
      hA'OB'
        ⟨base,
         hA'base,
         hO'base,
         hB'base⟩

  --------------------------------------------------------------------
  -- Copy the first ambient angle into the plane of the second one.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        A O B
        A' O' B'
        hAOB
        hA'O'
        pi
        base
        hBasePi
        hA'base
        hO'base
        hB'pi
        hB'off with
    ⟨K, hKSame, hCopy, _hUnique⟩

  have hKpi :
      S.OnPlane K pi :=
    hKSame.1

  have hKoff :
      Not (H.OnLine K base) :=
    hKSame.2.2.1

  have hA'OK :
      Not (PrimCollinear Geo A' O' K) :=
    hilbert_not_collinear_of_off_line
      Geo
      A' O' K
      base
      hA'O'
      hA'base
      hO'base
      hKoff

  --------------------------------------------------------------------
  -- Expose the supplementary points witnessing both right angles.
  --------------------------------------------------------------------

  rcases hRight with
    ⟨C, hAOC, hRightEq⟩

  rcases hRight' with
    ⟨D', hA'O'D', hRightEqTarget⟩

  --------------------------------------------------------------------
  -- Hilbert 14 transports the source supplementary congruence.
  --
  -- From
  --
  --   AOB ~= A'O'K
  --
  -- and the linear pairs A-O-C, A'-O'-D',
  --
  --   BOC ~= KO'D'.
  --
  -- Since AOB ~= BOC, the copied angle A'O'K is right.
  --------------------------------------------------------------------

  have hSupp :
      Geo.AngleCongruent
        B O C
        K O' D' :=
    hilbert_space_adjacent_angles_congruent
      (Geo := Geo)
      A O B C
      A' O' K D'
      hAOC
      hA'O'D'
      hAOB
      hA'OK
      hCopy

  have hCopySymm :
      Geo.AngleCongruent
        A' O' K
        A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      A' O' K
      hCopy

  have hCopiedToSourceSupplement :
      Geo.AngleCongruent
        A' O' K
        B O C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A' O' K
      A O B
      B O C
      hCopySymm
      hRightEq

  have hCopiedRightEq :
      Geo.AngleCongruent
        A' O' K
        K O' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A' O' K
      B O C
      K O' D'
      hCopiedToSourceSupplement
      hSupp

  have hRightK :
      HilbertRightAngle Geo A' O' K :=
    ⟨D',
     hA'O'D',
     hCopiedRightEq⟩

  --------------------------------------------------------------------
  -- Both A'O'K and A'O'B' now lie in pi.
  -- Apply the coplanar Hilbert 21 proved in test03.
  --------------------------------------------------------------------

  let A'p : PlanePoint Geo pi :=
    ⟨A', hA'pi⟩

  let O'p : PlanePoint Geo pi :=
    ⟨O', hO'pi⟩

  let Kp : PlanePoint Geo pi :=
    ⟨K, hKpi⟩

  let B'p : PlanePoint Geo pi :=
    ⟨B', hB'pi⟩

  have hLocal :
      Geo.AngleCongruent
        A' O' K
        A' O' B' :=
    hilbert_space_coplanar_right_angles_congruent
      (Geo := Geo)
      pi
      A'p O'p Kp
      A'p O'p B'p
      (by
        simpa [A'p, O'p, Kp] using hA'OK)
      (by
        simpa [A'p, O'p, B'p] using hA'OB')
      hRightK
      ⟨D', hA'O'D', hRightEqTarget⟩

  --------------------------------------------------------------------
  -- Compose the copied angle with the local comparison.
  --------------------------------------------------------------------

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O B
      A' O' K
      A' O' B'
      hCopy
      hLocal


/--
Ambient right-triangle hypotenuse comparison.

Two nondegenerate right triangles may lie in different planes.  If the
corresponding legs are congruent, then their hypotenuses are congruent.
-/
theorem hilbert_space_right_triangles_hypotenuse
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C A' B' C' : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear Geo A' B' C'))
    (hRight :
      HilbertRightAngle Geo B A C)
    (hRight' :
      HilbertRightAngle Geo B' A' C')
    (hAB :
      Geo.Congruent A B A' B')
    (hAC :
      Geo.Congruent A C A' C') :
    Geo.Congruent B C B' C' := by

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  have hB'A'C' :
      Not (PrimCollinear Geo B' A' C') := by
    intro h
    exact
      hA'B'C'
        (PrimCollinearSwap
          Geo B' A' C' h)

  have hAngle :
      Geo.AngleCongruent
        B A C
        B' A' C' :=
    hilbert_space_all_right_angles_congruent
      (Geo := Geo)
      B A C
      B' A' C'
      hBAC
      hB'A'C'
      hRight
      hRight'

  exact
    hilbert_space_sas_third_side
      (Geo := Geo)
      A B C
      A' B' C'
      hABC
      hA'B'C'
      hAB
      hAC
      hAngle


end Geometry


namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Two construction lemmas needed for the final spatial corner:

1. complete a square when two prescribed adjacent sides are already
   equal and perpendicular;
2. erect from a point of an ambient plane a normal segment congruent
   to a prescribed segment.

The first lemma is planar and is essentially the second half of
Euclid I.46.  The second lemma is spatial and uses XI.12 plus Hilbert
III.1.
-/


/--
Complete a square from two prescribed equal perpendicular adjacent
sides.

Given noncollinear `A B D`, with `AD ~= AB` and right angle `DAB`,
there exists `C` such that `A B C D` is a square.

This is exactly the part of Euclid I.46 after the perpendicular equal
side has already been constructed.
-/
theorem hilbert_square_complete_of_equal_perpendicular
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B D : Geo.Point)
    (hNCABD :
      Not (PrimCollinear Geo A B D))
    (hRightDAB :
      HilbertRightAngle Geo D A B)
    (hCongAD_AB :
      Geo.Congruent A D A B) :
    exists C : Geo.Point,
      IsSquare Geo A B C D := by

  --------------------------------------------------------------------
  -- Complete the parallelogram A-B-C-D.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo A B D hNCABD with
    ⟨C, hParallelogram⟩

  --------------------------------------------------------------------
  -- I.34 gives opposite sides and opposite angles.
  --------------------------------------------------------------------

  have hI34 :=
    euclid_proposition_34
      Geo A B C D hParallelogram

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    hI34.1

  have hOppositeAngles :
      OppositeAnglesCongruent Geo A B C D :=
    hI34.2

  --------------------------------------------------------------------
  -- All four sides are congruent.
  --------------------------------------------------------------------

  have hCongDA_AB :
      Geo.Congruent D A A B :=
    CongruentReverseFirst
      Geo A D A B hCongAD_AB

  have hCongBC_AB :
      Geo.Congruent B C A B :=
    hilbert_congruent_transitivity
      Geo B C D A A B
      hSides.2
      hCongDA_AB

  have hCongAB_BC :
      Geo.Congruent A B B C :=
    hilbert_congruent_symmetry
      Geo B C A B hCongBC_AB

  have hCongBC_CD :
      Geo.Congruent B C C D :=
    hilbert_congruent_transitivity
      Geo B C A B C D
      hCongBC_AB
      hSides.1

  have hCongCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hSides.1

  have hCongAB_DA :
      Geo.Congruent A B D A :=
    hilbert_congruent_symmetry
      Geo D A A B hCongDA_AB

  have hCongCD_DA :
      Geo.Congruent C D D A :=
    hilbert_congruent_transitivity
      Geo C D A B D A
      hCongCD_AB
      hCongAB_DA

  --------------------------------------------------------------------
  -- The remaining three angles are right.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hParallelogram

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    parallelogram_adjacent_right_angle
      Geo A B C D
      hParallelogram
      hRightDAB

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    hilbert_right_angle_transport
      Geo
      D A B
      B C D
      hNC.1
      hNC.2.2.1
      hRightDAB
      hOppositeAngles.1

  have hRightCDA :
      HilbertRightAngle Geo C D A :=
    hilbert_right_angle_transport
      Geo
      A B C
      C D A
      hNC.2.1
      hNC.2.2.2
      hRightABC
      hOppositeAngles.2

  exact
    ⟨C,
      hParallelogram,
      hCongAB_BC,
      hCongBC_CD,
      hCongCD_DA,
      hRightDAB,
      hRightABC,
      hRightBCD,
      hRightCDA⟩


/--
Erect an equal normal segment from a point of a plane.

For `A` on `pi` and a nondegenerate reference segment `AB`, construct
a line `l` perpendicular to `pi` at `A` and a point `E` on `l` such
that:

* `E` is outside `pi`;
* `AE ~= AB`.

Construction:

1. XI.12 gives the normal line `l` at `A`;
2. choose any second point `X` on `l`;
3. Hilbert III.1 lays off `AB` on ray `AX`;
4. uniqueness of the perpendicular foot proves that the new endpoint
   cannot lie in `pi`.
-/
theorem hilbert_space_equal_normal_segment_exists
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
    (A B : Geo.Point)
    (hApi : S.OnPlane A pi) :
    exists l : Geo.Line,
      exists E : Geo.Point,
        HilbertLinePerpendicularPlaneAt Geo l pi A /\
        H.OnLine E l /\
        Not (S.OnPlane E pi) /\
        Geo.Congruent A E A B := by

  --------------------------------------------------------------------
  -- XI.12: erect the normal line at A.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_12
        (Geo := Geo)
        pi A hApi with
    ⟨l, hPerp⟩

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hAl :
      H.OnLine A l :=
    hInc.1

  --------------------------------------------------------------------
  -- Choose a direction point X on the normal.
  --------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l A with
    ⟨X, hXA, hXl⟩

  have hAX :
      Ne A X :=
    hXA.symm

  --------------------------------------------------------------------
  -- Hilbert III.1: lay off AB on ray AX.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        A B
        A X
        hAX with
    ⟨E, hRayAXE, hCongAE⟩

  have hEA :
      Ne E A :=
    hRayAXE.2.1

  have hEl :
      H.OnLine E l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAX
      hAl
      hXl
      hRayAXE.2.2.1

  --------------------------------------------------------------------
  -- E cannot return to the base plane: A is the unique foot.
  --------------------------------------------------------------------

  have hEoff :
      Not (S.OnPlane E pi) := by
    intro hEpi

    have hEAeq :
        E = A :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        pi l A E
        hPerp
        hEl
        hEpi

    exact
      hEA hEAeq

  exact
    ⟨l, E,
      hPerp,
      hEl,
      hEoff,
      hCongAE⟩


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Existence of the basic square-normal scaffold.

We construct:

* an ambient plane `pi`;
* a square `A B C D` inside `PlaneGeo Geo pi`;
* a line `l` perpendicular to `pi` at `A`;
* a point `E` on `l`, outside `pi`, with `AE ~= AB`.

This is the exact input needed for the two vertical square faces in the
next stage.
-/


/--
There exists a planar square together with an equal normal edge erected
at one of its vertices.
-/
theorem hilbert_space_square_equal_normal_scaffold_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo] :
    exists pi : S.Plane,
      exists A B C D : PlanePoint Geo pi,
        IsSquare
            (PlaneGeo Geo pi)
            A B C D /\
        exists l : Geo.Line,
          exists E : Geo.Point,
            HilbertLinePerpendicularPlaneAt
              Geo l pi A.1 /\
            H.OnLine E l /\
            Not (S.OnPlane E pi) /\
            Geo.Congruent A.1 E A.1 B.1 := by

  --------------------------------------------------------------------
  -- Start from Hilbert I.8 and take the plane through the first three
  -- noncoplanar-frame points.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.four_noncoplanar
        (Geo := Geo) with
    ⟨P, Q, R, T, hNoncoplanar⟩

  have hPQR :
      Not (PrimCollinear Geo P Q R) :=
    hilbert_noncoplanar4_not_collinear_first_three
      (Geo := Geo)
      P Q R T
      hNoncoplanar

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        P Q R hPQR with
    ⟨pi, hPpi, hQpi, hRpi⟩

  let A : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let B : PlanePoint Geo pi :=
    ⟨Q, hQpi⟩

  have hPQ :
      Ne P Q :=
    hilbert_noncollinear_ne_first
      Geo P Q R hPQR

  have hAB :
      Ne A B := by
    intro h
    apply hPQ
    exact congrArg Subtype.val h

  --------------------------------------------------------------------
  -- Euclid I.46 inside the induced plane.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        (PlaneGeo Geo pi)
        A B hAB with
    ⟨C, D, hSquare⟩

  --------------------------------------------------------------------
  -- XI.12 + III.1: erect an equal normal edge AE at A.
  --------------------------------------------------------------------

  rcases
      hilbert_space_equal_normal_segment_exists
        (Geo := Geo)
        pi
        A.1 B.1
        A.2 with
    ⟨l, E,
     hPerp,
     hEl,
     hEoff,
     hAE_AB⟩

  exact
    ⟨pi,
     A, B, C, D,
     hSquare,
     l, E,
     hPerp,
     hEl,
     hEoff,
     hAE_AB⟩


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Four ambient points form a square inside the explicit ambient plane `pi`.

The point-plane incidence proofs are hidden existentially so that callers
do not have to mention proof terms in dependent `PlanePoint` arguments.
-/
def IsSquareInPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (A B C D : Geo.Point) : Prop :=
  exists hA : S.OnPlane A pi,
    exists hB : S.OnPlane B pi,
      exists hC : S.OnPlane C pi,
        exists hD : S.OnPlane D pi,
          IsSquare
            (PlaneGeo Geo pi)
            ⟨A, hA⟩
            ⟨B, hB⟩
            ⟨C, hC⟩
            ⟨D, hD⟩

/-!
# Coxeter A3 existence - derived spatial layer

Construct one vertical square face from:

* a base edge `AB` contained in an ambient plane `pi`;
* a normal line `l` to `pi` at `A`;
* a point `E` on `l`, with `AE ~= AB`.

The two intersecting lines `l` and `AB` determine a vertical plane
`sigma`.  Inside `PlaneGeo sigma`, XI.4 normalizes the line-line
perpendicularity to the chosen points `E,A,B`, and the square is
completed by the planar constructor from test08.
-/


/--
Construct a square face on a base edge and an equal normal edge.

Input:
* `A,B` lie in `pi`;
* `l` is perpendicular to `pi` at `A`;
* `E` lies on `l`, outside `pi`;
* `AE ~= AB`.

Output:
* a vertical plane `sigma` containing `A,B,E`;
* a point `F` in `sigma`;
* `A B F E` is a square in `PlaneGeo sigma`.
-/
theorem hilbert_space_vertical_square_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A B E : Geo.Point)
    (l : Geo.Line)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hAB : Ne A B)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hEl : H.OnLine E l)
    (hEoff : Not (S.OnPlane E pi))
    (hAE_AB : Geo.Congruent A E A B) :
    exists sigma : S.Plane,
      exists F : Geo.Point,
        S.OnPlane A sigma /\
        S.OnPlane B sigma /\
        S.OnPlane E sigma /\
        S.OnPlane F sigma /\
        IsSquareInPlane Geo sigma A B F E := by

  --------------------------------------------------------------------
  -- Carrier line m = AB lies in the base plane pi.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨m, hAm, hBm⟩

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      m hAm hBm
      pi hApi hBpi

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hAl :
      H.OnLine A l :=
    hInc.1

  --------------------------------------------------------------------
  -- The normal line l is distinct from the base line m.
  --------------------------------------------------------------------

  have hlm :
      Ne l m := by
    intro hEq

    have hlpi :
        HilbertLineInPlane Geo l pi := by
      rw [hEq]
      exact hmpi

    exact
      (hilbert_linePerpendicularPlaneAt_not_in_plane
        (Geo := Geo)
        l pi A hPerp)
        hlpi

  --------------------------------------------------------------------
  -- l and m determine the vertical plane sigma.
  --------------------------------------------------------------------

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm
        A hAl hAm with
    ⟨sigma, hlsigma, hmsigma, _hUniqueSigma⟩

  have hAsigma :
      S.OnPlane A sigma :=
    hlsigma A hAl

  have hBsigma :
      S.OnPlane B sigma :=
    hmsigma B hBm

  have hEsigma :
      S.OnPlane E sigma :=
    hlsigma E hEl

  --------------------------------------------------------------------
  -- The normal-to-plane relation gives l perpendicular to m at A.
  --------------------------------------------------------------------

  have hPerpLM :
      HilbertLinesPerpendicularAt Geo l m A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp
      hmpi
      hAm

  let lp : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  let mp : PlaneLine Geo sigma :=
    ⟨m, hmsigma⟩

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Ep : PlanePoint Geo sigma :=
    ⟨E, hEsigma⟩

  have hlpmp :
      Ne lp mp := by
    intro h
    apply hlm
    exact congrArg Subtype.val h

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma)
        lp mp Ap :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma lp mp Ap).mpr
      hPerpLM

  --------------------------------------------------------------------
  -- E != A because E is outside pi while A is in pi.
  --------------------------------------------------------------------

  have hEA :
      Ne E A := by
    intro hEq
    subst E
    exact hEoff hApi

  have hEpAp :
      Ne Ep Ap := by
    intro h
    apply hEA
    exact congrArg Subtype.val h

  have hBpAp :
      Ne Bp Ap := by
    intro h
    apply hAB
    exact (congrArg Subtype.val h).symm

  --------------------------------------------------------------------
  -- XI.4: normalize perpendicularity to the chosen points E,A,B.
  --------------------------------------------------------------------

  have hNorm :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo sigma)
      lp mp
      Ap Ep Bp
      hlpmp
      hPerpPlane
      hEpAp
      hBpAp
      hEl
      hBm

  have hEAB :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ep Ap Bp) :=
    hNorm.1

  have hRightEAB :
      HilbertRightAngle
        (PlaneGeo Geo sigma)
        Ep Ap Bp :=
    hNorm.2

  --------------------------------------------------------------------
  -- Reorder noncollinearity for the square constructor A-B-?-E.
  --------------------------------------------------------------------

  have hABENon :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Ap Bp Ep) := by
    intro hCol

    have hBEA :
        PrimCollinear
          (PlaneGeo Geo sigma)
          Bp Ep Ap :=
      PrimCollinearCycle
        (PlaneGeo Geo sigma)
        Ap Bp Ep hCol

    have hEAB' :
        PrimCollinear
          (PlaneGeo Geo sigma)
          Ep Ap Bp :=
      PrimCollinearCycle
        (PlaneGeo Geo sigma)
        Bp Ep Ap hBEA

    exact hEAB hEAB'

  --------------------------------------------------------------------
  -- Ambient AE ~= AB becomes plane-local congruence.
  --------------------------------------------------------------------

  have hCongPlane :
      (PlaneGeo Geo sigma).Congruent
        Ap Ep Ap Bp :=
    (planeGeo_congruent
      (Geo := Geo)
      sigma
      Ap Ep Ap Bp).mpr
      hAE_AB

  --------------------------------------------------------------------
  -- Complete A-B-F-E to a square inside the vertical plane sigma.
  --------------------------------------------------------------------

  rcases
      hilbert_square_complete_of_equal_perpendicular
        (PlaneGeo Geo sigma)
        Ap Bp Ep
        hABENon
        hRightEAB
        hCongPlane with
    ⟨Fp, hSquare⟩

  have hSquareAmbient :
      IsSquareInPlane Geo sigma A B Fp.1 E := by
    exact
      ⟨hAsigma,
       hBsigma,
       Fp.2,
       hEsigma,
       hSquare⟩

  exact
    ⟨sigma,
     Fp.1,
     hAsigma,
     hBsigma,
     hEsigma,
     Fp.2,
     hSquareAmbient⟩


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Existence of a three-square spatial corner.

The data are:

* base square      A B C D in pi,
* front square     A B F E in sigmaFront,
* left square      A D H E in sigmaLeft,
* AE perpendicular to the base plane pi,
* AE congruent to AB.

This is the synthetic three-face corner of a cube.  No top/right/back
face is constructed.
-/


/--
Three mutually attached square faces around the vertex A.

The common edge `AE` is explicitly certified as normal to the base
plane.  The two vertical squares are stored using `IsSquareInPlane`,
so their plane-incidence witnesses remain local.
-/
structure HilbertThreeSquareCorner3D
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] where

  pi : S.Plane
  sigmaFront : S.Plane
  sigmaLeft : S.Plane

  A : Geo.Point
  B : Geo.Point
  C : Geo.Point
  D : Geo.Point
  E : Geo.Point
  F : Geo.Point
  Hpt : Geo.Point

  normalLine : Geo.Line

  base :
    IsSquareInPlane Geo pi A B C D

  normal :
    HilbertLinePerpendicularPlaneAt
      Geo normalLine pi A

  E_on_normal :
    H.OnLine E normalLine

  E_off_base :
    Not (S.OnPlane E pi)

  AE_eq_AB :
    Geo.Congruent A E A B

  front :
    IsSquareInPlane
      Geo sigmaFront A B F E

  left :
    IsSquareInPlane
      Geo sigmaLeft A D Hpt E


/--
A three-square spatial corner exists in every Hilbert 3-space with the
current Euclidean spatial interface.
-/
theorem hilbert_three_square_corner_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo] :
    Nonempty (HilbertThreeSquareCorner3D Geo) := by

  --------------------------------------------------------------------
  -- Base square plus equal normal edge.
  --------------------------------------------------------------------

  rcases
      hilbert_space_square_equal_normal_scaffold_exists
        (Geo := Geo) with
    ⟨pi,
     A, B, C, D,
     hBase,
     l, E,
     hNormal,
     hEl,
     hEoff,
     hAE_AB⟩

  --------------------------------------------------------------------
  -- Package the base square ambiently.
  --------------------------------------------------------------------

  have hBaseAmbient :
      IsSquareInPlane
        Geo pi
        A.1 B.1 C.1 D.1 := by
    exact
      ⟨A.2,
       B.2,
       C.2,
       D.2,
       hBase⟩

  --------------------------------------------------------------------
  -- The base edge AB is nondegenerate.
  --------------------------------------------------------------------

  have hABPlane :
      Ne A B :=
    hBase.1.1.1

  have hAB :
      Ne A.1 B.1 := by
    intro h
    apply hABPlane
    exact Subtype.ext h

  --------------------------------------------------------------------
  -- First vertical square: A-B-F-E.
  --------------------------------------------------------------------

  rcases
      hilbert_space_vertical_square_exists
        (Geo := Geo)
        pi
        A.1 B.1 E
        l
        A.2
        B.2
        hAB
        hNormal
        hEl
        hEoff
        hAE_AB with
    ⟨sigmaFront,
     F,
     _hAFront,
     _hBFront,
     _hEFront,
     _hFFront,
     hFront⟩

  --------------------------------------------------------------------
  -- Prepare AE ~= AD from the base square.
  --------------------------------------------------------------------

  have hBaseSides :=
    euclid_proposition_46_side
      (PlaneGeo Geo pi)
      A B C D
      hBase

  have hAB_DA_Plane :
      (PlaneGeo Geo pi).Congruent
        A B D A :=
    hBaseSides.2.2

  have hAB_DA :
      Geo.Congruent
        A.1 B.1 D.1 A.1 :=
    (planeGeo_congruent
      (Geo := Geo)
      pi
      A B D A).mp
      hAB_DA_Plane

  have hAB_AD :
      Geo.Congruent
        A.1 B.1 A.1 D.1 :=
    CongruentSwapSecond
      Geo
      A.1 B.1
      D.1 A.1
      hAB_DA

  have hAE_AD :
      Geo.Congruent
        A.1 E A.1 D.1 :=
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      A.1 E
      A.1 B.1
      A.1 D.1
      hAE_AB
      hAB_AD

  --------------------------------------------------------------------
  -- The base edge AD is nondegenerate.
  --------------------------------------------------------------------

  have hDAPlane :
      Ne D A :=
    hBase.1.2.2.1

  have hAD :
      Ne A.1 D.1 := by
    intro h
    apply hDAPlane
    exact
      Subtype.ext h.symm

  --------------------------------------------------------------------
  -- Second vertical square: A-D-H-E.
  --------------------------------------------------------------------

  rcases
      hilbert_space_vertical_square_exists
        (Geo := Geo)
        pi
        A.1 D.1 E
        l
        A.2
        D.2
        hAD
        hNormal
        hEl
        hEoff
        hAE_AD with
    ⟨sigmaLeft,
     Hpt,
     _hALeft,
     _hDLeft,
     _hELeft,
     _hHLeft,
     hLeft⟩

  --------------------------------------------------------------------
  -- Package the three-square corner.
  --------------------------------------------------------------------

  exact
    ⟨{
      pi := pi
      sigmaFront := sigmaFront
      sigmaLeft := sigmaLeft

      A := A.1
      B := B.1
      C := C.1
      D := D.1
      E := E
      F := F
      Hpt := Hpt

      normalLine := l

      base := hBaseAmbient
      normal := hNormal
      E_on_normal := hEl
      E_off_base := hEoff
      AE_eq_AB := hAE_AB
      front := hFront
      left := hLeft
    }⟩


end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

The two vertical outer edges of the three-square corner are
perpendicular to the base plane.

The proof has two representation bridges:

1. planar point-pair parallelism inside `PlaneGeo sigma` is converted
   to ambient spatial parallelism of the two carrier lines;
2. the carrier of the common edge `EA` is identified with the original
   normal line by incidence uniqueness.

Then Euclid XI.8 transports perpendicularity from `EA` to `BF` and
from `EA` to `DH`.
-/


/--
Convert planar point-pair parallelism in an induced plane into ambient
spatial parallelism of the corresponding carrier lines.
-/
theorem hilbert_space_parallel_carriers_of_planeGeo_parallel
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (A B C D : PlanePoint Geo sigma)
    (hParallel :
      (PlaneGeo Geo sigma).Parallel A B C D) :
    exists l m : Geo.Line,
      H.OnLine A.1 l /\
      H.OnLine B.1 l /\
      H.OnLine C.1 m /\
      H.OnLine D.1 m /\
      HilbertSpaceLinesParallel Geo l m := by

  have hAB :
      Ne A B :=
    hParallel.1

  have hCD :
      Ne C D :=
    hParallel.2.1

  rcases
      planePoint_line_through
        (Geo := Geo)
        sigma A B hAB with
    ⟨lp, hAl, hBl⟩

  rcases
      planePoint_line_through
        (Geo := Geo)
        sigma C D hCD with
    ⟨mp, hCm, hDm⟩

  have hDisjoint :
      HilbertLinesDisjoint Geo lp.1 mp.1 := by
    rintro ⟨P, hPl, hPm⟩

    have hPsigma :
        S.OnPlane P sigma :=
      lp.2 P hPl

    let Pp : PlanePoint Geo sigma :=
      ⟨P, hPsigma⟩

    have hPAB :
        Pp ∈ (PlaneGeo Geo sigma).PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo sigma)
        A B Pp
        lp
        hAB
        hAl hBl).mpr
        hPl

    have hPCD :
        Pp ∈ (PlaneGeo Geo sigma).PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        (PlaneGeo Geo sigma)
        C D Pp
        mp
        hCD
        hCm hDm).mpr
        hPm

    exact
      Set.disjoint_left.mp
        hParallel.2.2
        hPAB hPCD

  exact
    ⟨lp.1, mp.1,
     hAl, hBl,
     hCm, hDm,
     ⟨sigma,
      lp.2,
      mp.2,
      hDisjoint⟩⟩


/--
Symmetry of spatial line parallelism.
-/
theorem hilbert_space_linesParallel_symm_local
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l m : Geo.Line)
    (hParallel :
      HilbertSpaceLinesParallel Geo l m) :
    HilbertSpaceLinesParallel Geo m l := by

  rcases hParallel with
    ⟨sigma, hlsigma, hmsigma, hDisjoint⟩

  refine
    ⟨sigma,
     hmsigma,
     hlsigma,
     ?_⟩

  rintro ⟨P, hPm, hPl⟩
  exact
    hDisjoint
      ⟨P, hPl, hPm⟩


namespace HilbertThreeSquareCorner3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/--
In a three-square corner, the outer vertical edges `BF` and `DH` are
perpendicular to the base plane at `B` and `D`, respectively.
-/
theorem vertical_edges_perpendicular_to_base
    (Q : HilbertThreeSquareCorner3D Geo) :
    exists lineBF lineDH : Geo.Line,
      H.OnLine Q.B lineBF /\
      H.OnLine Q.F lineBF /\
      H.OnLine Q.D lineDH /\
      H.OnLine Q.Hpt lineDH /\
      HilbertLinePerpendicularPlaneAt
        Geo lineBF Q.pi Q.B /\
      HilbertLinePerpendicularPlaneAt
        Geo lineDH Q.pi Q.D := by

  --------------------------------------------------------------------
  -- Unpack base incidence.
  --------------------------------------------------------------------

  rcases Q.base with
    ⟨hAbase, hBbase, _hCbase, hDbase, _hBaseSquare⟩

  --------------------------------------------------------------------
  -- Front square A-B-F-E.
  --------------------------------------------------------------------

  rcases Q.front with
    ⟨hAfront, hBfront, hFfront, hEfront, hFrontSquare⟩

  let Af : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.A, hAfront⟩

  let Bf : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.B, hBfront⟩

  let Ff : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.F, hFfront⟩

  let Ef : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.E, hEfront⟩

  have hParallelBFEA :
      (PlaneGeo Geo Q.sigmaFront).Parallel
        Bf Ff Ef Af :=
    hFrontSquare.1.2

  rcases
      hilbert_space_parallel_carriers_of_planeGeo_parallel
        (Geo := Geo)
        Q.sigmaFront
        Bf Ff Ef Af
        hParallelBFEA with
    ⟨lineBF, lineEAfront,
     hBbf, hFbf,
     hEeaFront, hAeaFront,
     hParallelBF_EA⟩

  --------------------------------------------------------------------
  -- Identify the front carrier EA with the original normal line.
  --------------------------------------------------------------------

  have hEA :
      Ne Q.E Q.A := by
    intro hEq
    apply Q.E_off_base
    rw [hEq]
    exact hAbase

  have hNormalInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      Q.normal

  have hAonNormal :
      H.OnLine Q.A Q.normalLine :=
    hNormalInc.1

  have hEAfront_eq_normal :
      lineEAfront = Q.normalLine :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      Q.E Q.A hEA
      lineEAfront Q.normalLine
      hEeaFront hAeaFront
      Q.E_on_normal hAonNormal

  have hParallelBFNormal :
      HilbertSpaceLinesParallel
        Geo lineBF Q.normalLine := by
    simpa [hEAfront_eq_normal]
      using hParallelBF_EA

  have hParallelNormalBF :
      HilbertSpaceLinesParallel
        Geo Q.normalLine lineBF :=
    hilbert_space_linesParallel_symm_local
      (Geo := Geo)
      lineBF Q.normalLine
      hParallelBFNormal

  --------------------------------------------------------------------
  -- XI.8 transports perpendicularity from EA to BF.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_8
        (Geo := Geo)
        Q.normalLine lineBF
        Q.pi
        Q.A
        hParallelNormalBF
        Q.normal with
    ⟨XBF, hPerpBF_X⟩

  have hB_eq_XBF :
      Q.B = XBF :=
    hilbert_XI12_perpendicular_foot_unique
      (Geo := Geo)
      Q.pi lineBF
      XBF Q.B
      hPerpBF_X
      hBbf
      hBbase

  subst XBF

  have hPerpBF :
      HilbertLinePerpendicularPlaneAt
        Geo lineBF Q.pi Q.B :=
    hPerpBF_X

  --------------------------------------------------------------------
  -- Left square A-D-H-E.
  --------------------------------------------------------------------

  rcases Q.left with
    ⟨hAleft, hDleft, hHleft, hEleft, hLeftSquare⟩

  let Al : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.A, hAleft⟩

  let Dl : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.D, hDleft⟩

  let Hl : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.Hpt, hHleft⟩

  let El : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.E, hEleft⟩

  have hParallelDHEA :
      (PlaneGeo Geo Q.sigmaLeft).Parallel
        Dl Hl El Al :=
    hLeftSquare.1.2

  rcases
      hilbert_space_parallel_carriers_of_planeGeo_parallel
        (Geo := Geo)
        Q.sigmaLeft
        Dl Hl El Al
        hParallelDHEA with
    ⟨lineDH, lineEAleft,
     hDdh, hHdh,
     hEeaLeft, hAeaLeft,
     hParallelDH_EA⟩

  --------------------------------------------------------------------
  -- Identify the left carrier EA with the same original normal line.
  --------------------------------------------------------------------

  have hEAleft_eq_normal :
      lineEAleft = Q.normalLine :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      Q.E Q.A hEA
      lineEAleft Q.normalLine
      hEeaLeft hAeaLeft
      Q.E_on_normal hAonNormal

  have hParallelDHNormal :
      HilbertSpaceLinesParallel
        Geo lineDH Q.normalLine := by
    simpa [hEAleft_eq_normal]
      using hParallelDH_EA

  have hParallelNormalDH :
      HilbertSpaceLinesParallel
        Geo Q.normalLine lineDH :=
    hilbert_space_linesParallel_symm_local
      (Geo := Geo)
      lineDH Q.normalLine
      hParallelDHNormal

  --------------------------------------------------------------------
  -- XI.8 transports perpendicularity from EA to DH.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_8
        (Geo := Geo)
        Q.normalLine lineDH
        Q.pi
        Q.A
        hParallelNormalDH
        Q.normal with
    ⟨XDH, hPerpDH_X⟩

  have hD_eq_XDH :
      Q.D = XDH :=
    hilbert_XI12_perpendicular_foot_unique
      (Geo := Geo)
      Q.pi lineDH
      XDH Q.D
      hPerpDH_X
      hDdh
      hDbase

  subst XDH

  have hPerpDH :
      HilbertLinePerpendicularPlaneAt
        Geo lineDH Q.pi Q.D :=
    hPerpDH_X

  exact
    ⟨lineBF, lineDH,
     hBbf, hFbf,
     hDdh, hHdh,
     hPerpBF,
     hPerpDH⟩


end HilbertThreeSquareCorner3D

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Metric closure of the three-square corner.

For the alternating vertices

    A, C, F, H

we prove all five nontrivial edge equalities with the reference edge
`AC`:

    AF ~= AC,
    AH ~= AC,
    CF ~= AC,
    CH ~= AC,
    FH ~= AC.

The first four are right-triangle comparisons using the two vertical
edges proved perpendicular to the base plane in test12.

The final equality `FH ~= AC` does not require a top square.  Instead:

* `AB` is perpendicular to both `AD` and the normal `AE`;
* XI.4 therefore gives `AB` perpendicular to the left vertical plane;
* the front square gives `FE || AB`;
* XI.8 transports the plane perpendicularity from `AB` to `FE`;
* hence `FE` is perpendicular to `EH`;
* the right triangles `ABC` and `FEH` have corresponding equal legs,
  so their hypotenuses `AC` and `FH` are congruent.

No coordinates or metric formulas are used.
-/


/--
Ambient normalization of a line-line perpendicularity to arbitrary
chosen nonvertex points on the two carriers.

The proof chooses the plane generated by the two intersecting lines and
uses the already established planar XI.4 normalization inside its
`PlaneGeo`.
-/
theorem hilbert_space_linesPerpendicularAt_right_angle_of_points
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m : Geo.Line)
    (O A B : Geo.Point)
    (hPerp :
      HilbertLinesPerpendicularAt Geo l m O)
    (hAO : Ne A O)
    (hBO : Ne B O)
    (hAl : H.OnLine A l)
    (hBm : H.OnLine B m) :
    Not (PrimCollinear Geo A O B) /\
    HilbertRightAngle Geo A O B := by

  have hlm :
      Ne l m :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l m O hPerp

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm
        O
        hPerp.1
        hPerp.2.1 with
    ⟨rho, hlrho, hmrho, _hUnique⟩

  let lp : PlaneLine Geo rho :=
    ⟨l, hlrho⟩

  let mp : PlaneLine Geo rho :=
    ⟨m, hmrho⟩

  let Op : PlanePoint Geo rho :=
    ⟨O, hlrho O hPerp.1⟩

  let Ap : PlanePoint Geo rho :=
    ⟨A, hlrho A hAl⟩

  let Bp : PlanePoint Geo rho :=
    ⟨B, hmrho B hBm⟩

  have hlpmp :
      Ne lp mp := by
    intro h
    apply hlm
    exact congrArg Subtype.val h

  have hAOp :
      Ne Ap Op := by
    intro h
    apply hAO
    exact congrArg Subtype.val h

  have hBOp :
      Ne Bp Op := by
    intro h
    apply hBO
    exact congrArg Subtype.val h

  have hPerpPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho)
        lp mp Op :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      rho lp mp Op).mpr
      hPerp

  have hNorm :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      lp mp
      Op Ap Bp
      hlpmp
      hPerpPlane
      hAOp
      hBOp
      hAl
      hBm

  have hNonAmbient :
      Not (PrimCollinear Geo A O B) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      rho Ap Op Bp
      hNorm.1

  have hRightAmbient :
      HilbertRightAngle Geo A O B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      rho Ap Op Bp).mp
      hNorm.2

  exact
    ⟨hNonAmbient, hRightAmbient⟩


/--
A line perpendicular to a plane forms a right angle with every
nondegenerate line of that plane through the foot, normalized to
arbitrary chosen points on the two carriers.
-/
theorem hilbert_space_linePerpendicularPlane_right_angle_of_points
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (normalLine planeLine : Geo.Line)
    (O A B : Geo.Point)
    (hPerpPlane :
      HilbertLinePerpendicularPlaneAt
        Geo normalLine pi O)
    (hPlaneLineInPi :
      HilbertLineInPlane Geo planeLine pi)
    (hOPlaneLine :
      H.OnLine O planeLine)
    (hAPlaneLine :
      H.OnLine A planeLine)
    (hBNormal :
      H.OnLine B normalLine)
    (hAO : Ne A O)
    (hBO : Ne B O) :
    Not (PrimCollinear Geo A O B) /\
    HilbertRightAngle Geo A O B := by

  have hNormalPerpPlaneLine :
      HilbertLinesPerpendicularAt
        Geo normalLine planeLine O :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerpPlane
      hPlaneLineInPi
      hOPlaneLine

  have hPlaneLinePerpNormal :
      HilbertLinesPerpendicularAt
        Geo planeLine normalLine O :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      normalLine planeLine O
      hNormalPerpPlaneLine

  exact
    hilbert_space_linesPerpendicularAt_right_angle_of_points
      (Geo := Geo)
      planeLine normalLine
      O A B
      hPlaneLinePerpNormal
      hAO
      hBO
      hAPlaneLine
      hBNormal


namespace HilbertThreeSquareCorner3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/--
All five nontrivial edges of the alternating tetrahedron `A,C,F,H`
are congruent to the reference edge `AC`.
-/
theorem alternating_edges_congruent
    (Q : HilbertThreeSquareCorner3D Geo) :
    Geo.Congruent Q.A Q.F Q.A Q.C /\
    Geo.Congruent Q.A Q.Hpt Q.A Q.C /\
    Geo.Congruent Q.C Q.F Q.A Q.C /\
    Geo.Congruent Q.C Q.Hpt Q.A Q.C /\
    Geo.Congruent Q.F Q.Hpt Q.A Q.C := by

  --------------------------------------------------------------------
  -- Unpack the three square faces.
  --------------------------------------------------------------------

  rcases Q.base with
    ⟨hAbase, hBbase, hCbase, hDbase, hBaseSquare⟩

  rcases Q.front with
    ⟨hAfront, hBfront, hFfront, hEfront, hFrontSquare⟩

  rcases Q.left with
    ⟨hAleft, hDleft, hHleft, hEleft, hLeftSquare⟩

  let Ab : PlanePoint Geo Q.pi :=
    ⟨Q.A, hAbase⟩
  let Bb : PlanePoint Geo Q.pi :=
    ⟨Q.B, hBbase⟩
  let Cb : PlanePoint Geo Q.pi :=
    ⟨Q.C, hCbase⟩
  let Db : PlanePoint Geo Q.pi :=
    ⟨Q.D, hDbase⟩

  let Af : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.A, hAfront⟩
  let Bf : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.B, hBfront⟩
  let Ff : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.F, hFfront⟩
  let Ef : PlanePoint Geo Q.sigmaFront :=
    ⟨Q.E, hEfront⟩

  let Al : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.A, hAleft⟩
  let Dl : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.D, hDleft⟩
  let Hl : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.Hpt, hHleft⟩
  let El : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.E, hEleft⟩

  --------------------------------------------------------------------
  -- Noncollinearity and right angles from the three squares.
  --------------------------------------------------------------------

  have hNCBase :=
    parallelogram_vertices_noncollinear
      (PlaneGeo Geo Q.pi)
      Ab Bb Cb Db
      hBaseSquare.1

  have hNCFront :=
    parallelogram_vertices_noncollinear
      (PlaneGeo Geo Q.sigmaFront)
      Af Bf Ff Ef
      hFrontSquare.1

  have hNCLeft :=
    parallelogram_vertices_noncollinear
      (PlaneGeo Geo Q.sigmaLeft)
      Al Dl Hl El
      hLeftSquare.1

  have hABC :
      Not (PrimCollinear Geo Q.A Q.B Q.C) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      Q.pi Ab Bb Cb
      hNCBase.2.1

  have hBAC :
      Not (PrimCollinear Geo Q.B Q.A Q.C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo Q.B Q.A Q.C h)

  have hABF :
      Not (PrimCollinear Geo Q.A Q.B Q.F) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      Q.sigmaFront Af Bf Ff
      hNCFront.2.1

  have hBAF :
      Not (PrimCollinear Geo Q.B Q.A Q.F) := by
    intro h
    exact
      hABF
        (PrimCollinearSwap
          Geo Q.B Q.A Q.F h)

  have hADH :
      Not (PrimCollinear Geo Q.A Q.D Q.Hpt) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      Q.sigmaLeft Al Dl Hl
      hNCLeft.2.1

  have hDAH :
      Not (PrimCollinear Geo Q.D Q.A Q.Hpt) := by
    intro h
    exact
      hADH
        (PrimCollinearSwap
          Geo Q.D Q.A Q.Hpt h)

  have hRightABC :
      HilbertRightAngle Geo Q.A Q.B Q.C :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      Q.pi Ab Bb Cb).mp
      hBaseSquare.2.2.2.2.2.1

  have hRightDAB :
      HilbertRightAngle Geo Q.D Q.A Q.B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      Q.pi Db Ab Bb).mp
      hBaseSquare.2.2.2.2.1

  have hRightABF :
      HilbertRightAngle Geo Q.A Q.B Q.F :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      Q.sigmaFront Af Bf Ff).mp
      hFrontSquare.2.2.2.2.2.1

  have hRightADH :
      HilbertRightAngle Geo Q.A Q.D Q.Hpt :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      Q.sigmaLeft Al Dl Hl).mp
      hLeftSquare.2.2.2.2.2.1

  --------------------------------------------------------------------
  -- Side data: every square side is congruent to its first side.
  --------------------------------------------------------------------

  have hBaseSides :=
    euclid_proposition_46_side
      (PlaneGeo Geo Q.pi)
      Ab Bb Cb Db
      hBaseSquare

  have hFrontSides :=
    euclid_proposition_46_side
      (PlaneGeo Geo Q.sigmaFront)
      Af Bf Ff Ef
      hFrontSquare

  have hLeftSides :=
    euclid_proposition_46_side
      (PlaneGeo Geo Q.sigmaLeft)
      Al Dl Hl El
      hLeftSquare

  have hAB_BC :
      Geo.Congruent Q.A Q.B Q.B Q.C :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.pi Ab Bb Bb Cb).mp
      hBaseSides.1

  have hAB_CD :
      Geo.Congruent Q.A Q.B Q.C Q.D :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.pi Ab Bb Cb Db).mp
      hBaseSides.2.1

  have hAB_DA :
      Geo.Congruent Q.A Q.B Q.D Q.A :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.pi Ab Bb Db Ab).mp
      hBaseSides.2.2

  have hAB_BF :
      Geo.Congruent Q.A Q.B Q.B Q.F :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.sigmaFront Af Bf Bf Ff).mp
      hFrontSides.1

  have hAB_FE :
      Geo.Congruent Q.A Q.B Q.F Q.E :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.sigmaFront Af Bf Ff Ef).mp
      hFrontSides.2.1

  have hAD_DH :
      Geo.Congruent Q.A Q.D Q.D Q.Hpt :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.sigmaLeft Al Dl Dl Hl).mp
      hLeftSides.1

  have hAD_HE :
      Geo.Congruent Q.A Q.D Q.Hpt Q.E :=
    (planeGeo_congruent
      (Geo := Geo)
      Q.sigmaLeft Al Dl Hl El).mp
      hLeftSides.2.1

  --------------------------------------------------------------------
  -- Normalized side congruences used by the right triangles.
  --------------------------------------------------------------------

  have hBA_BA :
      Geo.Congruent Q.B Q.A Q.B Q.A :=
    hilbert_space_congruent_reflexive_all
      (Geo := Geo)
      Q.B Q.A

  have hBC_AB :
      Geo.Congruent Q.B Q.C Q.A Q.B :=
    hilbert_space_congruent_symmetry_all
      (Geo := Geo)
      Q.A Q.B
      Q.B Q.C
      hAB_BC

  have hBC_BF :
      Geo.Congruent Q.B Q.C Q.B Q.F :=
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      Q.B Q.C
      Q.A Q.B
      Q.B Q.F
      hBC_AB
      hAB_BF

  have hAB_AD :
      Geo.Congruent Q.A Q.B Q.A Q.D :=
    CongruentSwapSecond
      Geo
      Q.A Q.B
      Q.D Q.A
      hAB_DA

  have hBA_DA :
      Geo.Congruent Q.B Q.A Q.D Q.A :=
    CongruentReverseFirst
      Geo
      Q.A Q.B
      Q.D Q.A
      hAB_DA

  have hBC_AD :
      Geo.Congruent Q.B Q.C Q.A Q.D :=
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      Q.B Q.C
      Q.A Q.B
      Q.A Q.D
      hBC_AB
      hAB_AD

  have hBC_DH :
      Geo.Congruent Q.B Q.C Q.D Q.Hpt :=
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      Q.B Q.C
      Q.A Q.D
      Q.D Q.Hpt
      hBC_AD
      hAD_DH

  have hBA_BC :
      Geo.Congruent Q.B Q.A Q.B Q.C :=
    CongruentReverseFirst
      Geo
      Q.A Q.B
      Q.B Q.C
      hAB_BC

  have hBA_DC :
      Geo.Congruent Q.B Q.A Q.D Q.C := by
    have hBA_CD :
        Geo.Congruent Q.B Q.A Q.C Q.D :=
      CongruentReverseFirst
        Geo
        Q.A Q.B
        Q.C Q.D
        hAB_CD

    exact
      CongruentSwapSecond
        Geo
        Q.B Q.A
        Q.C Q.D
        hBA_CD

  have hBA_EF :
      Geo.Congruent Q.B Q.A Q.E Q.F := by
    have hBA_FE :
        Geo.Congruent Q.B Q.A Q.F Q.E :=
      CongruentReverseFirst
        Geo
        Q.A Q.B
        Q.F Q.E
        hAB_FE

    exact
      CongruentSwapSecond
        Geo
        Q.B Q.A
        Q.F Q.E
        hBA_FE

  have hAD_EH :
      Geo.Congruent Q.A Q.D Q.E Q.Hpt :=
    CongruentSwapSecond
      Geo
      Q.A Q.D
      Q.Hpt Q.E
      hAD_HE

  have hBC_AD_for_top :
      Geo.Congruent Q.B Q.C Q.A Q.D :=
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      Q.B Q.C
      Q.A Q.B
      Q.A Q.D
      hBC_AB
      hAB_AD

  have hBC_EH :
      Geo.Congruent Q.B Q.C Q.E Q.Hpt :=
    hilbert_space_congruent_transitivity_all
      (Geo := Geo)
      Q.B Q.C
      Q.A Q.D
      Q.E Q.Hpt
      hBC_AD_for_top
      hAD_EH

  --------------------------------------------------------------------
  -- AC ~= AF.
  --------------------------------------------------------------------

  have hAC_AF :
      Geo.Congruent Q.A Q.C Q.A Q.F :=
    hilbert_space_right_triangles_hypotenuse
      (Geo := Geo)
      Q.B Q.A Q.C
      Q.B Q.A Q.F
      hBAC
      hBAF
      hRightABC
      hRightABF
      hBA_BA
      hBC_BF

  --------------------------------------------------------------------
  -- AC ~= AH.
  --------------------------------------------------------------------

  have hAC_AH :
      Geo.Congruent Q.A Q.C Q.A Q.Hpt :=
    hilbert_space_right_triangles_hypotenuse
      (Geo := Geo)
      Q.B Q.A Q.C
      Q.D Q.A Q.Hpt
      hBAC
      hDAH
      hRightABC
      hRightADH
      hBA_DA
      hBC_DH

  --------------------------------------------------------------------
  -- Vertical outer edges BF and DH are perpendicular to the base.
  --------------------------------------------------------------------

  rcases
      Q.vertical_edges_perpendicular_to_base
        (Geo := Geo) with
    ⟨lineBF, lineDH,
     hBbf, hFbf,
     hDdh, hHdh,
     hPerpBF,
     hPerpDH⟩

  --------------------------------------------------------------------
  -- Base carrier BC and right angle C-B-F.
  --------------------------------------------------------------------

  have hBC :
      Ne Q.B Q.C := by
    intro h
    apply hBaseSquare.1.2.1
    exact Subtype.ext h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Q.B Q.C hBC with
    ⟨lineBC, hBbc, hCbc⟩

  have hBCpi :
      HilbertLineInPlane Geo lineBC Q.pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.B Q.C hBC
      lineBC hBbc hCbc
      Q.pi hBbase hCbase

  have hBF :
      Ne Q.B Q.F := by
    intro h
    apply hFrontSquare.1.2.1
    exact Subtype.ext h

  have hNormCBF :=
    hilbert_space_linePerpendicularPlane_right_angle_of_points
      (Geo := Geo)
      Q.pi
      lineBF lineBC
      Q.B Q.C Q.F
      hPerpBF
      hBCpi
      hBbc
      hCbc
      hFbf
      hBC.symm
      hBF.symm

  have hBCF :
      Not (PrimCollinear Geo Q.B Q.C Q.F) := by
    intro h
    exact
      hNormCBF.1
        (PrimCollinearSwap
          Geo Q.B Q.C Q.F h)

  have hRightCBF :
      HilbertRightAngle Geo Q.C Q.B Q.F :=
    hNormCBF.2

  --------------------------------------------------------------------
  -- AC ~= CF.
  --------------------------------------------------------------------

  have hAC_CF :
      Geo.Congruent Q.A Q.C Q.C Q.F :=
    hilbert_space_right_triangles_hypotenuse
      (Geo := Geo)
      Q.B Q.A Q.C
      Q.B Q.C Q.F
      hBAC
      hBCF
      hRightABC
      hRightCBF
      hBA_BC
      hBC_BF

  --------------------------------------------------------------------
  -- Base carrier DC and right angle C-D-H.
  --------------------------------------------------------------------

  have hCD :
      Ne Q.C Q.D := by
    intro h
    apply hBaseSquare.1.1.2.1
    exact Subtype.ext h

  have hDC :
      Ne Q.D Q.C :=
    hCD.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Q.D Q.C hDC with
    ⟨lineDC, hDdc, hCdc⟩

  have hDCpi :
      HilbertLineInPlane Geo lineDC Q.pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.D Q.C hDC
      lineDC hDdc hCdc
      Q.pi hDbase hCbase

  have hDH :
      Ne Q.D Q.Hpt := by
    intro h
    apply hLeftSquare.1.2.1
    exact Subtype.ext h

  have hNormCDH :=
    hilbert_space_linePerpendicularPlane_right_angle_of_points
      (Geo := Geo)
      Q.pi
      lineDH lineDC
      Q.D Q.C Q.Hpt
      hPerpDH
      hDCpi
      hDdc
      hCdc
      hHdh
      hDC.symm
      hDH.symm

  have hDCH :
      Not (PrimCollinear Geo Q.D Q.C Q.Hpt) := by
    intro h
    exact
      hNormCDH.1
        (PrimCollinearSwap
          Geo Q.D Q.C Q.Hpt h)

  have hRightCDH :
      HilbertRightAngle Geo Q.C Q.D Q.Hpt :=
    hNormCDH.2

  --------------------------------------------------------------------
  -- AC ~= CH.
  --------------------------------------------------------------------

  have hAC_CH :
      Geo.Congruent Q.A Q.C Q.C Q.Hpt :=
    hilbert_space_right_triangles_hypotenuse
      (Geo := Geo)
      Q.B Q.A Q.C
      Q.D Q.C Q.Hpt
      hBAC
      hDCH
      hRightABC
      hRightCDH
      hBA_DC
      hBC_DH

  --------------------------------------------------------------------
  -- Final diagonal FH without constructing a top square.
  --
  -- First prove AB perpendicular to the whole left vertical plane.
  --------------------------------------------------------------------

  have hAB :
      Ne Q.A Q.B := by
    intro h
    apply hBaseSquare.1.1.1
    exact Subtype.ext h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Q.A Q.B hAB with
    ⟨lineAB, hAab, hBab⟩

  have hABpi :
      HilbertLineInPlane Geo lineAB Q.pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.A Q.B hAB
      lineAB hAab hBab
      Q.pi hAbase hBbase

  have hAD :
      Ne Q.A Q.D := by
    intro h
    apply hBaseSquare.1.2.2.1
    exact Subtype.ext h.symm

  rcases
      planePoint_line_through
        (Geo := Geo)
        Q.sigmaLeft Al Dl
        (by
          intro h
          apply hAD
          exact congrArg Subtype.val h) with
    ⟨lineADp, hAad, hDad⟩

  have hADpi :
      HilbertLineInPlane Geo lineADp.1 Q.pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.A Q.D hAD
      lineADp.1 hAad hDad
      Q.pi hAbase hDbase

  have hNormalInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      Q.normal

  have hAonNormal :
      H.OnLine Q.A Q.normalLine :=
    hNormalInc.1

  have hAE :
      Ne Q.A Q.E := by
    intro h
    apply Q.E_off_base
    rw [← h]
    exact hAbase

  have hNormalInLeft :
      HilbertLineInPlane
        Geo Q.normalLine Q.sigmaLeft :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.A Q.E hAE
      Q.normalLine
      hAonNormal Q.E_on_normal
      Q.sigmaLeft
      hAleft hEleft

  let normalLeft : PlaneLine Geo Q.sigmaLeft :=
    ⟨Q.normalLine, hNormalInLeft⟩

  let Aleft : PlanePoint Geo Q.sigmaLeft :=
    ⟨Q.A, hAleft⟩

  have hPerpNormalAD :
      HilbertLinesPerpendicularAt
        Geo Q.normalLine lineADp.1 Q.A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      Q.normal
      hADpi
      hAad

  have hAD_ne_normal :
      Ne lineADp.1 Q.normalLine := by
    have hNormal_ne_AD :
        Ne Q.normalLine lineADp.1 :=
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        Q.normalLine lineADp.1 Q.A
        hPerpNormalAD
    exact hNormal_ne_AD.symm

  have hADp_ne_normalLeft :
      Ne lineADp normalLeft := by
    intro h
    apply hAD_ne_normal
    exact congrArg Subtype.val h

  have hNonDAB :
      Not (PrimCollinear Geo Q.D Q.A Q.B) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      Q.pi Db Ab Bb
      hNCBase.1

  have hDA :
      Ne Q.D Q.A :=
    hAD.symm

  have hBA :
      Ne Q.B Q.A :=
    hAB.symm

  have hPerpAD_AB :
      HilbertLinesPerpendicularAt
        Geo lineADp.1 lineAB Q.A :=
    ⟨hAad, hAab,
     Q.D, Q.B,
     hDA, hBA,
     hDad, hBab,
     hNonDAB,
     hRightDAB⟩

  have hPerpAB_AD :
      HilbertLinesPerpendicularAt
        Geo lineAB lineADp.1 Q.A :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      lineADp.1 lineAB Q.A
      hPerpAD_AB

  have hPerpNormalAB :
      HilbertLinesPerpendicularAt
        Geo Q.normalLine lineAB Q.A :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      Q.normal
      hABpi
      hAab

  have hPerpAB_Normal :
      HilbertLinesPerpendicularAt
        Geo lineAB Q.normalLine Q.A :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      Q.normalLine lineAB Q.A
      hPerpNormalAB

  have hABperpLeft :
      HilbertLinePerpendicularPlaneAt
        Geo lineAB Q.sigmaLeft Q.A :=
    euclid_proposition_11_4
      (Geo := Geo)
      Q.sigmaLeft
      lineADp normalLeft
      lineAB
      Aleft
      hADp_ne_normalLeft
      hPerpAB_AD
      hPerpAB_Normal

  --------------------------------------------------------------------
  -- Front square gives AB || FE.  Convert to carrier parallelism and
  -- identify the AB carrier with the chosen base carrier lineAB.
  --------------------------------------------------------------------

  have hParallelAB_FE :
      (PlaneGeo Geo Q.sigmaFront).Parallel
        Af Bf Ff Ef :=
    hFrontSquare.1.1

  rcases
      hilbert_space_parallel_carriers_of_planeGeo_parallel
        (Geo := Geo)
        Q.sigmaFront
        Af Bf Ff Ef
        hParallelAB_FE with
    ⟨lineABfront, lineFE,
     hAabFront, hBabFront,
     hFfe, hEfe,
     hParallelABfront_FE⟩

  have hABfront_eq_AB :
      lineABfront = lineAB :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      Q.A Q.B hAB
      lineABfront lineAB
      hAabFront hBabFront
      hAab hBab

  have hParallelAB_FE_ambient :
      HilbertSpaceLinesParallel
        Geo lineAB lineFE := by
    rw [← hABfront_eq_AB]
    exact hParallelABfront_FE

  --------------------------------------------------------------------
  -- XI.8: FE is perpendicular to the left plane.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_8
        (Geo := Geo)
        lineAB lineFE
        Q.sigmaLeft
        Q.A
        hParallelAB_FE_ambient
        hABperpLeft with
    ⟨XFE, hFEperpLeftX⟩

  have hE_eq_XFE :
      Q.E = XFE :=
    hilbert_XI12_perpendicular_foot_unique
      (Geo := Geo)
      Q.sigmaLeft
      lineFE
      XFE Q.E
      hFEperpLeftX
      hEfe
      hEleft

  subst XFE

  have hFEperpLeft :
      HilbertLinePerpendicularPlaneAt
        Geo lineFE Q.sigmaLeft Q.E :=
    hFEperpLeftX

  --------------------------------------------------------------------
  -- EH lies in the left plane, hence FE perpendicular EH at E.
  --------------------------------------------------------------------

  have hHE :
      Ne Q.Hpt Q.E := by
    intro h
    apply hLeftSquare.1.1.2.1
    exact Subtype.ext h

  have hEH :
      Ne Q.E Q.Hpt :=
    hHE.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Q.E Q.Hpt hEH with
    ⟨lineEH, hEeh, hHeh⟩

  have hEHleft :
      HilbertLineInPlane
        Geo lineEH Q.sigmaLeft :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.E Q.Hpt hEH
      lineEH hEeh hHeh
      Q.sigmaLeft
      hEleft hHleft

  have hPerpFE_EH :
      HilbertLinesPerpendicularAt
        Geo lineFE lineEH Q.E :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hFEperpLeft
      hEHleft
      hEeh

  have hFE :
      Ne Q.F Q.E := by
    intro h
    apply hFrontSquare.1.1.2.1
    exact Subtype.ext h

  have hNormFEH :=
    hilbert_space_linesPerpendicularAt_right_angle_of_points
      (Geo := Geo)
      lineFE lineEH
      Q.E Q.F Q.Hpt
      hPerpFE_EH
      hFE
      hHE
      hFfe
      hHeh

  have hFEH :
      Not (PrimCollinear Geo Q.F Q.E Q.Hpt) :=
    hNormFEH.1

  have hRightFEH :
      HilbertRightAngle Geo Q.F Q.E Q.Hpt :=
    hNormFEH.2

  --------------------------------------------------------------------
  -- AC ~= FH.
  --------------------------------------------------------------------

  have hAC_FH :
      Geo.Congruent Q.A Q.C Q.F Q.Hpt :=
    hilbert_space_right_triangles_hypotenuse
      (Geo := Geo)
      Q.B Q.A Q.C
      Q.E Q.F Q.Hpt
      hBAC
      (by
        intro h
        exact
          hFEH
            (PrimCollinearSwap
              Geo Q.E Q.F Q.Hpt h))
      hRightABC
      hRightFEH
      hBA_EF
      hBC_EH

  --------------------------------------------------------------------
  -- Orient all five conclusions as edge ~= AC.
  --------------------------------------------------------------------

  exact
    ⟨hilbert_space_congruent_symmetry_all
        (Geo := Geo)
        Q.A Q.C
        Q.A Q.F
        hAC_AF,
     hilbert_space_congruent_symmetry_all
        (Geo := Geo)
        Q.A Q.C
        Q.A Q.Hpt
        hAC_AH,
     hilbert_space_congruent_symmetry_all
        (Geo := Geo)
        Q.A Q.C
        Q.C Q.F
        hAC_CF,
     hilbert_space_congruent_symmetry_all
        (Geo := Geo)
        Q.A Q.C
        Q.C Q.Hpt
        hAC_CH,
     hilbert_space_congruent_symmetry_all
        (Geo := Geo)
        Q.A Q.C
        Q.F Q.Hpt
        hAC_FH⟩


end HilbertThreeSquareCorner3D

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Noncoplanarity of the alternating regular tetrahedron.

The key new result is purely planar:

> four points in a Hilbert plane cannot have all six mutual segments
> congruent to one nondegenerate reference edge.

Proof:
* same-side case: Euclid I.7;
* opposite-side case: the segment joining the two apexes crosses the
  base line.  At one endpoint of the base, one equilateral angle is
  therefore strictly inside another angle which SSS proves congruent
  to it, contradicting irreflexivity of strict angle comparison.

This planar obstruction is then applied inside a hypothetical plane
containing the four alternating vertices A,C,F,H.
-/


/--
There are no four planar points whose six mutual segments are all
congruent to the nondegenerate base `AB`.

The source triangle `ABC` is assumed noncollinear only to certify that
the common edge is nondegenerate and to orient the planar side
arguments.
-/
theorem hilbert_no_four_pairwise_equal_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hAC_AB :
      Geo.Congruent A C A B)
    (hAD_AB :
      Geo.Congruent A D A B)
    (hBC_AB :
      Geo.Congruent B C A B)
    (hBD_AB :
      Geo.Congruent B D A B)
    (hCD_AB :
      Geo.Congruent C D A B) :
    False := by

  --------------------------------------------------------------------
  -- Base nondegeneracy.
  --------------------------------------------------------------------

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨base, hAbase, hBbase⟩

  --------------------------------------------------------------------
  -- Congruences needed for SSS on ABC and ABD.
  --------------------------------------------------------------------

  have hAB_AB :
      Geo.Congruent A B A B :=
    hilbert_congruent_reflexive
      Geo A B

  have hAB_AC :
      Geo.Congruent A B A C :=
    hilbert_congruent_symmetry
      Geo A C A B hAC_AB

  have hAB_AD :
      Geo.Congruent A B A D :=
    hilbert_congruent_symmetry
      Geo A D A B hAD_AB

  have hAB_BC :
      Geo.Congruent A B B C :=
    hilbert_congruent_symmetry
      Geo B C A B hBC_AB

  have hAB_BD :
      Geo.Congruent A B B D :=
    hilbert_congruent_symmetry
      Geo B D A B hBD_AB

  have hAB_CD :
      Geo.Congruent A B C D :=
    hilbert_congruent_symmetry
      Geo C D A B hCD_AB

  have hAC_AD :
      Geo.Congruent A C A D :=
    hilbert_congruent_transitivity
      Geo
      A C
      A B
      A D
      hAC_AB
      hAB_AD

  have hBC_BD :
      Geo.Congruent B C B D :=
    hilbert_congruent_transitivity
      Geo
      B C
      A B
      B D
      hBC_AB
      hAB_BD

  --------------------------------------------------------------------
  -- SSS also proves that ABD is nondegenerate.
  --------------------------------------------------------------------

  have hSSS_AB :=
    HilbertSSS
      Geo
      A B C
      A B D
      hABC
      hAB_AB
      hBC_BD
      hAC_AD

  have hABD :
      Not (PrimCollinear Geo A B D) :=
    hSSS_AB.1

  --------------------------------------------------------------------
  -- C and D lie off the base line AB.
  --------------------------------------------------------------------

  have hCoff :
      Not (HilbertIncidence.OnLine C base) := by
    intro hCbase
    exact
      hABC
        ⟨base,
         hAbase,
         hBbase,
         hCbase⟩

  have hDoff :
      Not (HilbertIncidence.OnLine D base) := by
    intro hDbase
    exact
      hABD
        ⟨base,
         hAbase,
         hBbase,
         hDbase⟩

  --------------------------------------------------------------------
  -- C and D are distinct because CD is congruent to nonzero AB.
  --------------------------------------------------------------------

  have hCD :
      Ne C D :=
    bookZero_nullSegment3
      Geo
      A B C D
      hAB
      hAB_CD

  --------------------------------------------------------------------
  -- First case: C and D on the same side of AB.
  -- Euclid I.7 forces C = D.
  --------------------------------------------------------------------

  by_cases hSame :
      HilbertSameSide Geo C D base

  · have hEq :
        C = D :=
      euclid_proposition_7
        Geo
        A B C D
        base
        hAB
        hAbase
        hBbase
        hSame
        hAC_AD
        hBC_BD

    exact
      hCD hEq

  --------------------------------------------------------------------
  -- Second case: C and D lie on opposite sides of AB.
  --------------------------------------------------------------------

  · have hOpp :
        HilbertOppositeSide Geo C D base :=
      hilbert_oppositeSide_of_not_sameSide
        Geo
        C D base
        hCoff
        hDoff
        hSame

    rcases hOpp.2.2 with
      ⟨P, hCPD, hPbase⟩

    ------------------------------------------------------------------
    -- The crossing point P lies on at least one of the two base rays:
    --
    --   ray A B
    -- or
    --   ray B A.
    ------------------------------------------------------------------

    have hRayCover :
        HilbertSameRay Geo A B P ∨
        HilbertSameRay Geo B A P := by

      by_cases hPA :
          P = A

      · subst P
        exact
          Or.inr
            (hilbert_sameRay_refl
              Geo B A hAB)

      · by_cases hPB :
          P = B

        · subst P
          exact
            Or.inl
              (hilbert_sameRay_refl
                Geo A B hAB.symm)

        · have hAP :
              Ne A P := by
            intro h
            exact hPA h.symm

          have hPBne :
              Ne P B :=
            hPB

          have hAPBcol :
              PrimCollinear Geo A P B :=
            ⟨base,
             hAbase,
             hPbase,
             hBbase⟩

          rcases
              hilbert_between_trichotomy
                Geo
                A P B
                hAP
                hPBne
                hAB
                hAPBcol with
            hAPB | hPAB | hABP

          · have hRayAPB :
                HilbertSameRay Geo A P B :=
              hilbert_sameRay_of_between
                Geo A P B hAPB

            exact
              Or.inl
                (hilbert_sameRay_symm
                  Geo A P B hRayAPB)

          · have hBAP :
                Geo.Between B A P :=
              (HilbertOrder.between_incidence
                P A B hPAB).2.2.2.2

            exact
              Or.inr
                (hilbert_sameRay_of_between
                  Geo B A P hBAP)

          · exact
              Or.inl
                (hilbert_sameRay_of_between
                  Geo A B P hABP)

    ------------------------------------------------------------------
    -- Prepare SSS angle equality at A:
    --
    --   angle C A B ~= angle C A D.
    ------------------------------------------------------------------

    have hACB :
        Not (PrimCollinear Geo A C B) := by
      intro h
      exact
        hABC
          (PrimCollinearRotate
            Geo A C B h)

    have hAC_AC :
        Geo.Congruent A C A C :=
      hilbert_congruent_reflexive
        Geo A C

    have hCB_AB :
        Geo.Congruent C B A B :=
      CongruentReverseFirst
        Geo
        B C A B
        hBC_AB

    have hCB_CD :
        Geo.Congruent C B C D :=
      hilbert_congruent_transitivity
        Geo
        C B
        A B
        C D
        hCB_AB
        hAB_CD

    have hSSS_A :=
      HilbertSSS
        Geo
        A C B
        A C D
        hACB
        hAC_AC
        hCB_CD
        hAB_AD

    have hACD :
        Not (PrimCollinear Geo A C D) :=
      hSSS_A.1

    have hAngleA :
        Geo.AngleCongruent
          C A B
          C A D :=
      hSSS_A.2.angleA

    have hCAB :
        Not (PrimCollinear Geo C A B) := by
      intro h
      exact
        hABC
          (PrimCollinearCycle
            Geo C A B h)

    have hCAD :
        Not (PrimCollinear Geo C A D) := by
      intro h
      exact
        hACD
          (PrimCollinearSwap
            Geo C A D h)

    ------------------------------------------------------------------
    -- Prepare SSS angle equality at B:
    --
    --   angle C B A ~= angle C B D.
    ------------------------------------------------------------------

    have hBCA :
        Not (PrimCollinear Geo B C A) := by
      intro h
      exact
        hABC
          (PrimCollinearCycle
            Geo C A B
            (PrimCollinearCycle
              Geo B C A h))

    have hBC_BC :
        Geo.Congruent B C B C :=
      hilbert_congruent_reflexive
        Geo B C

    have hCA_AB :
        Geo.Congruent C A A B :=
      CongruentReverseFirst
        Geo
        A C A B
        hAC_AB

    have hCA_CD :
        Geo.Congruent C A C D :=
      hilbert_congruent_transitivity
        Geo
        C A
        A B
        C D
        hCA_AB
        hAB_CD

    have hBA_AB :
        Geo.Congruent B A A B :=
      CongruentReverseFirst
        Geo
        A B A B
        hAB_AB

    have hBA_BD :
        Geo.Congruent B A B D :=
      hilbert_congruent_transitivity
        Geo
        B A
        A B
        B D
        hBA_AB
        hAB_BD

    have hSSS_B :=
      HilbertSSS
        Geo
        B C A
        B C D
        hBCA
        hBC_BC
        hCA_CD
        hBA_BD

    have hBCD :
        Not (PrimCollinear Geo B C D) :=
      hSSS_B.1

    have hAngleB :
        Geo.AngleCongruent
          C B A
          C B D :=
      hSSS_B.2.angleA

    have hCBA :
        Not (PrimCollinear Geo C B A) := by
      intro h
      exact
        hABC
          (PrimCollinearSymm
            Geo C B A h)

    have hCBD :
        Not (PrimCollinear Geo C B D) := by
      intro h
      exact
        hBCD
          (PrimCollinearSwap
            Geo C B D h)

    ------------------------------------------------------------------
    -- Whichever base ray contains P gives a strict angle contained
    -- in a congruent angle, hence angle < itself.
    ------------------------------------------------------------------

    rcases hRayCover with
      hRayABP | hRayBAP

    · have hInsideA :
          HilbertRayMeetsSegment
            Geo A B C D :=
        ⟨P, hCPD, hRayABP⟩

      have hReflA :
          Geo.AngleCongruent
            C A B
            C A B :=
        HilbertCongruence.angle_congruence_reflexive
          (Geo := Geo)
          C A B
          hCAB

      have hLessA :
          HilbertAngleLess
            Geo
            C A B
            C A D :=
        hilbert_angleLess_intro
          Geo
          C A B
          C A D
          B
          hCAB
          hCAD
          hInsideA
          hReflA

      have hAngleASymm :
          Geo.AngleCongruent
            C A D
            C A B :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C A B
          C A D
          hAngleA

      have hSelf :
          HilbertAngleLess
            Geo
            C A B
            C A B :=
        hilbert_angleLess_transport_right
          Geo
          C A B
          C A D
          C A B
          hLessA
          hCAB
          hAngleASymm

      exact
        (hilbert_angleLess_irrefl
          Geo C A B)
          hSelf

    · have hInsideB :
          HilbertRayMeetsSegment
            Geo B A C D :=
        ⟨P, hCPD, hRayBAP⟩

      have hReflB :
          Geo.AngleCongruent
            C B A
            C B A :=
        HilbertCongruence.angle_congruence_reflexive
          (Geo := Geo)
          C B A
          hCBA

      have hLessB :
          HilbertAngleLess
            Geo
            C B A
            C B D :=
        hilbert_angleLess_intro
          Geo
          C B A
          C B D
          A
          hCBA
          hCBD
          hInsideB
          hReflB

      have hAngleBSymm :
          Geo.AngleCongruent
            C B D
            C B A :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C B A
          C B D
          hAngleB

      have hSelf :
          HilbertAngleLess
            Geo
            C B A
            C B A :=
        hilbert_angleLess_transport_right
          Geo
          C B A
          C B D
          C B A
          hLessB
          hCBA
          hAngleBSymm

      exact
        (hilbert_angleLess_irrefl
          Geo C B A)
          hSelf


namespace HilbertThreeSquareCorner3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/--
The four alternating vertices `A,C,F,H` of the three-square corner are
not coplanar.
-/
theorem alternating_noncoplanar
    (Q : HilbertThreeSquareCorner3D Geo) :
    Not
      (HilbertCoplanar4
        Geo
        Q.A Q.C Q.F Q.Hpt) := by

  --------------------------------------------------------------------
  -- A,C lie in the base plane; F is outside it.
  --------------------------------------------------------------------

  rcases Q.base with
    ⟨hAbase, hBbase, hCbase, hDbase, hBaseSquare⟩

  rcases Q.front with
    ⟨_hAfront, hBfront, hFfront, _hEfront, hFrontSquare⟩

  let Ab : PlanePoint Geo Q.pi :=
    ⟨Q.A, hAbase⟩

  let Bb : PlanePoint Geo Q.pi :=
    ⟨Q.B, hBbase⟩

  let Cb : PlanePoint Geo Q.pi :=
    ⟨Q.C, hCbase⟩

  let Db : PlanePoint Geo Q.pi :=
    ⟨Q.D, hDbase⟩

  have hNCBase :=
    parallelogram_vertices_noncollinear
      (PlaneGeo Geo Q.pi)
      Ab Bb Cb Db
      hBaseSquare.1

  have hABCBase :
      Not (PrimCollinear Geo Q.A Q.B Q.C) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      Q.pi
      Ab Bb Cb
      hNCBase.2.1

  have hACBBase :
      Not (PrimCollinear Geo Q.A Q.C Q.B) := by
    intro h
    exact
      hABCBase
        (PrimCollinearRotate
          Geo Q.A Q.C Q.B h)

  have hAC :
      Ne Q.A Q.C :=
    hilbert_noncollinear_ne_first
      Geo
      Q.A Q.C Q.B
      hACBBase

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Q.A Q.C hAC with
    ⟨lineAC, hAac, hCac⟩

  have hACpi :
      HilbertLineInPlane
        Geo lineAC Q.pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Q.A Q.C hAC
      lineAC hAac hCac
      Q.pi
      hAbase hCbase

  rcases
      Q.vertical_edges_perpendicular_to_base
        (Geo := Geo) with
    ⟨lineBF, _lineDH,
     hBbf, hFbf,
     _hDdh, _hHdh,
     hPerpBF, _hPerpDH⟩

  have hBF :
      Ne Q.B Q.F := by
    intro h
    apply hFrontSquare.1.2.1
    exact
      Subtype.ext h

  have hFoff :
      Not (S.OnPlane Q.F Q.pi) := by
    intro hFpi

    have hF_eq_B :
        Q.F = Q.B :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        Q.pi
        lineBF
        Q.B Q.F
        hPerpBF
        hFbf
        hFpi

    exact
      hBF hF_eq_B.symm

  have hACF :
      Not (PrimCollinear Geo Q.A Q.C Q.F) := by
    intro hCol

    have hFac :
        H.OnLine Q.F lineAC :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAC
        hAac
        hCac
        hCol

    exact
      hFoff
        (hACpi Q.F hFac)

  --------------------------------------------------------------------
  -- Assume all four alternating vertices lie in one plane rho.
  --------------------------------------------------------------------

  intro hCop

  rcases hCop with
    ⟨rho,
     hArho,
     hCrho,
     hFrho,
     hHrho⟩

  let Ar : PlanePoint Geo rho :=
    ⟨Q.A, hArho⟩

  let Cr : PlanePoint Geo rho :=
    ⟨Q.C, hCrho⟩

  let Fr : PlanePoint Geo rho :=
    ⟨Q.F, hFrho⟩

  let Hr : PlanePoint Geo rho :=
    ⟨Q.Hpt, hHrho⟩

  have hACFPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo rho)
          Ar Cr Fr) := by
    intro hCol
    exact
      hACF
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          rho
          Ar Cr Fr
          hCol)

  --------------------------------------------------------------------
  -- All five nonreference edges are congruent to AC.
  --------------------------------------------------------------------

  have hEdges :=
    Q.alternating_edges_congruent
      (Geo := Geo)

  have hAF_AC :
      Geo.Congruent
        Q.A Q.F
        Q.A Q.C :=
    hEdges.1

  have hAH_AC :
      Geo.Congruent
        Q.A Q.Hpt
        Q.A Q.C :=
    hEdges.2.1

  have hCF_AC :
      Geo.Congruent
        Q.C Q.F
        Q.A Q.C :=
    hEdges.2.2.1

  have hCH_AC :
      Geo.Congruent
        Q.C Q.Hpt
        Q.A Q.C :=
    hEdges.2.2.2.1

  have hFH_AC :
      Geo.Congruent
        Q.F Q.Hpt
        Q.A Q.C :=
    hEdges.2.2.2.2

  have hAFPlane :
      (PlaneGeo Geo rho).Congruent
        Ar Fr Ar Cr :=
    (planeGeo_congruent
      (Geo := Geo)
      rho
      Ar Fr Ar Cr).mpr
      hAF_AC

  have hAHPlane :
      (PlaneGeo Geo rho).Congruent
        Ar Hr Ar Cr :=
    (planeGeo_congruent
      (Geo := Geo)
      rho
      Ar Hr Ar Cr).mpr
      hAH_AC

  have hCFPlane :
      (PlaneGeo Geo rho).Congruent
        Cr Fr Ar Cr :=
    (planeGeo_congruent
      (Geo := Geo)
      rho
      Cr Fr Ar Cr).mpr
      hCF_AC

  have hCHPlane :
      (PlaneGeo Geo rho).Congruent
        Cr Hr Ar Cr :=
    (planeGeo_congruent
      (Geo := Geo)
      rho
      Cr Hr Ar Cr).mpr
      hCH_AC

  have hFHPlane :
      (PlaneGeo Geo rho).Congruent
        Fr Hr Ar Cr :=
    (planeGeo_congruent
      (Geo := Geo)
      rho
      Fr Hr Ar Cr).mpr
      hFH_AC

  --------------------------------------------------------------------
  -- Contradiction with the planar four-equal-points theorem.
  --------------------------------------------------------------------

  exact
    hilbert_no_four_pairwise_equal_points
      (PlaneGeo Geo rho)
      Ar Cr Fr Hr
      hACFPlane
      hAFPlane
      hAHPlane
      hCFPlane
      hCHPlane
      hFHPlane


end HilbertThreeSquareCorner3D

end Geometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coxeter A3 existence - derived spatial layer

Final assembly of the synthetic existence chain:

    three-square corner
      -> regular tetrahedron
      -> Coxeter A3 tetrahedral frame.

All geometric work has already been completed in tests 08--14.
This file only packages the established noncoplanarity and the five
edge-congruence statements into the production structures.
-/


namespace HilbertThreeSquareCorner3D

variable
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]


/--
The alternating vertices `A,C,F,H` of a three-square corner form a
regular tetrahedron.
-/
def toRegularTetrahedron
    (Q : HilbertThreeSquareCorner3D Geo) :
    HilbertRegularTetrahedron3D Geo := by

  have hNoncoplanar :
      Not
        (HilbertCoplanar4
          Geo
          Q.A Q.C Q.F Q.Hpt) :=
    Q.alternating_noncoplanar
      (Geo := Geo)

  have hEdges :=
    Q.alternating_edges_congruent
      (Geo := Geo)

  exact
    {
      A := Q.A
      B := Q.C
      C := Q.F
      D := Q.Hpt

      noncoplanar := hNoncoplanar

      AC_eq_AB := hEdges.1
      AD_eq_AB := hEdges.2.1
      BC_eq_AB := hEdges.2.2.1
      BD_eq_AB := hEdges.2.2.2.1
      CD_eq_AB := hEdges.2.2.2.2
    }


end HilbertThreeSquareCorner3D


/--
A regular tetrahedron exists synthetically in the present Hilbert
3-space interface.
-/
theorem hilbert_regular_tetrahedron3D_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo] :
    Nonempty (HilbertRegularTetrahedron3D Geo) := by

  rcases
      hilbert_three_square_corner_exists
        (Geo := Geo) with
    ⟨Q⟩

  exact
    ⟨Q.toRegularTetrahedron
      (Geo := Geo)⟩


/--
A Coxeter A3 tetrahedral frame exists.

This is the final existence statement needed by the already completed
3D Coxeter-relation layer.
-/
theorem coxeter_A3_tetrahedral_frame_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo] :
    Nonempty (CoxeterA3TetrahedralFrame Geo) := by

  rcases
      hilbert_regular_tetrahedron3D_exists
        (Geo := Geo) with
    ⟨T⟩

  exact
    ⟨T.toCoxeterA3TetrahedralFrame
      (Geo := Geo)⟩


end Geometry

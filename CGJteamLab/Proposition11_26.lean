import CGJteamLab.HilbertInterfaceXI
import CGJteamLab.Proposition11_11
import CGJteamLab.Proposition11_12

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/--
Local recovery helper for XI.26.

A plane contains three noncollinear points, so at least one of them lies
off any prescribed line.
-/
private theorem hilbert_XI26_point_off_line_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (sigma : S.Plane)
    (l : Geo.Line) :
    exists T : Geo.Point,
      S.OnPlane T sigma /\ Not (Hinc.OnLine T l) := by
  classical
  rcases
      hilbert_three_noncollinear_on_plane
        (Geo := Geo) sigma
    with
    ⟨P, Q, R, hPsigma, hQsigma, hRsigma, hPQR⟩

  by_cases hPl : Hinc.OnLine P l
  · by_cases hQl : Hinc.OnLine Q l
    · refine ⟨R, hRsigma, ?_⟩
      intro hRl
      exact hPQR ⟨l, hPl, hQl, hRl⟩
    · exact ⟨Q, hQsigma, hQl⟩
  · exact ⟨P, hPsigma, hPl⟩


/-!
# Euclid XI.26

Complete synthetic Hilbert reconstruction of Euclid XI.26.

The proof proceeds by:

1. copying the proper base triangle D,E,C at the prescribed ray AB;
2. projecting the fourth source point F orthogonally to the base plane;
3. classifying the projection foot G relative to the two base rays;
4. constructing the corresponding copied base point K in each position;
5. copying the normal height and recovering the three target face angles
   by spatial right-angle, SAS, SSS, and Hilbert-T15 arguments.

The proposition-specific construction and case analysis remain in this
module. Proposition-independent spatial and planar helpers developed during
the proof have been promoted to `HilbertInterfaceXI`.

No `Proposition11_26_test*` module is imported, and XI.26 no longer depends
on `Proposition11_23`.
-/

/--
The base-triangle data actually produced by the first construction.
The source triangle is D,E,C; its copy is A,B0,L. The prescribed ray
is AB, so B0 is auxiliary and B need not have the length DE from A.
-/
structure HilbertXI26BaseCopy
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (sigma : S.Plane)
    (D E C A B B0 L : Geo.Point) : Prop where
  A_on : S.OnPlane A sigma
  B_on : S.OnPlane B sigma
  B0_on : S.OnPlane B0 sigma
  L_on : S.OnPlane L sigma
  first_ray : HilbertSameRay Geo A B B0
  first_side : Geo.Congruent D E A B0
  second_side : Geo.Congruent D C A L
  third_side : Geo.Congruent E C B0 L
  base_proper : Not (PrimCollinear Geo B A L)
  copy_proper : Not (PrimCollinear Geo B0 A L)
  base_angle : Geo.AngleCongruent B A L E D C
  copy_angle : Geo.AngleCongruent B0 A L E D C


/--
Copy the source base triangle into a prescribed plane along a prescribed
ray. This is an existence theorem, using spatial III.1 and III.4 followed
by the derived spatial SAS theorem.
-/
theorem hilbert_XI26_copy_base_triangle_in_plane
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (D E C A B : Geo.Point)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hAB : Ne A B)
    (hAsigma : S.OnPlane A sigma)
    (hBsigma : S.OnPlane B sigma) :
    exists B0 L : Geo.Point,
      HilbertXI26BaseCopy Geo sigma D E C A B B0 L := by

  have hXI26Data2 :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo) A B hAB
  cases hXI26Data2
  rename_i base hXI26Data2Rest1
  cases hXI26Data2Rest1
  rename_i hAbase hBbase

  have hBaseSigma : HilbertLineInPlane Geo base sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB base hAbase hBbase sigma hAsigma hBsigma

  have hXI26Data3 :=
      hilbert_XI26_point_off_line_in_plane
        (Geo := Geo) sigma base
  cases hXI26Data3
  rename_i T hXI26Data3Rest1
  cases hXI26Data3Rest1
  rename_i hTsigma hTbase

  have hXI26Data4 :=
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        E D C B A T hEDC hAB.symm
        sigma base hBaseSigma hBbase hAbase hTsigma hTbase
  cases hXI26Data4
  rename_i X hXI26Data4Rest1
  cases hXI26Data4Rest1
  rename_i hXside hXI26Data4Rest2
  cases hXI26Data4Rest2
  rename_i hEDC_BAX _hUniqueRay

  have hXsigma : S.OnPlane X sigma := hXside.1
  have hXbase : Not (Hinc.OnLine X base) := hXside.2.2.1

  have hBAX : Not (PrimCollinear Geo B A X) := by
    intro hCol
    apply hXbase
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo) hAB hAbase hBbase
        (PrimCollinearSwap Geo B A X hCol)

  have hAX : Ne A X := by
    intro hEq
    apply hXbase
    rw [hEq] at hAbase
    exact hAbase

  have hXI26Data5 :=
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo) D E A B hAB
  cases hXI26Data5
  rename_i B0 hXI26Data5Rest1
  cases hXI26Data5Rest1
  rename_i hRayB0 hAB0_DE

  have hXI26Data6 :=
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo) D C A X hAX
  cases hXI26Data6
  rename_i L hXI26Data6Rest1
  cases hXI26Data6Rest1
  rename_i hRayL hAL_DC

  have hB0sigma : S.OnPlane B0 sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A B B0 hAB hAsigma hBsigma hRayB0.2.2.1

  have hLsigma : S.OnPlane L sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A X L hAX hAsigma hXsigma hRayL.2.2.1

  let Ap : PlanePoint Geo sigma := Subtype.mk A hAsigma
  let Bp : PlanePoint Geo sigma := Subtype.mk B hBsigma
  let Xp : PlanePoint Geo sigma := Subtype.mk X hXsigma
  let B0p : PlanePoint Geo sigma := Subtype.mk B0 hB0sigma
  let Lp : PlanePoint Geo sigma := Subtype.mk L hLsigma

  have hBAXPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Bp Ap Xp) := by
    intro hCol
    apply hBAX
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma Bp Ap Xp hCol
    simpa [Bp, Ap, Xp] using hAmbient

  have hRayB0Plane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Bp B0p := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Bp B0p).mpr
    simpa [Ap, Bp, B0p] using hRayB0

  have hRayLPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Xp Lp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Xp Lp).mpr
    simpa [Ap, Xp, Lp] using hRayL

  have hRayBB : HilbertSameRay Geo A B B := by
    refine And.intro hAB.symm (And.intro hAB.symm (And.intro ?hCol ?hNotBetween))
    case hCol =>
      exact Exists.intro base (And.intro hAbase (And.intro hBbase hBbase))
    case hNotBetween =>
      intro hBetween
      exact
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo) B A B hBetween).2.2.1 rfl

  have hRayBBPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Bp Bp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Bp Bp).mpr
    simpa [Ap, Bp] using hRayBB

  have hB0ALPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) B0p Ap Lp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      Bp Ap Xp B0p Lp hBAXPlane hRayB0Plane hRayLPlane

  have hBALPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Bp Ap Lp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      Bp Ap Xp Bp Lp hBAXPlane hRayBBPlane hRayLPlane

  have hB0AL : Not (PrimCollinear Geo B0 A L) := by
    have hAmbient :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo) sigma B0p Ap Lp hB0ALPlane
    simpa [B0p, Ap, Lp] using hAmbient

  have hBAL : Not (PrimCollinear Geo B A L) := by
    have hAmbient :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo) sigma Bp Ap Lp hBALPlane
    simpa [Bp, Ap, Lp] using hAmbient

  have hMoveCopy : Geo.AngleCongruent B A X B0 A L :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma B A X B0 L
      hBsigma hAsigma hXsigma hB0sigma hLsigma
      hBAX hRayB0 hRayL

  have hMoveBase : Geo.AngleCongruent B A X B A L :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma B A X B L
      hBsigma hAsigma hXsigma hBsigma hLsigma
      hBAX hRayBB hRayL

  have hEDC_B0AL : Geo.AngleCongruent E D C B0 A L :=
    Geometry.Geo.angle_congruent_transitivity
      Geo E D C B A X B0 A L hEDC_BAX hMoveCopy

  have hEDC_BAL : Geo.AngleCongruent E D C B A L :=
    Geometry.Geo.angle_congruent_transitivity
      Geo E D C B A X B A L hEDC_BAX hMoveBase

  have hDE_AB0 : Geo.Congruent D E A B0 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) A B0 D E hRayB0.2.1.symm hAB0_DE

  have hDC_AL : Geo.Congruent D C A L :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) A L D C hRayL.2.1.symm hAL_DC

  have hDEC : Not (PrimCollinear Geo D E C) := by
    intro hCol
    exact hEDC (PrimCollinearSwap Geo D E C hCol)

  have hAB0LPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Ap B0p Lp) := by
    intro hCol
    exact
      hB0ALPlane
        (PrimCollinearSwap (PlaneGeo Geo sigma) Ap B0p Lp hCol)

  have hSAS :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma D E C Ap B0p Lp
      hDEC hAB0LPlane hDE_AB0 hDC_AL hEDC_B0AL

  have hEC_B0L : Geo.Congruent E C B0 L := by
    simpa [Ap, B0p, Lp] using hSAS.1

  refine Exists.intro B0 (Exists.intro L ?_)
  exact
    { A_on := hAsigma
      B_on := hBsigma
      B0_on := hB0sigma
      L_on := hLsigma
      first_ray := hRayB0
      first_side := hDE_AB0
      second_side := hDC_AL
      third_side := hEC_B0L
      base_proper := hBAL
      copy_proper := hB0AL
      base_angle :=
        Geometry.Geo.angle_congruent_symmetry
          Geo E D C B A L hEDC_BAL
      copy_angle :=
        Geometry.Geo.angle_congruent_symmetry
          Geo E D C B0 A L hEDC_B0AL }


/--
The prescribed ray alone suffices: first construct a plane containing
it, then apply the preceding base-triangle construction.
-/
theorem hilbert_XI26_copy_base_triangle_on_ray
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (D E C A B : Geo.Point)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hAB : Ne A B) :
    exists sigma : S.Plane,
      exists B0 L : Geo.Point,
        HilbertXI26BaseCopy Geo sigma D E C A B B0 L := by

  have hXI26Data7 :=
      HilbertSpaceIncidence.plane_through
        (Geo := Geo) E D C hEDC
  cases hXI26Data7
  rename_i rho hXI26Data7Rest1
  cases hXI26Data7Rest1
  rename_i _hErho hXI26Data7Rest2
  cases hXI26Data7Rest2
  rename_i _hDrho _hCrho

  have hXI26Data8 :=
      HilbertPlaneIncidence.line_through
        (Geo := Geo) A B hAB
  cases hXI26Data8
  rename_i base hXI26Data8Rest1
  cases hXI26Data8Rest1
  rename_i hAbase hBbase

  have hXI26Data9 :=
      hilbert_XI26_point_off_line_in_plane
        (Geo := Geo) rho base
  cases hXI26Data9
  rename_i T hXI26Data9Rest1
  cases hXI26Data9Rest1
  rename_i _hTrho hTbase

  have hABT : Not (PrimCollinear Geo A B T) := by
    intro hCol
    apply hTbase
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo) hAB hAbase hBbase hCol

  have hXI26Data10 :=
      HilbertSpaceIncidence.plane_through
        (Geo := Geo) A B T hABT
  cases hXI26Data10
  rename_i sigma hXI26Data10Rest1
  cases hXI26Data10Rest1
  rename_i hAsigma hXI26Data10Rest2
  cases hXI26Data10Rest2
  rename_i hBsigma _hTsigma

  have hXI26Data11 :=
      hilbert_XI26_copy_base_triangle_in_plane
        (Geo := Geo) sigma D E C A B hEDC hAB hAsigma hBsigma
  cases hXI26Data11
  rename_i B0 hXI26Data11Rest1
  cases hXI26Data11Rest1
  rename_i L hCopy
  exact Exists.intro sigma (Exists.intro B0 (Exists.intro L hCopy))


/--
The original trihedron supplies Euclid's source projection. The foot G
may be D, may lie on either base line, or may be outside the base angle.
None of these possibilities is excluded in this statement.
-/
theorem hilbert_XI26_source_projection
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F) :
    exists pi : S.Plane,
      exists normal : Geo.Line,
        exists G : Geo.Point,
          S.OnPlane D pi /\
          S.OnPlane E pi /\
          S.OnPlane C pi /\
          Not (S.OnPlane F pi) /\
          Hinc.OnLine F normal /\
          S.OnPlane G pi /\
          Ne F G /\
          HilbertLinePerpendicularPlaneAt Geo normal pi G := by

  have hXI26Data12 :=
      HilbertSpaceIncidence.plane_through
        (Geo := Geo) E D C hTri.1
  cases hXI26Data12
  rename_i pi hXI26Data12Rest1
  cases hXI26Data12Rest1
  rename_i hEpi hXI26Data12Rest2
  cases hXI26Data12Rest2
  rename_i hDpi hCpi

  have hFpi : Not (S.OnPlane F pi) := by
    intro hOn
    exact hTri.2.2.2 (Exists.intro pi (And.intro hDpi (And.intro hEpi (And.intro hCpi hOn))))

  have hXI26Data13 :=
      euclid_proposition_11_11
        (Geo := Geo) pi F hFpi
  cases hXI26Data13
  rename_i normal hXI26Data13Rest1
  cases hXI26Data13Rest1
  rename_i G hXI26Data13Rest2
  cases hXI26Data13Rest2
  rename_i hFnormal hPerp

  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2

  have hFG : Ne F G := by
    intro hEq
    apply hFpi
    rw [hEq]
    exact hGpi

  exact
    Exists.intro pi (Exists.intro normal (Exists.intro G
      (And.intro hDpi (And.intro hEpi (And.intro hCpi
      (And.intro hFpi (And.intro hFnormal (And.intro hGpi
      (And.intro hFG hPerp)))))))))


/--
The geometric output of the interior-point construction. All three
distances to the base vertices are transported by proved congruences.
-/
structure HilbertXI26InteriorPointCopy
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (sigma : S.Plane)
    (D E C A B0 L G K : Geo.Point) : Prop where
  K_on : S.OnPlane K sigma
  source_ne : Ne D G
  target_ne : Ne A K
  interior_ray : HilbertRayMeetsSegment Geo A K B0 L
  radial : Geo.Congruent D G A K
  first_distance : Geo.Congruent E G B0 K
  second_distance : Geo.Congruent C G L K
  first_angle : Geo.AngleCongruent E D G B0 A K
  second_angle : Geo.AngleCongruent C D G L A K


/--
Extend the copied base by a point G whose ray DG is interior to EDC.

The existing simultaneous subangle transport fixes one target ray.
Laying off DG on that ray gives K. Two spatial SAS applications then
prove EG ~= B0K and CG ~= LK for this same K.
-/
theorem hilbert_XI26_copy_interior_point
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hInside : HilbertRayMeetsSegment Geo D G E C) :
    exists K : Geo.Point,
      HilbertXI26InteriorPointCopy Geo sigma D E C A B0 L G K := by

  have hSource :=
    hilbert_space_interior_ray_noncollinear
      (Geo := Geo) D E C G hEDC hInside
  have hDG : Ne D G := hSource.1
  have hEDG : Not (PrimCollinear Geo E D G) := hSource.2.1
  have hCDG : Not (PrimCollinear Geo C D G) := hSource.2.2

  have hWhole : Geo.AngleCongruent E D C B0 A L :=
    Geometry.Geo.angle_congruent_symmetry
      Geo B0 A L E D C hCopy.copy_angle

  have hConstruction :=
    hilbert_space_interior_subangle_transport_both_in_plane
      (Geo := Geo)
      sigma D E C G B0 A L
      hCopy.B0_on hCopy.A_on hCopy.L_on
      hEDC hCopy.copy_proper hInside hWhole
  cases hConstruction
  rename_i K0 hK0data

  have hK0sigma : S.OnPlane K0 sigma := hK0data.1
  have hInsideK0 : HilbertRayMeetsSegment Geo A K0 B0 L := hK0data.2.1
  have hCDG_LAK0 : Geo.AngleCongruent C D G L A K0 := hK0data.2.2.1
  have hEDG_B0AK0 : Geo.AngleCongruent E D G B0 A K0 := hK0data.2.2.2

  have hSeed :=
    hilbert_space_interior_ray_noncollinear
      (Geo := Geo) A B0 L K0 hCopy.copy_proper hInsideK0
  have hAK0 : Ne A K0 := hSeed.1
  have hB0AK0 : Not (PrimCollinear Geo B0 A K0) := hSeed.2.1
  have hLAK0 : Not (PrimCollinear Geo L A K0) := hSeed.2.2

  have hSegment :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) D G A K0 hAK0
  cases hSegment
  rename_i K hKdata
  have hRayK : HilbertSameRay Geo A K0 K := hKdata.1
  have hAK_DG : Geo.Congruent A K D G := hKdata.2
  have hAK : Ne A K := hRayK.2.1.symm

  have hKsigma : S.OnPlane K sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A K0 K hAK0 hCopy.A_on hK0sigma hRayK.2.2.1

  let Ap : PlanePoint Geo sigma := Subtype.mk A hCopy.A_on
  let B0p : PlanePoint Geo sigma := Subtype.mk B0 hCopy.B0_on
  let Lp : PlanePoint Geo sigma := Subtype.mk L hCopy.L_on
  let K0p : PlanePoint Geo sigma := Subtype.mk K0 hK0sigma
  let Kp : PlanePoint Geo sigma := Subtype.mk K hKsigma

  have hRayKPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap K0p Kp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap K0p Kp).mpr
    simpa [Ap, K0p, Kp] using hRayK

  have hB0A : Ne B0 A :=
    hilbert_noncollinear_ne_first Geo B0 A K0 hB0AK0
  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first Geo L A K0 hLAK0

  have hRayB0Plane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap B0p B0p :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma) Ap B0p
      (by
        intro hEq
        exact hB0A (congrArg Subtype.val hEq))

  have hRayLPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Lp Lp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma) Ap Lp
      (by
        intro hEq
        exact hLA (congrArg Subtype.val hEq))

  have hRayB0 : HilbertSameRay Geo A B0 B0 := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap B0p B0p).mp hRayB0Plane
    simpa [Ap, B0p] using hAmbient

  have hRayL : HilbertSameRay Geo A L L := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Lp Lp).mp hRayLPlane
    simpa [Ap, Lp] using hAmbient

  have hB0AK0Plane :
      Not (PrimCollinear (PlaneGeo Geo sigma) B0p Ap K0p) := by
    intro hCol
    apply hB0AK0
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma B0p Ap K0p hCol
    simpa [B0p, Ap, K0p] using hAmbient

  have hLAK0Plane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Lp Ap K0p) := by
    intro hCol
    apply hLAK0
    have hAmbient :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo) sigma Lp Ap K0p hCol
    simpa [Lp, Ap, K0p] using hAmbient

  have hB0AKPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) B0p Ap Kp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      B0p Ap K0p B0p Kp hB0AK0Plane hRayB0Plane hRayKPlane

  have hLAKPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Lp Ap Kp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      Lp Ap K0p Lp Kp hLAK0Plane hRayLPlane hRayKPlane

  have hMoveFirst : Geo.AngleCongruent B0 A K0 B0 A K :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma B0 A K0 B0 K
      hCopy.B0_on hCopy.A_on hK0sigma hCopy.B0_on hKsigma
      hB0AK0 hRayB0 hRayK

  have hMoveSecond : Geo.AngleCongruent L A K0 L A K :=
    hilbert_space_angleCongruent_of_sameRays_in_plane
      (Geo := Geo)
      sigma L A K0 L K
      hCopy.L_on hCopy.A_on hK0sigma hCopy.L_on hKsigma
      hLAK0 hRayL hRayK

  have hEDG_B0AK : Geo.AngleCongruent E D G B0 A K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo E D G B0 A K0 B0 A K hEDG_B0AK0 hMoveFirst

  have hCDG_LAK : Geo.AngleCongruent C D G L A K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo C D G L A K0 L A K hCDG_LAK0 hMoveSecond

  have hDG_AK : Geo.Congruent D G A K :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) A K D G hAK hAK_DG

  have hDEG : Not (PrimCollinear Geo D E G) := by
    intro hCol
    exact hEDG (PrimCollinearSwap Geo D E G hCol)
  have hDCG : Not (PrimCollinear Geo D C G) := by
    intro hCol
    exact hCDG (PrimCollinearSwap Geo D C G hCol)

  have hAB0KPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Ap B0p Kp) := by
    intro hCol
    exact hB0AKPlane
      (PrimCollinearSwap (PlaneGeo Geo sigma) Ap B0p Kp hCol)

  have hALKPlane :
      Not (PrimCollinear (PlaneGeo Geo sigma) Ap Lp Kp) := by
    intro hCol
    exact hLAKPlane
      (PrimCollinearSwap (PlaneGeo Geo sigma) Ap Lp Kp hCol)

  have hFirstSAS :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma D E G Ap B0p Kp
      hDEG hAB0KPlane hCopy.first_side hDG_AK hEDG_B0AK

  have hSecondSAS :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma D C G Ap Lp Kp
      hDCG hALKPlane hCopy.second_side hDG_AK hCDG_LAK

  have hEG_B0K : Geo.Congruent E G B0 K := by
    simpa [Ap, B0p, Kp] using hFirstSAS.1
  have hCG_LK : Geo.Congruent C G L K := by
    simpa [Ap, Lp, Kp] using hSecondSAS.1

  have hInsideK : HilbertRayMeetsSegment Geo A K B0 L := by
    cases hInsideK0
    rename_i Y hYdata
    have hRayK0Y : HilbertSameRay Geo A K0 Y := hYdata.2
    have hYsigma : S.OnPlane Y sigma :=
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        sigma A K0 Y hAK0 hCopy.A_on hK0sigma hRayK0Y.2.2.1
    let Yp : PlanePoint Geo sigma := Subtype.mk Y hYsigma
    have hRayK0YPlane :
        HilbertSameRay (PlaneGeo Geo sigma) Ap K0p Yp := by
      apply
        (planeGeo_sameRay_iff_ambient
          (Geo := Geo) sigma Ap K0p Yp).mpr
      simpa [Ap, K0p, Yp] using hRayK0Y
    have hRayKYPlane :
        HilbertSameRay (PlaneGeo Geo sigma) Ap Kp Yp :=
      bookZero_36_ray3
        (PlaneGeo Geo sigma) Ap K0p Kp Yp hRayKPlane hRayK0YPlane
    have hRayKY : HilbertSameRay Geo A K Y := by
      have hAmbient :=
        (planeGeo_sameRay_iff_ambient
          (Geo := Geo) sigma Ap Kp Yp).mp hRayKYPlane
      simpa [Ap, Kp, Yp] using hAmbient
    exact Exists.intro Y (And.intro hYdata.1 hRayKY)

  refine Exists.intro K ?_
  exact
    { K_on := hKsigma
      source_ne := hDG
      target_ne := hAK
      interior_ray := hInsideK
      radial := hDG_AK
      first_distance := hEG_B0K
      second_distance := hCG_LK
      first_angle := hEDG_B0AK
      second_angle := hCDG_LAK }


/--
Combined existence: copy the base on the prescribed ray and extend that
same copy by the interior-ray point G.
-/
theorem hilbert_XI26_copy_base_with_interior_point
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (D E C A B G : Geo.Point)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hAB : Ne A B)
    (hInside : HilbertRayMeetsSegment Geo D G E C) :
    exists sigma : S.Plane,
      exists B0 L K : Geo.Point,
        HilbertXI26BaseCopy Geo sigma D E C A B B0 L /\
        HilbertXI26InteriorPointCopy Geo sigma D E C A B0 L G K := by

  have hBase :=
    hilbert_XI26_copy_base_triangle_on_ray
      (Geo := Geo) D E C A B hEDC hAB
  cases hBase
  rename_i sigma hBaseData
  cases hBaseData
  rename_i B0 hBaseTail
  cases hBaseTail
  rename_i L hCopy

  have hPoint :=
    hilbert_XI26_copy_interior_point
      (Geo := Geo) sigma D E C A B B0 L G hEDC hCopy hInside
  cases hPoint
  rename_i K hPointCopy
  exact
    Exists.intro sigma (Exists.intro B0 (Exists.intro L (Exists.intro K
      (And.intro hCopy hPointCopy))))


/-!
## Third stage: lifting the interior point and completing this branch

All planar right-angle arguments below take place in an explicit
PlaneGeo. The final theorem still has the interior-projection hypothesis.
-/


/--
Euclid XI.26 for the branch in which the projection ray DG is interior
to the base angle EDC. The prescribed point A and ray AB are retained.

The conclusion includes the proper target trihedron and all three
corresponding face-angle congruences. The source projection data can be
obtained from hilbert_XI26_source_projection; its other possible foot
positions are not covered by this theorem.
-/
theorem euclid_proposition_11_26_of_interior_projection
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hInside : HilbertRayMeetsSegment Geo D G E C) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2
  have hFG : Ne F G := by
    intro hEq
    have hFpi : S.OnPlane F pi := by
      rw [hEq]
      exact hGpi
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi (And.intro hEpi (And.intro hCpi hFpi))))

  have hConstruction :=
    hilbert_XI26_copy_base_with_interior_point
      (Geo := Geo) D E C A B G hTri.1 hAB hInside
  cases hConstruction
  rename_i sigma hConstructionTail1
  cases hConstructionTail1
  rename_i B0 hConstructionTail2
  cases hConstructionTail2
  rename_i L hConstructionTail3
  cases hConstructionTail3
  rename_i K hCopies
  have hCopy := hCopies.1
  have hPoint := hCopies.2

  have hTargetNormal :=
    euclid_proposition_11_12 (Geo := Geo) sigma K hPoint.K_on
  cases hTargetNormal
  rename_i targetNormal hTargetPerp
  have hKnormal : Hinc.OnLine K targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1
  have hOther :=
    hilbert_other_point_on_line (Geo := Geo) targetNormal K
  cases hOther
  rename_i R hOtherData
  have hHeightCopy :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) G F K R hOtherData.1.symm
  cases hHeightCopy
  rename_i H hHeightData
  have hRayH : HilbertSameRay Geo K R H := hHeightData.1
  have hHK : Ne H K := hRayH.2.1
  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo) hOtherData.1.symm hKnormal hOtherData.2 hRayH.2.2.1
  have hHeight : Geo.Congruent G F K H :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) K H G F hHK.symm hHeightData.2

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHK
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo) sigma targetNormal K H hTargetPerp hHnormal hOn)

  have hSourceInside :=
    hilbert_space_interior_ray_noncollinear
      (Geo := Geo) D E C G hTri.1 hInside
  have hTargetInside :=
    hilbert_space_interior_ray_noncollinear
      (Geo := Geo) A B0 L K hCopy.copy_proper hPoint.interior_ray
  have hEG : Ne E G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) E D G hSourceInside.2.1
  have hCG : Ne C G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) C D G hSourceInside.2.2
  have hB0K : Ne B0 K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) B0 A K hTargetInside.2.1
  have hLK : Ne L K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) L A K hTargetInside.2.2

  have hDF_AH : Geo.Congruent D F A H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F D K H A
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hDpi hCopy.A_on hPoint.source_ne hPoint.target_ne
      hPoint.radial hHeight
  have hEF_B0H : Geo.Congruent E F B0 H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F E K H B0
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hEpi hCopy.B0_on hEG hB0K hPoint.first_distance hHeight
  have hCF_LH : Geo.Congruent C F L H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F C K H L
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hCpi hCopy.L_on hCG hLK hPoint.second_distance hHeight

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo) sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on hCopy.base_proper hHsigma
  have hAuxTri : HilbertTrihedralConfiguration Geo A B0 L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo) sigma A B0 L H
      hCopy.A_on hCopy.B0_on hCopy.L_on hCopy.copy_proper hHsigma

  have hDEF : Not (PrimCollinear Geo D E F) := by
    intro hCol
    exact hTri.2.2.1
      (PrimCollinearSymm Geo E D F (PrimCollinearSwap Geo D E F hCol))
  have hDCF : Not (PrimCollinear Geo D C F) := by
    intro hCol
    exact hTri.2.1 (PrimCollinearSwap Geo D C F hCol)
  have hAB0H : Not (PrimCollinear Geo A B0 H) := by
    intro hCol
    exact hAuxTri.2.2.1
      (PrimCollinearSymm Geo B0 A H (PrimCollinearSwap Geo A B0 H hCol))
  have hALH : Not (PrimCollinear Geo A L H) := by
    intro hCol
    exact hTargetTri.2.1 (PrimCollinearSwap Geo A L H hCol)

  have hEDF_B0AH : Geo.AngleCongruent E D F B0 A H :=
    hilbert_space_sss_angleA
      (Geo := Geo) D E F A B0 H
      hDEF hAB0H hCopy.first_side hEF_B0H hDF_AH
  have hCDF_LAH : Geo.AngleCongruent C D F L A H :=
    hilbert_space_sss_angleA
      (Geo := Geo) D C F A L H
      hDCF hALH hCopy.second_side hCF_LH hDF_AH

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry Geo C D F L A H hCDF_LAH
  have hB0AH_EDF : Geo.AngleCongruent B0 A H E D F :=
    Geometry.Geo.angle_congruent_symmetry Geo E D F B0 A H hEDF_B0AH
  have hHAB0_FDE : Geo.AngleCongruent H A B0 F D E :=
    (Geo.angle_congruent_reverse_second H A B0 E D F).mp
      ((Geo.angle_congruent_reverse_first B0 A H E D F).mp hB0AH_EDF)
  have hAngleEq : Geo.Angle H A B = Geo.Angle H A B0 :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A H B B0 hCopy.first_ray
  have hThird : Geo.AngleCongruent H A B F D E := by
    unfold Geometry.Geo.AngleCongruent at hHAB0_FDE |-
    rw [hAngleEq]
    exact hHAB0_FDE

  exact Exists.intro L (Exists.intro H
    (And.intro hTargetTri
      (And.intro hCopy.base_angle (And.intro hSecond hThird))))


/--
Euclid XI.26 in the branch where D is the foot of the perpendicular
from F to the base plane containing D,E,C.
-/
theorem euclid_proposition_11_26_of_projection_at_vertex
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi D) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  ----------------------------------------------------------------------
  -- F is genuinely outside the base plane, hence F != D.
  ----------------------------------------------------------------------
  have hFpi : Not (S.OnPlane F pi) := by
    intro hOn
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi (And.intro hEpi (And.intro hCpi hOn))))

  have hFD : Ne F D := by
    intro hEq
    apply hFpi
    rw [hEq]
    exact hDpi

  ----------------------------------------------------------------------
  -- Copy the base triangle DEC on the prescribed ray AB.
  ----------------------------------------------------------------------
  have hBase :=
    hilbert_XI26_copy_base_triangle_on_ray
      (Geo := Geo) D E C A B hTri.1 hAB
  cases hBase
  rename_i sigma hBaseTail1
  cases hBaseTail1
  rename_i B0 hBaseTail2
  cases hBaseTail2
  rename_i L hCopy

  ----------------------------------------------------------------------
  -- Construct the target normal at A and lay off DF on it.
  ----------------------------------------------------------------------
  have hTargetNormal :=
    euclid_proposition_11_12 (Geo := Geo) sigma A hCopy.A_on
  cases hTargetNormal
  rename_i targetNormal hTargetPerp

  have hAnormal : Hinc.OnLine A targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1

  have hOther :=
    hilbert_other_point_on_line (Geo := Geo) targetNormal A
  cases hOther
  rename_i R hOtherData

  have hHeightCopy :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) D F A R hOtherData.1.symm
  cases hHeightCopy
  rename_i H hHeightData

  have hRayH : HilbertSameRay Geo A R H := hHeightData.1
  have hHA : Ne H A := hRayH.2.1

  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo) hOtherData.1.symm hAnormal hOtherData.2 hRayH.2.2.1

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHA
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo) sigma targetNormal A H
        hTargetPerp hHnormal hOn)

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo) sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on hCopy.base_proper hHsigma

  ----------------------------------------------------------------------
  -- Nondegeneracy of the four planar arms used below.
  ----------------------------------------------------------------------
  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro hCol
    exact hTri.1 (PrimCollinearSymm Geo C D E hCol)

  have hCD : Ne C D :=
    hilbert_noncollinear_ne_first Geo C D E hCDE

  have hED : Ne E D :=
    hilbert_noncollinear_ne_first Geo E D C hTri.1

  have hLAB : Not (PrimCollinear Geo L A B) := by
    intro hCol
    exact hCopy.base_proper (PrimCollinearSymm Geo L A B hCol)

  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first Geo L A B hLAB

  ----------------------------------------------------------------------
  -- The source and target lateral angles are right angles.
  ----------------------------------------------------------------------
  have hSourceC :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) pi normal D F C
      hPerp hFnormal hFD hCpi hCD

  have hTargetL :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) sigma targetNormal A H L
      hTargetPerp hHnormal hHA hCopy.L_on hLA

  have hFDC_HAL : Geo.AngleCongruent F D C H A L :=
    hilbert_space_all_right_angles_congruent
      (Geo := Geo) F D C H A L
      hSourceC.1 hTargetL.1 hSourceC.2 hTargetL.2

  have hCDF_LAH : Geo.AngleCongruent C D F L A H :=
    (Geo.angle_congruent_reverse_second C D F H A L).mp
      ((Geo.angle_congruent_reverse_first F D C H A L).mp hFDC_HAL)

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo C D F L A H hCDF_LAH

  have hSourceE :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) pi normal D F E
      hPerp hFnormal hFD hEpi hED

  have hTargetB :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) sigma targetNormal A H B
      hTargetPerp hHnormal hHA hCopy.B_on hAB.symm

  have hFDE_HAB : Geo.AngleCongruent F D E H A B :=
    hilbert_space_all_right_angles_congruent
      (Geo := Geo) F D E H A B
      hSourceE.1 hTargetB.1 hSourceE.2 hTargetB.2

  have hThird : Geo.AngleCongruent H A B F D E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo F D E H A B hFDE_HAB

  ----------------------------------------------------------------------
  -- The base angle is already supplied by the copied base triangle.
  ----------------------------------------------------------------------
  exact Exists.intro L (Exists.intro H
    (And.intro hTargetTri
      (And.intro hCopy.base_angle (And.intro hSecond hThird))))


/--
Wrapper in the form naturally produced by hilbert_XI26_source_projection:
the projection foot is a point G together with the branch equation G = D.
-/
theorem euclid_proposition_11_26_of_projection_foot_eq_vertex
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hGD : G = D) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  subst G
  exact
    euclid_proposition_11_26_of_projection_at_vertex
      (Geo := Geo) D E C F A B pi normal
      hTri hAB hDpi hEpi hCpi hFnormal hPerp


/--
Euclid XI.26 in the boundary branch in which the projection ray DG is
the same ray as DE.
-/
theorem euclid_proposition_11_26_of_projection_on_first_ray
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hRayDEG : HilbertSameRay Geo D E G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  ----------------------------------------------------------------------
  -- Source projection data.
  ----------------------------------------------------------------------
  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2

  have hFpi : Not (S.OnPlane F pi) := by
    intro hOn
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi (And.intro hEpi (And.intro hCpi hOn))))

  have hFG : Ne F G := by
    intro hEq
    apply hFpi
    rw [hEq]
    exact hGpi

  have hDG : Ne D G := hRayDEG.2.1.symm

  ----------------------------------------------------------------------
  -- Copy the base triangle DEC on the prescribed ray AB.
  ----------------------------------------------------------------------
  have hBase :=
    hilbert_XI26_copy_base_triangle_on_ray
      (Geo := Geo) D E C A B hTri.1 hAB
  cases hBase
  rename_i sigma hBaseTail1
  cases hBaseTail1
  rename_i B0 hBaseTail2
  cases hBaseTail2
  rename_i L hCopy

  have hB0A : Ne B0 A :=
    hilbert_noncollinear_ne_first
      Geo B0 A L hCopy.copy_proper
  have hAB0 : Ne A B0 := hB0A.symm

  ----------------------------------------------------------------------
  -- Lay off DG on the copied first base ray AB0.
  ----------------------------------------------------------------------
  have hSegment :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) D G A B0 hAB0
  cases hSegment
  rename_i K hKdata

  have hRayB0K : HilbertSameRay Geo A B0 K := hKdata.1
  have hAK_DG : Geo.Congruent A K D G := hKdata.2
  have hAK : Ne A K := hRayB0K.2.1.symm

  have hKsigma : S.OnPlane K sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A B0 K hAB0 hCopy.A_on hCopy.B0_on hRayB0K.2.2.1

  have hDG_AK : Geo.Congruent D G A K :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) A K D G hAK hAK_DG

  ----------------------------------------------------------------------
  -- The angle CDG is the transported base angle LAK.
  ----------------------------------------------------------------------
  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro hCol
    exact hTri.1 (PrimCollinearSymm Geo C D E hCol)

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro hCol
    exact hCopy.copy_proper (PrimCollinearSymm Geo L A B0 hCol)

  have hCDG : Not (PrimCollinear Geo C D G) :=
    hilbert_noncollinear_change_second_sameRay_XI
      (Geo := Geo) C D E G hCDE hRayDEG

  have hLAK : Not (PrimCollinear Geo L A K) :=
    hilbert_noncollinear_change_second_sameRay_XI
      (Geo := Geo) L A B0 K hLAB0 hRayB0K

  have hEDC_B0AL : Geo.AngleCongruent E D C B0 A L :=
    Geometry.Geo.angle_congruent_symmetry
      Geo B0 A L E D C hCopy.copy_angle

  have hCDE_B0AL : Geo.AngleCongruent C D E B0 A L :=
    (Geo.angle_congruent_reverse_first E D C B0 A L).mp hEDC_B0AL

  have hCDE_LAB0 : Geo.AngleCongruent C D E L A B0 :=
    (Geo.angle_congruent_reverse_second C D E B0 A L).mp hCDE_B0AL

  have hCDE_CDG :
      Geo.Angle C D E = Geo.Angle C D G :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) D C E G hRayDEG

  have hLAB0_LAK :
      Geo.Angle L A B0 = Geo.Angle L A K :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A L B0 K hRayB0K

  have hCDG_LAK : Geo.AngleCongruent C D G L A K := by
    unfold Geometry.Geo.AngleCongruent at hCDE_LAB0 |-
    rw [<- hCDE_CDG, <- hLAB0_LAK]
    exact hCDE_LAB0

  ----------------------------------------------------------------------
  -- SAS gives the second distance from the projection point.
  ----------------------------------------------------------------------
  have hDCG : Not (PrimCollinear Geo D C G) := by
    intro hCol
    exact hCDG (PrimCollinearSwap Geo D C G hCol)

  have hALK : Not (PrimCollinear Geo A L K) := by
    intro hCol
    exact hLAK (PrimCollinearSwap Geo A L K hCol)

  have hCG_LK : Geo.Congruent C G L K :=
    hilbert_space_sas_third_side
      (Geo := Geo) D C G A L K
      hDCG hALK hCopy.second_side hDG_AK hCDG_LAK

  ----------------------------------------------------------------------
  -- Erect the target normal at K and copy the height GF.
  ----------------------------------------------------------------------
  have hTargetNormal :=
    euclid_proposition_11_12 (Geo := Geo) sigma K hKsigma
  cases hTargetNormal
  rename_i targetNormal hTargetPerp

  have hKnormal : Hinc.OnLine K targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1

  have hOther :=
    hilbert_other_point_on_line (Geo := Geo) targetNormal K
  cases hOther
  rename_i R hOtherData

  have hHeightCopy :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) G F K R hOtherData.1.symm
  cases hHeightCopy
  rename_i H hHeightData

  have hRayH : HilbertSameRay Geo K R H := hHeightData.1
  have hHK : Ne H K := hRayH.2.1

  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo) hOtherData.1.symm hKnormal hOtherData.2 hRayH.2.2.1

  have hHeight : Geo.Congruent G F K H :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) K H G F hHK.symm hHeightData.2

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHK
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo) sigma targetNormal K H
        hTargetPerp hHnormal hOn)

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo) sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on hCopy.base_proper hHsigma

  ----------------------------------------------------------------------
  -- Lift D/A and C/L through the equal normal heights.
  ----------------------------------------------------------------------
  have hDF_AH : Geo.Congruent D F A H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F D K H A
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hDpi hCopy.A_on hDG hAK hDG_AK hHeight

  have hCG : Ne C G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) C D G hCDG

  have hLK : Ne L K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) L A K hLAK

  have hCF_LH : Geo.Congruent C F L H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F C K H L
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hCpi hCopy.L_on hCG hLK hCG_LK hHeight

  ----------------------------------------------------------------------
  -- Second lateral face: CDF ~= LAH by SSS.
  ----------------------------------------------------------------------
  have hDCF : Not (PrimCollinear Geo D C F) := by
    intro hCol
    exact hTri.2.1 (PrimCollinearSwap Geo D C F hCol)

  have hALH : Not (PrimCollinear Geo A L H) := by
    intro hCol
    exact hTargetTri.2.1 (PrimCollinearSwap Geo A L H hCol)

  have hCDF_LAH : Geo.AngleCongruent C D F L A H :=
    hilbert_space_sss_angleA
      (Geo := Geo) D C F A L H
      hDCF hALH hCopy.second_side hCF_LH hDF_AH

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo C D F L A H hCDF_LAH

  ----------------------------------------------------------------------
  -- Third lateral face.
  -- First compare the right triangles DGF and AKH by SSS, then replace
  -- G by E and K by B on the corresponding rays.
  ----------------------------------------------------------------------
  have hSourceRight :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) pi normal G F D
      hPerp hFnormal hFG hDpi hDG

  have hTargetRight :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) sigma targetNormal K H A
      hTargetPerp hHnormal hHK hCopy.A_on hAK

  have hDGF : Not (PrimCollinear Geo D G F) := by
    intro hCol
    exact hSourceRight.1 (PrimCollinearSymm Geo D G F hCol)

  have hAKH : Not (PrimCollinear Geo A K H) := by
    intro hCol
    exact hTargetRight.1 (PrimCollinearSymm Geo A K H hCol)

  have hGDF_KAH : Geo.AngleCongruent G D F K A H :=
    hilbert_space_sss_angleA
      (Geo := Geo) D G F A K H
      hDGF hAKH hDG_AK hHeight hDF_AH

  have hFDG_KAH : Geo.AngleCongruent F D G K A H :=
    (Geo.angle_congruent_reverse_first G D F K A H).mp hGDF_KAH

  have hFDG_HAK : Geo.AngleCongruent F D G H A K :=
    (Geo.angle_congruent_reverse_second F D G K A H).mp hFDG_KAH

  have hFDE_FDG :
      Geo.Angle F D E = Geo.Angle F D G :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) D F E G hRayDEG

  have hHAB_HAB0 :
      Geo.Angle H A B = Geo.Angle H A B0 :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A H B B0 hCopy.first_ray

  have hHAB0_HAK :
      Geo.Angle H A B0 = Geo.Angle H A K :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A H B0 K hRayB0K

  have hHAB_HAK :
      Geo.Angle H A B = Geo.Angle H A K :=
    hHAB_HAB0.trans hHAB0_HAK

  have hFDE_HAB : Geo.AngleCongruent F D E H A B := by
    unfold Geometry.Geo.AngleCongruent at hFDG_HAK |-
    rw [hFDE_FDG, hHAB_HAK]
    exact hFDG_HAK

  have hThird : Geo.AngleCongruent H A B F D E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo F D E H A B hFDE_HAB

  ----------------------------------------------------------------------
  -- Package the three faces.
  ----------------------------------------------------------------------
  exact Exists.intro L (Exists.intro H
    (And.intro hTargetTri
      (And.intro hCopy.base_angle (And.intro hSecond hThird))))


/--
Euclid XI.26 in the boundary branch in which the projection ray DG is
the same ray as DC.
-/
theorem euclid_proposition_11_26_of_projection_on_second_ray
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hRayDCG : HilbertSameRay Geo D C G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  ----------------------------------------------------------------------
  -- Source projection data.
  ----------------------------------------------------------------------
  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2

  have hFpi : Not (S.OnPlane F pi) := by
    intro hOn
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi (And.intro hEpi (And.intro hCpi hOn))))

  have hFG : Ne F G := by
    intro hEq
    apply hFpi
    rw [hEq]
    exact hGpi

  have hDG : Ne D G := hRayDCG.2.1.symm

  ----------------------------------------------------------------------
  -- Copy the base triangle DEC on the prescribed ray AB.
  ----------------------------------------------------------------------
  have hBase :=
    hilbert_XI26_copy_base_triangle_on_ray
      (Geo := Geo) D E C A B hTri.1 hAB
  cases hBase
  rename_i sigma hBaseTail1
  cases hBaseTail1
  rename_i B0 hBaseTail2
  cases hBaseTail2
  rename_i L hCopy

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro hCol
    exact hCopy.copy_proper (PrimCollinearSymm Geo L A B0 hCol)

  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first
      Geo L A B0 hLAB0
  have hAL : Ne A L := hLA.symm

  ----------------------------------------------------------------------
  -- Lay off DG on the copied second base ray AL.
  ----------------------------------------------------------------------
  have hSegment :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) D G A L hAL
  cases hSegment
  rename_i K hKdata

  have hRayLK : HilbertSameRay Geo A L K := hKdata.1
  have hAK_DG : Geo.Congruent A K D G := hKdata.2
  have hAK : Ne A K := hRayLK.2.1.symm

  have hKsigma : S.OnPlane K sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A L K hAL hCopy.A_on hCopy.L_on hRayLK.2.2.1

  have hDG_AK : Geo.Congruent D G A K :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) A K D G hAK hAK_DG

  ----------------------------------------------------------------------
  -- The angle EDG is the transported base angle B0AK.
  ----------------------------------------------------------------------
  have hEDG : Not (PrimCollinear Geo E D G) :=
    hilbert_noncollinear_change_second_sameRay_XI
      (Geo := Geo) E D C G hTri.1 hRayDCG

  have hB0AK : Not (PrimCollinear Geo B0 A K) :=
    hilbert_noncollinear_change_second_sameRay_XI
      (Geo := Geo) B0 A L K hCopy.copy_proper hRayLK

  have hEDC_B0AL : Geo.AngleCongruent E D C B0 A L :=
    Geometry.Geo.angle_congruent_symmetry
      Geo B0 A L E D C hCopy.copy_angle

  have hEDC_EDG :
      Geo.Angle E D C = Geo.Angle E D G :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) D E C G hRayDCG

  have hB0AL_B0AK :
      Geo.Angle B0 A L = Geo.Angle B0 A K :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A B0 L K hRayLK

  have hEDG_B0AK : Geo.AngleCongruent E D G B0 A K := by
    unfold Geometry.Geo.AngleCongruent at hEDC_B0AL |-
    rw [<- hEDC_EDG, <- hB0AL_B0AK]
    exact hEDC_B0AL

  ----------------------------------------------------------------------
  -- SAS gives the first distance from the projection point.
  ----------------------------------------------------------------------
  have hDEG : Not (PrimCollinear Geo D E G) := by
    intro hCol
    exact hEDG (PrimCollinearSwap Geo D E G hCol)

  have hAB0K : Not (PrimCollinear Geo A B0 K) := by
    intro hCol
    exact hB0AK (PrimCollinearSwap Geo A B0 K hCol)

  have hEG_B0K : Geo.Congruent E G B0 K :=
    hilbert_space_sas_third_side
      (Geo := Geo) D E G A B0 K
      hDEG hAB0K hCopy.first_side hDG_AK hEDG_B0AK

  ----------------------------------------------------------------------
  -- Erect the target normal at K and copy the height GF.
  ----------------------------------------------------------------------
  have hTargetNormal :=
    euclid_proposition_11_12 (Geo := Geo) sigma K hKsigma
  cases hTargetNormal
  rename_i targetNormal hTargetPerp

  have hKnormal : Hinc.OnLine K targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1

  have hOther :=
    hilbert_other_point_on_line (Geo := Geo) targetNormal K
  cases hOther
  rename_i R hOtherData

  have hHeightCopy :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) G F K R hOtherData.1.symm
  cases hHeightCopy
  rename_i H hHeightData

  have hRayH : HilbertSameRay Geo K R H := hHeightData.1
  have hHK : Ne H K := hRayH.2.1

  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo) hOtherData.1.symm hKnormal hOtherData.2 hRayH.2.2.1

  have hHeight : Geo.Congruent G F K H :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) K H G F hHK.symm hHeightData.2

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHK
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo) sigma targetNormal K H
        hTargetPerp hHnormal hOn)

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo) sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on hCopy.base_proper hHsigma

  have hAuxTri : HilbertTrihedralConfiguration Geo A B0 L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo) sigma A B0 L H
      hCopy.A_on hCopy.B0_on hCopy.L_on hCopy.copy_proper hHsigma

  ----------------------------------------------------------------------
  -- Lift D/A and E/B0 through the equal normal heights.
  ----------------------------------------------------------------------
  have hDF_AH : Geo.Congruent D F A H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F D K H A
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hDpi hCopy.A_on hDG hAK hDG_AK hHeight

  have hEG : Ne E G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) E D G hEDG

  have hB0K : Ne B0 K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) B0 A K hB0AK

  have hEF_B0H : Geo.Congruent E F B0 H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo) pi sigma normal targetNormal G F E K H B0
      hPerp hTargetPerp hFnormal hHnormal hFG hHK
      hEpi hCopy.B0_on hEG hB0K hEG_B0K hHeight

  ----------------------------------------------------------------------
  -- Third lateral face: FDE ~= HAB by SSS and ray transport B0 -> B.
  ----------------------------------------------------------------------
  have hDEF : Not (PrimCollinear Geo D E F) := by
    intro hCol
    exact hTri.2.2.1
      (PrimCollinearSymm Geo E D F (PrimCollinearSwap Geo D E F hCol))

  have hAB0H : Not (PrimCollinear Geo A B0 H) := by
    intro hCol
    exact hAuxTri.2.2.1
      (PrimCollinearSymm Geo B0 A H (PrimCollinearSwap Geo A B0 H hCol))

  have hEDF_B0AH : Geo.AngleCongruent E D F B0 A H :=
    hilbert_space_sss_angleA
      (Geo := Geo) D E F A B0 H
      hDEF hAB0H hCopy.first_side hEF_B0H hDF_AH

  have hB0AH_EDF : Geo.AngleCongruent B0 A H E D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo E D F B0 A H hEDF_B0AH

  have hHAB0_FDE : Geo.AngleCongruent H A B0 F D E :=
    (Geo.angle_congruent_reverse_second H A B0 E D F).mp
      ((Geo.angle_congruent_reverse_first B0 A H E D F).mp hB0AH_EDF)

  have hAngleEq : Geo.Angle H A B = Geo.Angle H A B0 :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A H B B0 hCopy.first_ray

  have hThird : Geo.AngleCongruent H A B F D E := by
    unfold Geometry.Geo.AngleCongruent at hHAB0_FDE |-
    rw [hAngleEq]
    exact hHAB0_FDE

  ----------------------------------------------------------------------
  -- Second lateral face.
  -- Compare DGF and AKH by SSS, then replace G by C and K by L on the
  -- corresponding rays.
  ----------------------------------------------------------------------
  have hSourceRight :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) pi normal G F D
      hPerp hFnormal hFG hDpi hDG

  have hTargetRight :=
    hilbert_space_right_angle_from_plane_normal
      (Geo := Geo) sigma targetNormal K H A
      hTargetPerp hHnormal hHK hCopy.A_on hAK

  have hDGF : Not (PrimCollinear Geo D G F) := by
    intro hCol
    exact hSourceRight.1 (PrimCollinearSymm Geo D G F hCol)

  have hAKH : Not (PrimCollinear Geo A K H) := by
    intro hCol
    exact hTargetRight.1 (PrimCollinearSymm Geo A K H hCol)

  have hGDF_KAH : Geo.AngleCongruent G D F K A H :=
    hilbert_space_sss_angleA
      (Geo := Geo) D G F A K H
      hDGF hAKH hDG_AK hHeight hDF_AH

  have hCDF_GDF :
      Geo.Angle C D F = Geo.Angle G D F :=
    hilbert_space_angle_eq_of_sameRay_first
      (Geo := Geo) D C G F hRayDCG

  have hLAH_KAH :
      Geo.Angle L A H = Geo.Angle K A H :=
    hilbert_space_angle_eq_of_sameRay_first
      (Geo := Geo) A L K H hRayLK

  have hCDF_LAH : Geo.AngleCongruent C D F L A H := by
    unfold Geometry.Geo.AngleCongruent at hGDF_KAH |-
    rw [hCDF_GDF, hLAH_KAH]
    exact hGDF_KAH

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo C D F L A H hCDF_LAH

  ----------------------------------------------------------------------
  -- Package the three faces.
  ----------------------------------------------------------------------
  exact Exists.intro L (Exists.intro H
    (And.intro hTargetTri
      (And.intro hCopy.base_angle (And.intro hSecond hThird))))


/--
Local construction for the first adjacent exterior sector of XI.26.

The source hypothesis `hEDG` supplies the proper triangle DEG.  The point K
is placed on a ray adjacent to the copied base angle at the AB0 side.
-/
theorem hilbert_XI26_copy_first_exterior_component
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDG : Not (PrimCollinear Geo E D G)) :
    exists base : Geo.Line,
      exists T X K : Geo.Point,
        HilbertLineInPlane Geo base sigma /\
        Hinc.OnLine A base /\
        Hinc.OnLine B0 base /\
        Geo.Between L A T /\
        HilbertSameSideInPlane Geo X T base sigma /\
        S.OnPlane K sigma /\
        HilbertSameRay Geo A X K /\
        Geo.Congruent D G A K /\
        Geo.Congruent E G B0 K /\
        Geo.AngleCongruent E D G B0 A K /\
        Not (PrimCollinear Geo B0 A K) := by

  ----------------------------------------------------------------------
  -- Carrier AB0 of the copied first base arm.
  ----------------------------------------------------------------------
  have hB0A : Ne B0 A :=
    hilbert_noncollinear_ne_first
      Geo B0 A L hCopy.copy_proper
  have hAB0 : Ne A B0 := hB0A.symm

  have hBase :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo) A B0 hAB0
  cases hBase
  rename_i base hBaseData
  have hAbase : Hinc.OnLine A base := hBaseData.1
  have hB0base : Hinc.OnLine B0 base := hBaseData.2

  have hBaseSigma : HilbertLineInPlane Geo base sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B0 hAB0
      base hAbase hB0base
      sigma hCopy.A_on hCopy.B0_on

  ----------------------------------------------------------------------
  -- L is off AB0. Extend LA through A to obtain a point T on the
  -- opposite side of the carrier.
  ----------------------------------------------------------------------
  have hLbase : Not (Hinc.OnLine L base) := by
    intro hOn
    exact hCopy.copy_proper
      (Exists.intro base
        (And.intro hB0base (And.intro hAbase hOn)))

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro hCol
    exact hCopy.copy_proper
      (PrimCollinearSymm Geo L A B0 hCol)

  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first
      Geo L A B0 hLAB0

  have hExtension :=
    HilbertSpaceOrder.between_extension
      (Geo := Geo) L A hLA
  cases hExtension
  rename_i T hLAT

  have hLATdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) L A T hLAT
  have hAT : Ne A T := hLATdata.2.1
  have hLATcol : PrimCollinear Geo L A T :=
    hLATdata.2.2.2.1

  have hTsigma : S.OnPlane T sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma L A T hLA
      hCopy.L_on hCopy.A_on hLATcol

  have hTbase : Not (Hinc.OnLine T base) := by
    intro hTOn
    have hATL : PrimCollinear Geo A T L := by
      rcases hLATcol with
        ⟨line, hLline, hAline, hTline⟩
      exact
        Exists.intro line
          (And.intro hAline (And.intro hTline hLline))
    have hLOn : Hinc.OnLine L base :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAT hAbase hTOn hATL
    exact hLbase hLOn

  ----------------------------------------------------------------------
  -- Copy angle EDG on the T-side of AB0.
  ----------------------------------------------------------------------
  have hAngleCopy :=
    HilbertSpaceCongruence.angle_construction_in_plane
      (Geo := Geo)
      E D G B0 A T
      hEDG hB0A
      sigma base hBaseSigma
      hB0base hAbase hTsigma hTbase
  cases hAngleCopy
  rename_i X hAngleData
  have hXside : HilbertSameSideInPlane Geo X T base sigma :=
    hAngleData.1
  have hEDG_B0AX : Geo.AngleCongruent E D G B0 A X :=
    hAngleData.2.1

  have hXsigma : S.OnPlane X sigma := hXside.1
  have hXbase : Not (Hinc.OnLine X base) := hXside.2.2.1

  have hB0AX : Not (PrimCollinear Geo B0 A X) := by
    intro hCol
    apply hXbase
    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hB0A hB0base hAbase hCol

  have hAX : Ne A X := by
    intro hEq
    apply hXbase
    rw [<- hEq]
    exact hAbase

  ----------------------------------------------------------------------
  -- Lay off DG on the constructed ray AX.
  ----------------------------------------------------------------------
  have hSegment :=
    HilbertSpaceCongruence.segment_construction
      (Geo := Geo) D G A X hAX
  cases hSegment
  rename_i K hKdata

  have hRayXK : HilbertSameRay Geo A X K := hKdata.1
  have hAK_DG : Geo.Congruent A K D G := hKdata.2
  have hAK : Ne A K := hRayXK.2.1.symm

  have hKsigma : S.OnPlane K sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A X K hAX
      hCopy.A_on hXsigma hRayXK.2.2.1

  have hDG_AK : Geo.Congruent D G A K :=
    hilbert_space_congruent_symmetry
      (Geo := Geo) A K D G hAK hAK_DG

  have hB0AK : Not (PrimCollinear Geo B0 A K) :=
    hilbert_noncollinear_change_second_sameRay_XI
      (Geo := Geo) B0 A X K hB0AX hRayXK

  have hB0AX_B0AK :
      Geo.Angle B0 A X = Geo.Angle B0 A K :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo) A B0 X K hRayXK

  have hEDG_B0AK : Geo.AngleCongruent E D G B0 A K := by
    unfold Geometry.Geo.AngleCongruent at hEDG_B0AX |-
    rw [<- hB0AX_B0AK]
    exact hEDG_B0AX

  ----------------------------------------------------------------------
  -- SAS in triangles DEG and AB0K gives EG ~= B0K.
  ----------------------------------------------------------------------
  have hDEG : Not (PrimCollinear Geo D E G) := by
    intro hCol
    exact hEDG (PrimCollinearSwap Geo D E G hCol)

  have hAB0K : Not (PrimCollinear Geo A B0 K) := by
    intro hCol
    exact hB0AK (PrimCollinearSwap Geo A B0 K hCol)

  have hEG_B0K : Geo.Congruent E G B0 K :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      D E G A B0 K
      hDEG hAB0K
      hCopy.first_side hDG_AK hEDG_B0AK

  refine Exists.intro base ?_
  refine Exists.intro T ?_
  refine Exists.intro X ?_
  refine Exists.intro K ?_
  refine And.intro hBaseSigma ?_
  refine And.intro hAbase ?_
  refine And.intro hB0base ?_
  refine And.intro hLAT ?_
  refine And.intro hXside ?_
  refine And.intro hKsigma ?_
  refine And.intro hRayXK ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hEDG_B0AK ?_
  exact hB0AK


/--
The local first-exterior construction places K on the side of the copied
carrier AB0 opposite L.

The proof is carried out in PlaneGeo sigma.  First L and the extension
point T are opposite across AB0 because L-A-T.  The angle-construction
point X is on the same side as T.  Finally K is on the same ray AX as X,
so X and K remain on the same side of AB0.
-/
theorem hilbert_XI26_first_exterior_target_opposite
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDG : Not (PrimCollinear Geo E D G)) :
    exists base : Geo.Line,
      exists K : Geo.Point,
        HilbertLineInPlane Geo base sigma /\
        Hinc.OnLine A base /\
        Hinc.OnLine B0 base /\
        S.OnPlane K sigma /\
        Geo.Congruent D G A K /\
        Geo.Congruent E G B0 K /\
        Geo.AngleCongruent E D G B0 A K /\
        Not (PrimCollinear Geo B0 A K) /\
        HilbertOppositeSide Geo L K base := by

  rcases
      hilbert_XI26_copy_first_exterior_component
        (Geo := Geo)
        sigma D E C A B B0 L G hCopy hEDG with
    ⟨base, T, X, K,
      hBaseSigma,
      hAbase,
      hB0base,
      hLAT,
      hXside,
      hKsigma,
      hRayXK,
      hDG_AK,
      hEG_B0K,
      hEDG_B0AK,
      hB0AK⟩

  have hLbase : Not (Hinc.OnLine L base) := by
    intro hLline
    exact hCopy.copy_proper
      (Exists.intro base
        (And.intro hB0base
          (And.intro hAbase hLline)))

  have hTsigma : S.OnPlane T sigma := hXside.2.1
  have hTbase : Not (Hinc.OnLine T base) := hXside.2.2.2.1
  have hXsigma : S.OnPlane X sigma := hXside.1
  have hXbase : Not (Hinc.OnLine X base) := hXside.2.2.1

  let Ap : PlanePoint Geo sigma :=
    Subtype.mk A hCopy.A_on
  let B0p : PlanePoint Geo sigma :=
    Subtype.mk B0 hCopy.B0_on
  let Lp : PlanePoint Geo sigma :=
    Subtype.mk L hCopy.L_on
  let Tp : PlanePoint Geo sigma :=
    Subtype.mk T hTsigma
  let Xp : PlanePoint Geo sigma :=
    Subtype.mk X hXsigma
  let Kp : PlanePoint Geo sigma :=
    Subtype.mk K hKsigma
  let basep : PlaneLine Geo sigma :=
    Subtype.mk base hBaseSigma

  have hAbasep :
      PlaneOnLine Geo Ap basep := by
    change Hinc.OnLine A base
    exact hAbase

  have hB0basep :
      PlaneOnLine Geo B0p basep := by
    change Hinc.OnLine B0 base
    exact hB0base

  have hLoffp :
      Not (PlaneOnLine Geo Lp basep) := by
    change Not (Hinc.OnLine L base)
    exact hLbase

  have hToffp :
      Not (PlaneOnLine Geo Tp basep) := by
    change Not (Hinc.OnLine T base)
    exact hTbase

  have hLATPlane :
      (PlaneGeo Geo sigma).Between Lp Ap Tp := by
    apply
      (planeGeo_between
        (Geo := Geo) sigma Lp Ap Tp).mpr
    simpa [Lp, Ap, Tp] using hLAT

  have hOppLTPlane :
      HilbertOppositeSide
        (PlaneGeo Geo sigma) Lp Tp basep :=
    ⟨hLoffp,
      hToffp,
      ⟨Ap, hLATPlane, hAbasep⟩⟩

  have hSameXTPlane :
      HilbertSameSide
        (PlaneGeo Geo sigma) Xp Tp basep := by
    apply
      (planeGeo_sameSide_iff_space
        (Geo := Geo) sigma Xp Tp basep).mpr
    simpa [Xp, Tp, basep] using hXside

  have hSameTXPlane :
      HilbertSameSide
        (PlaneGeo Geo sigma) Tp Xp basep :=
    hilbert_sameSide_symm
      (PlaneGeo Geo sigma) Xp Tp basep hSameXTPlane

  have hOppLXPlane :
      HilbertOppositeSide
        (PlaneGeo Geo sigma) Lp Xp basep :=
    hilbert_oppositeSide_transport_right
      (PlaneGeo Geo sigma)
      Lp Tp Xp basep
      hOppLTPlane hSameTXPlane

  have hRayXKPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Ap Xp Kp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Xp Kp).mpr
    simpa [Ap, Xp, Kp] using hRayXK

  have hAXp : Ne Ap Xp := by
    intro hEq
    apply hRayXK.1
    exact (congrArg Subtype.val hEq).symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma) Ap Xp hAXp with
    ⟨lineAX, hAlineAX, hXlineAX⟩

  have hB0Ap : Ne B0p Ap := by
    intro hEq
    have hVal : B0 = A := congrArg Subtype.val hEq
    exact
      (hilbert_noncollinear_ne_first
        Geo B0 A L hCopy.copy_proper) hVal

  have hB0offAX :
      Not (PlaneOnLine Geo B0p lineAX) := by
    intro hB0lineAX

    have hEqLines : lineAX = basep :=
      HilbertPlaneIncidence.line_unique
        Ap B0p hB0Ap.symm
        lineAX basep
        hAlineAX hB0lineAX
        hAbasep hB0basep

    have hXbasep : PlaneOnLine Geo Xp basep := by
      rw [<- hEqLines]
      exact hXlineAX

    have hXbaseAmbient : Hinc.OnLine X base := by
      change Hinc.OnLine X base at hXbasep
      exact hXbasep
    exact hXbase hXbaseAmbient

  have hRayXXPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) Ap Xp Xp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma) Ap Xp hRayXKPlane.1

  have hSameXKPlane :
      HilbertSameSide
        (PlaneGeo Geo sigma) Xp Kp basep :=
    hilbert_sameRay_points_sameSide
      (PlaneGeo Geo sigma)
      Ap Xp Xp Kp B0p
      lineAX basep
      hAlineAX hXlineAX
      hAbasep hB0basep
      hB0offAX
      hRayXXPlane hRayXKPlane

  have hOppLKPlane :
      HilbertOppositeSide
        (PlaneGeo Geo sigma) Lp Kp basep :=
    hilbert_oppositeSide_transport_right
      (PlaneGeo Geo sigma)
      Lp Xp Kp basep
      hOppLXPlane hSameXKPlane

  have hLoff : Not (Hinc.OnLine L base) := by
    have h := hOppLKPlane.1
    change Not (Hinc.OnLine L base) at h
    exact h

  have hKoff : Not (Hinc.OnLine K base) := by
    have h := hOppLKPlane.2.1
    change Not (Hinc.OnLine K base) at h
    exact h

  rcases hOppLKPlane.2.2 with
    ⟨Yp, hLYKPlane, hYbasep⟩

  have hLYK : Geo.Between L Yp.1 K := by
    have hAmbient :=
      (planeGeo_between
        (Geo := Geo) sigma Lp Yp Kp).mp hLYKPlane
    simpa [Lp, Kp] using hAmbient

  have hYbase : Hinc.OnLine Yp.1 base := by
    change Hinc.OnLine Yp.1 base at hYbasep
    exact hYbasep

  have hOppLK : HilbertOppositeSide Geo L K base :=
    ⟨hLoff, hKoff, ⟨Yp.1, hLYK, hYbase⟩⟩

  refine Exists.intro base ?_
  refine Exists.intro K ?_
  refine And.intro hBaseSigma ?_
  refine And.intro hAbase ?_
  refine And.intro hB0base ?_
  refine And.intro hKsigma ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hEDG_B0AK ?_
  refine And.intro hB0AK ?_
  exact hOppLK


/--
Normalize the copied base-angle component to the orientation required by
Hilbert T15 in the first exterior sector:

    angle CDE ~= angle LAB0.
-/
theorem hilbert_XI26_first_exterior_base_component_angle
    [Hinc : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (sigma : S.Plane)
    (D E C A B B0 L : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L) :
    Geo.AngleCongruent C D E L A B0 := by

  have hLAB0_CDE :
      Geo.AngleCongruent L A B0 C D E :=
    (Geo.angle_congruent_reverse_second
      L A B0 E D C).mp
      ((Geo.angle_congruent_reverse_first
        B0 A L E D C).mp hCopy.copy_angle)

  exact
    Geometry.Geo.angle_congruent_symmetry
      Geo L A B0 C D E hLAB0_CDE


/--
Exact Hilbert-T15 input package for the first exterior sector of XI.26.

The two component congruences are

    CDE ~= LAB0,
    EDG ~= B0AK,

and the corresponding outer points lie on opposite sides of the divider
carriers DE and AB0.
-/
theorem hilbert_XI26_first_exterior_T15_data
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hEDG : Not (PrimCollinear Geo E D G))
    (hInside : HilbertRayMeetsSegment Geo D E C G) :
    exists lineDE base : Geo.Line,
      exists K : Geo.Point,
        Hinc.OnLine D lineDE /\
        Hinc.OnLine E lineDE /\
        HilbertOppositeSide Geo C G lineDE /\
        HilbertLineInPlane Geo base sigma /\
        Hinc.OnLine A base /\
        Hinc.OnLine B0 base /\
        S.OnPlane K sigma /\
        HilbertOppositeSide Geo L K base /\
        Not (PrimCollinear Geo C D G) /\
        Not (PrimCollinear Geo B0 A K) /\
        Geo.AngleCongruent C D E L A B0 /\
        Geo.AngleCongruent E D G B0 A K /\
        Geo.Congruent D G A K /\
        Geo.Congruent E G B0 K := by

  rcases
      hilbert_ray_meets_segment_endpoints_oppositeSide_XI
        (Geo := Geo)
        D E C G hEDC hEDG hInside with
    ⟨lineDE, hDlineDE, hElineDE, hOppCG⟩

  rcases
      hilbert_XI26_first_exterior_target_opposite
        (Geo := Geo)
        sigma D E C A B B0 L G hCopy hEDG with
    ⟨base, K,
      hBaseSigma,
      hAbase,
      hB0base,
      hKsigma,
      hDG_AK,
      hEG_B0K,
      hEDG_B0AK,
      hB0AK,
      hOppLK⟩

  have hCDG : Not (PrimCollinear Geo C D G) :=
    hilbert_ray_meets_segment_outer_angle_nondegenerate_XI
      (Geo := Geo)
      D E C G hEDC hEDG hInside

  have hCDE_LAB0 :
      Geo.AngleCongruent C D E L A B0 :=
    hilbert_XI26_first_exterior_base_component_angle
      (Geo := Geo)
      sigma D E C A B B0 L hCopy

  refine Exists.intro lineDE ?_
  refine Exists.intro base ?_
  refine Exists.intro K ?_
  refine And.intro hDlineDE ?_
  refine And.intro hElineDE ?_
  refine And.intro hOppCG ?_
  refine And.intro hBaseSigma ?_
  refine And.intro hAbase ?_
  refine And.intro hB0base ?_
  refine And.intro hKsigma ?_
  refine And.intro hOppLK ?_
  refine And.intro hCDG ?_
  refine And.intro hB0AK ?_
  refine And.intro hCDE_LAB0 ?_
  refine And.intro hEDG_B0AK ?_
  refine And.intro hDG_AK ?_
  exact hEG_B0K


/--
Conditional target-side opposite-extension reduction.

This is the exact target analogue needed by the spatial T15 proof once
`LAK` is known to be a proper angle.
-/
theorem hilbert_XI26_target_extension_sameSide_of_nondegenerate
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (base : Geo.Line)
    (A B0 L K : Geo.Point)
    (hAsigma : S.OnPlane A sigma)
    (_hB0sigma : S.OnPlane B0 sigma)
    (hLsigma : S.OnPlane L sigma)
    (hKsigma : S.OnPlane K sigma)
    (hBaseSigma : HilbertLineInPlane Geo base sigma)
    (hAbase : Hinc.OnLine A base)
    (_hB0base : Hinc.OnLine B0 base)
    (hLAK : Not (PrimCollinear Geo L A K))
    (hOppLK : HilbertOppositeSide Geo L K base) :
    exists Q : Geo.Point,
      S.OnPlane Q sigma /\
      Geo.Between L A Q /\
      HilbertSameSideInPlane Geo Q K base sigma := by

  exact
    hilbert_space_plane_local_opposite_extension_sameSide
      (Geo := Geo)
      sigma base
      L A K
      hLsigma hAsigma hKsigma
      hBaseSigma
      hAbase
      hLAK
      hOppLK


/--
For the first exterior sector, the target opposite-extension construction
is therefore unconditional.  The theorem returns both extension points
P,Q and the same-side data consumed by the spatial-T15 step.
-/
theorem hilbert_XI26_first_exterior_opposite_extensions
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hEDG : Not (PrimCollinear Geo E D G))
    (hInside : HilbertRayMeetsSegment Geo D E C G) :
    exists pi : S.Plane,
      exists lineDE base : Geo.Line,
        exists K P Q : Geo.Point,
          HilbertLineInPlane Geo lineDE pi /\
          Hinc.OnLine D lineDE /\
          Hinc.OnLine E lineDE /\
          HilbertLineInPlane Geo base sigma /\
          Hinc.OnLine A base /\
          Hinc.OnLine B0 base /\
          S.OnPlane K sigma /\
          S.OnPlane P pi /\
          S.OnPlane Q sigma /\
          Not (PrimCollinear Geo L A K) /\
          Geo.Between C D P /\
          HilbertSameSideInPlane Geo P G lineDE pi /\
          Geo.Between L A Q /\
          HilbertSameSideInPlane Geo Q K base sigma /\
          Not (PrimCollinear Geo C D G) /\
          Not (PrimCollinear Geo B0 A K) /\
          Geo.AngleCongruent C D E L A B0 /\
          Geo.AngleCongruent E D G B0 A K /\
          Geo.Congruent D G A K /\
          Geo.Congruent E G B0 K := by

  rcases
      hilbert_XI26_first_exterior_T15_data
        (Geo := Geo)
        sigma D E C A B B0 L G
        hCopy hEDC hEDG hInside with
    ⟨_lineDE0, base, K,
      _hDline0, _hEline0, _hOppCG,
      hBaseSigma, hAbase, hB0base,
      hKsigma, hOppLK,
      hCDG, hB0AK,
      hCDE_LAB0, hEDG_B0AK,
      hDG_AK, hEG_B0K⟩

  rcases
      hilbert_space_ray_meets_segment_opposite_extension_sameSide
        (Geo := Geo)
        D E C G hEDC hEDG hInside with
    ⟨pi, lineDE, P,
      _hCpi, _hDpi, _hEpi, _hGpi, hPpi,
      hLineDEpi, hDlineDE, hElineDE,
      hCDP, hSamePG⟩

  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro h
    exact hEDC (PrimCollinearSymm Geo C D E h)

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro h
    exact hCopy.copy_proper
      (PrimCollinearSymm Geo L A B0 h)

  have hLAK : Not (PrimCollinear Geo L A K) :=
    hilbert_space_T15_target_outer_nondegenerate_from_data
      (Geo := Geo)
      pi lineDE base
      C D E G P L A B0 K
      hLineDEpi hDlineDE hElineDE
      hCDP hSamePG
      hAbase hOppLK
      hCDE hLAB0 hB0AK hCDG
      hCDE_LAB0 hEDG_B0AK

  rcases
      hilbert_XI26_target_extension_sameSide_of_nondegenerate
        (Geo := Geo)
        sigma base
        A B0 L K
        hCopy.A_on hCopy.B0_on hCopy.L_on hKsigma
        hBaseSigma hAbase hB0base
        hLAK hOppLK with
    ⟨Q, hQsigma, hLAQ, hSameQK⟩

  refine Exists.intro pi ?_
  refine Exists.intro lineDE ?_
  refine Exists.intro base ?_
  refine Exists.intro K ?_
  refine Exists.intro P ?_
  refine Exists.intro Q ?_
  refine And.intro hLineDEpi ?_
  refine And.intro hDlineDE ?_
  refine And.intro hElineDE ?_
  refine And.intro hBaseSigma ?_
  refine And.intro hAbase ?_
  refine And.intro hB0base ?_
  refine And.intro hKsigma ?_
  refine And.intro hPpi ?_
  refine And.intro hQsigma ?_
  refine And.intro hLAK ?_
  refine And.intro hCDP ?_
  refine And.intro hSamePG ?_
  refine And.intro hLAQ ?_
  refine And.intro hSameQK ?_
  refine And.intro hCDG ?_
  refine And.intro hB0AK ?_
  refine And.intro hCDE_LAB0 ?_
  refine And.intro hEDG_B0AK ?_
  refine And.intro hDG_AK ?_
  exact hEG_B0K


/--
Strong form of the first-exterior point-copy theorem.

Besides the three transported distances, retain the three proper-angle
facts needed later to prove that the radial target segments are
nondegenerate when the point is lifted off the copied base plane.
-/
theorem hilbert_XI26_copy_first_exterior_point_strong
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hEDG : Not (PrimCollinear Geo E D G))
    (hInside : HilbertRayMeetsSegment Geo D E C G) :
    exists K : Geo.Point,
      S.OnPlane K sigma /\
      Not (PrimCollinear Geo C D G) /\
      Not (PrimCollinear Geo B0 A K) /\
      Not (PrimCollinear Geo L A K) /\
      Geo.Congruent D G A K /\
      Geo.Congruent E G B0 K /\
      Geo.Congruent C G L K /\
      Geo.AngleCongruent E D G B0 A K /\
      Geo.AngleCongruent C D G L A K := by

  rcases
      hilbert_XI26_first_exterior_opposite_extensions
        (Geo := Geo)
        sigma D E C A B B0 L G
        hCopy hEDC hEDG hInside with
    ⟨pi, lineDE, base, K, P, Q,
      hLineDEpi,
      hDlineDE, hElineDE,
      hBaseSigma,
      hAbase, hB0base,
      hKsigma, _hPpi, _hQsigma,
      hLAK,
      hCDP, hSamePG,
      hLAQ, hSameQK,
      hCDG, hB0AK,
      hCDE_LAB0, hEDG_B0AK,
      hDG_AK, hEG_B0K⟩

  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro h
    exact hEDC (PrimCollinearSymm Geo C D E h)

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro h
    exact hCopy.copy_proper
      (PrimCollinearSymm Geo L A B0 h)

  have hPDE_QAB0 :
      Geo.AngleCongruent P D E Q A B0 :=
    hilbert_space_opposite_extension_component
      (Geo := Geo)
      C D E P L A B0 Q
      hCDP hLAQ
      hCDE hLAB0
      hCDE_LAB0

  have hCDPdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) C D P hCDP

  have hPDG : Not (PrimCollinear Geo P D G) := by
    intro h
    have hDPG : PrimCollinear Geo D P G :=
      PrimCollinearSwap Geo P D G h
    exact hCDG
      (hilbert_primCollinear_trans
        Geo C D P G
        hCDPdata.2.1
        hCDPdata.2.2.2.1
        hDPG)

  have hDE : Ne D E :=
    (hilbert_noncollinear_ne_first
      Geo E D C hEDC).symm

  have hAB0 : Ne A B0 :=
    (hilbert_noncollinear_ne_first
      Geo B0 A L hCopy.copy_proper).symm

  have hPDG_QAK :
      Geo.AngleCongruent P D G Q A K :=
    hilbert_space_T15_sameSide
      (Geo := Geo)
      pi sigma
      P D E G
      Q A B0 K
      lineDE base
      hLineDEpi hBaseSigma
      hDE hAB0
      hDlineDE hElineDE
      hAbase hB0base
      hSamePG hSameQK
      hPDG
      hPDE_QAB0 hEDG_B0AK

  have hLAQdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) L A Q hLAQ

  have hQAK : Not (PrimCollinear Geo Q A K) := by
    intro h
    have hAQK : PrimCollinear Geo A Q K :=
      PrimCollinearSwap Geo Q A K h
    exact hLAK
      (hilbert_primCollinear_trans
        Geo L A Q K
        hLAQdata.2.1
        hLAQdata.2.2.2.1
        hAQK)

  have hPDC : Geo.Between P D C :=
    hCDPdata.2.2.2.2

  have hQAL : Geo.Between Q A L :=
    hLAQdata.2.2.2.2

  have hGDC_KAL :
      Geo.AngleCongruent G D C K A L :=
    hilbert_space_adjacent_angles_congruent
      (Geo := Geo)
      P D G C
      Q A K L
      hPDC hQAL
      hPDG hQAK
      hPDG_QAK

  have hCDG_LAK :
      Geo.AngleCongruent C D G L A K :=
    (Geo.angle_congruent_reverse_second
      C D G
      K A L).mp
      ((Geo.angle_congruent_reverse_first
        G D C
        K A L).mp hGDC_KAL)

  have hDCG : Not (PrimCollinear Geo D C G) := by
    intro h
    exact hCDG
      (PrimCollinearSwap Geo D C G h)

  have hALK : Not (PrimCollinear Geo A L K) := by
    intro h
    exact hLAK
      (PrimCollinearSwap Geo A L K h)

  have hCG_LK : Geo.Congruent C G L K :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      D C G
      A L K
      hDCG hALK
      hCopy.second_side
      hDG_AK
      hCDG_LAK

  refine Exists.intro K ?_
  refine And.intro hKsigma ?_
  refine And.intro hCDG ?_
  refine And.intro hB0AK ?_
  refine And.intro hLAK ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hCG_LK ?_
  refine And.intro hEDG_B0AK ?_
  exact hCDG_LAK


/--
Euclid XI.26 for the first adjacent exterior position of the projection
ray.  The source condition is

    HilbertRayMeetsSegment Geo D E C G,

so the ray DE meets the open segment CG.  Together with the proper
component angle EDG this is the first exterior branch in the ray
classification used later for the unrestricted theorem.
-/
theorem euclid_proposition_11_26_of_first_exterior_projection
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hEDG : Not (PrimCollinear Geo E D G))
    (hInside : HilbertRayMeetsSegment Geo D E C G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2

  have hFG : Ne F G := by
    intro hEq
    have hFpi : S.OnPlane F pi := by
      rw [hEq]
      exact hGpi
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi
          (And.intro hEpi
            (And.intro hCpi hFpi))))

  have hBase :=
    hilbert_XI26_copy_base_triangle_on_ray
      (Geo := Geo) D E C A B hTri.1 hAB
  rcases hBase with
    ⟨sigma, B0, L, hCopy⟩

  rcases
      hilbert_XI26_copy_first_exterior_point_strong
        (Geo := Geo)
        sigma D E C A B B0 L G
        hCopy hTri.1 hEDG hInside with
    ⟨K,
      hKsigma,
      hCDG,
      hB0AK,
      hLAK,
      hDG_AK,
      hEG_B0K,
      hCG_LK,
      _hEDG_B0AK,
      _hCDG_LAK⟩

  have hDEG : Not (PrimCollinear Geo D E G) := by
    intro h
    exact hEDG
      (PrimCollinearSwap Geo D E G h)

  have hAB0K : Not (PrimCollinear Geo A B0 K) := by
    intro h
    exact hB0AK
      (PrimCollinearSwap Geo A B0 K h)

  have hDG : Ne D G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) D E G hDEG

  have hEG : Ne E G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) E D G hEDG

  have hCG : Ne C G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) C D G hCDG

  have hAK : Ne A K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) A B0 K hAB0K

  have hB0K : Ne B0 K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) B0 A K hB0AK

  have hLK : Ne L K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) L A K hLAK

  have hTargetNormal :=
    euclid_proposition_11_12
      (Geo := Geo) sigma K hKsigma
  rcases hTargetNormal with
    ⟨targetNormal, hTargetPerp⟩

  have hKnormal : Hinc.OnLine K targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) targetNormal K with
    ⟨R, hOtherData⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo) G F K R hOtherData.1.symm with
    ⟨H, hHeightData⟩

  have hRayH : HilbertSameRay Geo K R H :=
    hHeightData.1

  have hHK : Ne H K :=
    hRayH.2.1

  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hOtherData.1.symm
      hKnormal hOtherData.2
      hRayH.2.2.1

  have hHeight : Geo.Congruent G F K H :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      K H G F
      hHK.symm hHeightData.2

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHK
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        sigma targetNormal K H
        hTargetPerp hHnormal hOn)

  have hDF_AH : Geo.Congruent D F A H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F D K H A
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hDpi hCopy.A_on
      hDG hAK
      hDG_AK hHeight

  have hEF_B0H : Geo.Congruent E F B0 H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F E K H B0
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hEpi hCopy.B0_on
      hEG hB0K
      hEG_B0K hHeight

  have hCF_LH : Geo.Congruent C F L H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F C K H L
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hCpi hCopy.L_on
      hCG hLK
      hCG_LK hHeight

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo)
      sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on
      hCopy.base_proper hHsigma

  have hAuxTri : HilbertTrihedralConfiguration Geo A B0 L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo)
      sigma A B0 L H
      hCopy.A_on hCopy.B0_on hCopy.L_on
      hCopy.copy_proper hHsigma

  have hDEF : Not (PrimCollinear Geo D E F) := by
    intro hCol
    exact hTri.2.2.1
      (PrimCollinearSymm Geo E D F
        (PrimCollinearSwap Geo D E F hCol))

  have hDCF : Not (PrimCollinear Geo D C F) := by
    intro hCol
    exact hTri.2.1
      (PrimCollinearSwap Geo D C F hCol)

  have hAB0H : Not (PrimCollinear Geo A B0 H) := by
    intro hCol
    exact hAuxTri.2.2.1
      (PrimCollinearSymm Geo B0 A H
        (PrimCollinearSwap Geo A B0 H hCol))

  have hALH : Not (PrimCollinear Geo A L H) := by
    intro hCol
    exact hTargetTri.2.1
      (PrimCollinearSwap Geo A L H hCol)

  have hEDF_B0AH : Geo.AngleCongruent E D F B0 A H :=
    hilbert_space_sss_angleA
      (Geo := Geo)
      D E F A B0 H
      hDEF hAB0H
      hCopy.first_side hEF_B0H hDF_AH

  have hCDF_LAH : Geo.AngleCongruent C D F L A H :=
    hilbert_space_sss_angleA
      (Geo := Geo)
      D C F A L H
      hDCF hALH
      hCopy.second_side hCF_LH hDF_AH

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo C D F L A H hCDF_LAH

  have hB0AH_EDF : Geo.AngleCongruent B0 A H E D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo E D F B0 A H hEDF_B0AH

  have hHAB0_FDE : Geo.AngleCongruent H A B0 F D E :=
    (Geo.angle_congruent_reverse_second
      H A B0 E D F).mp
      ((Geo.angle_congruent_reverse_first
        B0 A H E D F).mp hB0AH_EDF)

  have hAngleEq : Geo.Angle H A B = Geo.Angle H A B0 :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo)
      A H B B0 hCopy.first_ray

  have hThird : Geo.AngleCongruent H A B F D E := by
    unfold Geometry.Geo.AngleCongruent at hHAB0_FDE |-
    rw [hAngleEq]
    exact hHAB0_FDE

  exact
    Exists.intro L
      (Exists.intro H
        (And.intro hTargetTri
          (And.intro hCopy.base_angle
            (And.intro hSecond hThird))))


/-!
# Euclid XI.26: second adjacent exterior sector by symmetry

The first adjacent exterior sector is now complete, including the lift
from the copied base plane to the fourth vertex H.

The second adjacent exterior sector

    HilbertRayMeetsSegment Geo D C E G

is mathematically the first one with E and C interchanged.  We exploit
that symmetry at the base-copy level.  The swapped source triangle
D,C,E is represented by the swapped copied triangle A,L,B0.

The prescribed output ray AB is not changed.  Therefore we do not apply
the full first-exterior XI.26 theorem after swapping labels; instead we
reuse only its point-copy theorem and then a proposition-level generic
lifting helper.
-/


/--
Reverse the two noninitial vertices of an XI.26 base copy.

The source copy

    D,E,C  ->  A,B0,L

becomes

    D,C,E  ->  A,L,B0.

For the auxiliary `B` field of `HilbertXI26BaseCopy` we use `L` itself;
this is sufficient because the swapped copy is used only as an internal
metric certificate, not as the final prescribed-ray output.
-/
theorem hilbert_XI26_swap_base_copy
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L) :
    HilbertXI26BaseCopy Geo sigma D C E A L L B0 := by

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro h
    exact hCopy.copy_proper
      (PrimCollinearSymm Geo L A B0 h)

  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first
      Geo L A B0 hLAB0

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hCopy.A_on⟩

  let Lp : PlanePoint Geo sigma :=
    ⟨L, hCopy.L_on⟩

  have hRayLLPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Lp Lp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma) Ap Lp
      (by
        intro hEq
        exact hLA (congrArg Subtype.val hEq))

  have hRayLL : HilbertSameRay Geo A L L := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Lp Lp).mp hRayLLPlane
    simpa [Ap, Lp] using hAmbient

  have hCE_LB0 : Geo.Congruent C E L B0 :=
    (Geo.congruent_reverse_second C E B0 L).mp
      ((Geo.congruent_reverse_first E C B0 L).mp
        hCopy.third_side)

  have hLAB0_CDE :
      Geo.AngleCongruent L A B0 C D E :=
    (Geo.angle_congruent_reverse_second
      L A B0 E D C).mp
      ((Geo.angle_congruent_reverse_first
        B0 A L E D C).mp hCopy.copy_angle)

  exact
    { A_on := hCopy.A_on
      B_on := hCopy.L_on
      B0_on := hCopy.L_on
      L_on := hCopy.B0_on
      first_ray := hRayLL
      first_side := hCopy.second_side
      second_side := hCopy.first_side
      third_side := hCE_LB0
      base_proper := hLAB0
      copy_proper := hLAB0
      base_angle := hLAB0_CDE
      copy_angle := hLAB0_CDE }


/--
Generic XI.26 lifting stage once a copied base point K is already known.

The input consists exactly of the three base-plane distances from G and
the proper source/target radial angles needed to make those distances
nondegenerate.  The construction of the target normal, the copied height,
and the three right-triangle comparisons are independent of how K was
obtained.
-/
theorem hilbert_XI26_lift_base_point_copy
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi sigma : S.Plane)
    (normal : Geo.Line)
    (G B0 L K : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hKsigma : S.OnPlane K sigma)
    (hEDG : Not (PrimCollinear Geo E D G))
    (hCDG : Not (PrimCollinear Geo C D G))
    (hB0AK : Not (PrimCollinear Geo B0 A K))
    (hLAK : Not (PrimCollinear Geo L A K))
    (hDG_AK : Geo.Congruent D G A K)
    (hEG_B0K : Geo.Congruent E G B0 K)
    (hCG_LK : Geo.Congruent C G L K) :
    exists H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2

  have hFG : Ne F G := by
    intro hEq
    have hFpi : S.OnPlane F pi := by
      rw [hEq]
      exact hGpi
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi
          (And.intro hEpi
            (And.intro hCpi hFpi))))

  have hDEG : Not (PrimCollinear Geo D E G) := by
    intro h
    exact hEDG
      (PrimCollinearSwap Geo D E G h)

  have hDCG : Not (PrimCollinear Geo D C G) := by
    intro h
    exact hCDG
      (PrimCollinearSwap Geo D C G h)

  have hAB0K : Not (PrimCollinear Geo A B0 K) := by
    intro h
    exact hB0AK
      (PrimCollinearSwap Geo A B0 K h)

  have hALK : Not (PrimCollinear Geo A L K) := by
    intro h
    exact hLAK
      (PrimCollinearSwap Geo A L K h)

  have hDG : Ne D G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) D E G hDEG

  have hEG : Ne E G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) E D G hEDG

  have hCG : Ne C G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) C D G hCDG

  have hAK : Ne A K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) A B0 K hAB0K

  have hB0K : Ne B0 K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) B0 A K hB0AK

  have hLK : Ne L K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) L A K hLAK

  rcases
      euclid_proposition_11_12
        (Geo := Geo) sigma K hKsigma with
    ⟨targetNormal, hTargetPerp⟩

  have hKnormal : Hinc.OnLine K targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) targetNormal K with
    ⟨R, hOtherData⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo) G F K R hOtherData.1.symm with
    ⟨H, hHeightData⟩

  have hRayH : HilbertSameRay Geo K R H :=
    hHeightData.1

  have hHK : Ne H K :=
    hRayH.2.1

  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hOtherData.1.symm
      hKnormal hOtherData.2
      hRayH.2.2.1

  have hHeight : Geo.Congruent G F K H :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      K H G F
      hHK.symm hHeightData.2

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHK
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        sigma targetNormal K H
        hTargetPerp hHnormal hOn)

  have hDF_AH : Geo.Congruent D F A H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F D K H A
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hDpi hCopy.A_on
      hDG hAK
      hDG_AK hHeight

  have hEF_B0H : Geo.Congruent E F B0 H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F E K H B0
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hEpi hCopy.B0_on
      hEG hB0K
      hEG_B0K hHeight

  have hCF_LH : Geo.Congruent C F L H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F C K H L
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hCpi hCopy.L_on
      hCG hLK
      hCG_LK hHeight

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo)
      sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on
      hCopy.base_proper hHsigma

  have hAuxTri : HilbertTrihedralConfiguration Geo A B0 L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo)
      sigma A B0 L H
      hCopy.A_on hCopy.B0_on hCopy.L_on
      hCopy.copy_proper hHsigma

  have hDEF : Not (PrimCollinear Geo D E F) := by
    intro hCol
    exact hTri.2.2.1
      (PrimCollinearSymm Geo E D F
        (PrimCollinearSwap Geo D E F hCol))

  have hDCF : Not (PrimCollinear Geo D C F) := by
    intro hCol
    exact hTri.2.1
      (PrimCollinearSwap Geo D C F hCol)

  have hAB0H : Not (PrimCollinear Geo A B0 H) := by
    intro hCol
    exact hAuxTri.2.2.1
      (PrimCollinearSymm Geo B0 A H
        (PrimCollinearSwap Geo A B0 H hCol))

  have hALH : Not (PrimCollinear Geo A L H) := by
    intro hCol
    exact hTargetTri.2.1
      (PrimCollinearSwap Geo A L H hCol)

  have hEDF_B0AH : Geo.AngleCongruent E D F B0 A H :=
    hilbert_space_sss_angleA
      (Geo := Geo)
      D E F A B0 H
      hDEF hAB0H
      hCopy.first_side hEF_B0H hDF_AH

  have hCDF_LAH : Geo.AngleCongruent C D F L A H :=
    hilbert_space_sss_angleA
      (Geo := Geo)
      D C F A L H
      hDCF hALH
      hCopy.second_side hCF_LH hDF_AH

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo C D F L A H hCDF_LAH

  have hB0AH_EDF : Geo.AngleCongruent B0 A H E D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo E D F B0 A H hEDF_B0AH

  have hHAB0_FDE : Geo.AngleCongruent H A B0 F D E :=
    (Geo.angle_congruent_reverse_second
      H A B0 E D F).mp
      ((Geo.angle_congruent_reverse_first
        B0 A H E D F).mp hB0AH_EDF)

  have hAngleEq : Geo.Angle H A B = Geo.Angle H A B0 :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo)
      A H B B0 hCopy.first_ray

  have hThird : Geo.AngleCongruent H A B F D E := by
    unfold Geometry.Geo.AngleCongruent at hHAB0_FDE |-
    rw [hAngleEq]
    exact hHAB0_FDE

  exact
    Exists.intro H
      (And.intro hTargetTri
        (And.intro hCopy.base_angle
          (And.intro hSecond hThird)))


/--
Strong point-copy theorem for the second adjacent exterior sector.

The source condition

    HilbertRayMeetsSegment Geo D C E G

is the first-exterior condition after interchanging E and C.  The target
copy is interchanged simultaneously, so the resulting data are returned
in the original XI.26 labels.
-/
theorem hilbert_XI26_copy_second_exterior_point_strong
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hCDG : Not (PrimCollinear Geo C D G))
    (hInside : HilbertRayMeetsSegment Geo D C E G) :
    exists K : Geo.Point,
      S.OnPlane K sigma /\
      Not (PrimCollinear Geo E D G) /\
      Not (PrimCollinear Geo B0 A K) /\
      Not (PrimCollinear Geo L A K) /\
      Geo.Congruent D G A K /\
      Geo.Congruent E G B0 K /\
      Geo.Congruent C G L K /\
      Geo.AngleCongruent E D G B0 A K /\
      Geo.AngleCongruent C D G L A K := by

  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro h
    exact hEDC
      (PrimCollinearSymm Geo C D E h)

  have hSwap :
      HilbertXI26BaseCopy Geo sigma D C E A L L B0 :=
    hilbert_XI26_swap_base_copy
      (Geo := Geo)
      sigma D E C A B B0 L hCopy

  rcases
      hilbert_XI26_copy_first_exterior_point_strong
        (Geo := Geo)
        sigma
        D C E
        A L L B0 G
        hSwap hCDE hCDG hInside with
    ⟨K,
      hKsigma,
      hEDG,
      hLAK,
      hB0AK,
      hDG_AK,
      hCG_LK,
      hEG_B0K,
      hCDG_LAK,
      hEDG_B0AK⟩

  refine Exists.intro K ?_
  refine And.intro hKsigma ?_
  refine And.intro hEDG ?_
  refine And.intro hB0AK ?_
  refine And.intro hLAK ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hCG_LK ?_
  refine And.intro hEDG_B0AK ?_
  exact hCDG_LAK


/--
Euclid XI.26 for the second adjacent exterior position of the projection
ray.  Here the ray DC meets the open segment EG.
-/
theorem euclid_proposition_11_26_of_second_exterior_projection
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hCDG : Not (PrimCollinear Geo C D G))
    (hInside : HilbertRayMeetsSegment Geo D C E G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  rcases
      hilbert_XI26_copy_base_triangle_on_ray
        (Geo := Geo)
        D E C A B hTri.1 hAB with
    ⟨sigma, B0, L, hCopy⟩

  rcases
      hilbert_XI26_copy_second_exterior_point_strong
        (Geo := Geo)
        sigma D E C A B B0 L G
        hCopy hTri.1 hCDG hInside with
    ⟨K,
      hKsigma,
      hEDG,
      hB0AK,
      hLAK,
      hDG_AK,
      hEG_B0K,
      hCG_LK,
      _hEDG_B0AK,
      _hCDG_LAK⟩

  rcases
      hilbert_XI26_lift_base_point_copy
        (Geo := Geo)
        D E C F A B
        pi sigma normal
        G B0 L K
        hTri
        hDpi hEpi hCpi
        hFnormal hPerp
        hCopy hKsigma
        hEDG hCDG
        hB0AK hLAK
        hDG_AK hEG_B0K hCG_LK with
    ⟨H, hRealizes⟩

  exact
    Exists.intro L
      (Exists.intro H hRealizes)


/--
Build the auxiliary copied triangle used in the cyclic XI.26 sector.

From

    D,E,C  ->  A,B0,L
    C-D-J

construct M with L-A-M so that

    D,J,E  ->  A,M,B0

is an XI.26 base copy.
-/
theorem hilbert_XI26_cyclic_auxiliary_base_copy
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L J : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hCDJ : Geo.Between C D J) :
    exists M : Geo.Point,
      S.OnPlane M sigma /\
      Geo.Between L A M /\
      Not (PrimCollinear Geo J D E) /\
      Not (PrimCollinear Geo M A B0) /\
      HilbertXI26BaseCopy Geo sigma D J E A M M B0 := by

  have hCDJdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) C D J hCDJ

  have hDJ : Ne D J := hCDJdata.2.1
  have hCDJcol : PrimCollinear Geo C D J :=
    hCDJdata.2.2.2.1

  have hJDE : Not (PrimCollinear Geo J D E) := by
    intro hCol
    have hDJE : PrimCollinear Geo D J E :=
      PrimCollinearSwap Geo J D E hCol
    have hCDE : PrimCollinear Geo C D E :=
      hilbert_primCollinear_trans
        Geo C D J E
        hDJ hCDJcol hDJE
    exact hEDC
      (PrimCollinearSymm Geo C D E hCDE)

  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro h
    exact hEDC (PrimCollinearSymm Geo C D E h)

  have hLAB0 : Not (PrimCollinear Geo L A B0) := by
    intro h
    exact hCopy.copy_proper
      (PrimCollinearSymm Geo L A B0 h)

  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first
      Geo L A B0 hLAB0

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo) L A hLA with
    ⟨T, hLAT⟩

  have hLATdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) L A T hLAT

  have hAT : Ne A T := hLATdata.2.1
  have hLATcol : PrimCollinear Geo L A T :=
    hLATdata.2.2.2.1

  have hTsigma : S.OnPlane T sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma L A T hLA
      hCopy.L_on hCopy.A_on hLATcol

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        D J A T hAT with
    ⟨M, hRayTM, hAM_DJ⟩

  have hAM : Ne A M := hRayTM.2.1.symm
  have hMA : Ne M A := hRayTM.2.1

  have hMsigma : S.OnPlane M sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma A T M hAT
      hCopy.A_on hTsigma hRayTM.2.2.1

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hCopy.A_on⟩
  let Lp : PlanePoint Geo sigma :=
    ⟨L, hCopy.L_on⟩

  have hRayLLPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Lp Lp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma) Ap Lp
      (by
        intro hEq
        exact hLA (congrArg Subtype.val hEq))

  have hRayLL : HilbertSameRay Geo A L L := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Lp Lp).mp hRayLLPlane
    simpa [Ap, Lp] using hAmbient

  have hLAM : Geo.Between L A M :=
    hilbert_space_between_transport_sameRays
      (Geo := Geo)
      L A T L M
      hLAT hRayLL hRayTM

  have hLAMdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) L A M hLAM

  have hMAB0 : Not (PrimCollinear Geo M A B0) := by
    intro hCol
    have hAMB0 : PrimCollinear Geo A M B0 :=
      PrimCollinearSwap Geo M A B0 hCol
    have hLAB0col : PrimCollinear Geo L A B0 :=
      hilbert_primCollinear_trans
        Geo L A M B0
        hLAMdata.2.1
        hLAMdata.2.2.2.1
        hAMB0
    exact hLAB0 hLAB0col

  have hDJ_AM : Geo.Congruent D J A M :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A M D J hAM hAM_DJ

  have hCDE_LAB0 :
      Geo.AngleCongruent C D E L A B0 :=
    hilbert_XI26_first_exterior_base_component_angle
      (Geo := Geo)
      sigma D E C A B B0 L hCopy

  have hEDJ_B0AM :
      Geo.AngleCongruent E D J B0 A M :=
    hilbert_space_adjacent_angles_congruent
      (Geo := Geo)
      C D E J
      L A B0 M
      hCDJ hLAM
      hCDE hLAB0
      hCDE_LAB0

  have hJDE_MAB0 :
      Geo.AngleCongruent J D E M A B0 :=
    (Geo.angle_congruent_reverse_second
      J D E B0 A M).mp
      ((Geo.angle_congruent_reverse_first
        E D J B0 A M).mp hEDJ_B0AM)

  have hDJE : Not (PrimCollinear Geo D J E) := by
    intro h
    exact hJDE (PrimCollinearSwap Geo D J E h)

  have hAMB0 : Not (PrimCollinear Geo A M B0) := by
    intro h
    exact hMAB0 (PrimCollinearSwap Geo A M B0 h)

  have hJE_MB0 : Geo.Congruent J E M B0 :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      D J E
      A M B0
      hDJE hAMB0
      hDJ_AM hCopy.first_side
      hJDE_MAB0

  let Mp : PlanePoint Geo sigma :=
    ⟨M, hMsigma⟩

  have hRayMMPlane :
      HilbertSameRay (PlaneGeo Geo sigma) Ap Mp Mp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma) Ap Mp
      (by
        intro hEq
        exact hMA (congrArg Subtype.val hEq))

  have hRayMM : HilbertSameRay Geo A M M := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) sigma Ap Mp Mp).mp hRayMMPlane
    simpa [Ap, Mp] using hAmbient

  have hMAB0_JDE :
      Geo.AngleCongruent M A B0 J D E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo J D E M A B0 hJDE_MAB0

  refine Exists.intro M ?_
  refine And.intro hMsigma ?_
  refine And.intro hLAM ?_
  refine And.intro hJDE ?_
  refine And.intro hMAB0 ?_
  exact
    { A_on := hCopy.A_on
      B_on := hMsigma
      B0_on := hMsigma
      L_on := hCopy.B0_on
      first_ray := hRayMM
      first_side := hDJ_AM
      second_side := hCopy.first_side
      third_side := hJE_MB0
      base_proper := hMAB0
      copy_proper := hMAB0
      base_angle := hMAB0_JDE
      copy_angle := hMAB0_JDE }


/--
Metric closure of the cyclic/opposite sector.

The classification witness J satisfies C-D-J and E-J-G.  The auxiliary
base copy from the preceding theorem converts this to the already solved
first-exterior problem for D,J,E.  The result is then transported back to
C/L by spatial Theorem 14 and one final SAS.
-/
theorem hilbert_XI26_copy_cyclic_point_strong
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G J : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hCDG : Not (PrimCollinear Geo C D G))
    (hCDJ : Geo.Between C D J)
    (hEJG : Geo.Between E J G) :
    exists K : Geo.Point,
      S.OnPlane K sigma /\
      Not (PrimCollinear Geo E D G) /\
      Not (PrimCollinear Geo B0 A K) /\
      Not (PrimCollinear Geo L A K) /\
      Geo.Congruent D G A K /\
      Geo.Congruent E G B0 K /\
      Geo.Congruent C G L K /\
      Geo.AngleCongruent E D G B0 A K /\
      Geo.AngleCongruent C D G L A K := by

  rcases
      hilbert_XI26_cyclic_auxiliary_base_copy
        (Geo := Geo)
        sigma D E C A B B0 L J
        hCopy hEDC hCDJ with
    ⟨M, hMsigma, hLAM, hJDE, hMAB0, hAux⟩

  have hCDJdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) C D J hCDJ

  have hDJ : Ne D J := hCDJdata.2.1
  have hCDJcol : PrimCollinear Geo C D J :=
    hCDJdata.2.2.2.1

  have hJDG : Not (PrimCollinear Geo J D G) := by
    intro hCol
    have hDJG : PrimCollinear Geo D J G :=
      PrimCollinearSwap Geo J D G hCol
    exact hCDG
      (hilbert_primCollinear_trans
        Geo C D J G
        hDJ hCDJcol hDJG)

  have hDJE : Not (PrimCollinear Geo D J E) := by
    intro h
    exact hJDE (PrimCollinearSwap Geo D J E h)

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo) D J E hDJE with
    ⟨rho, hDrho, hJrho, _hErho⟩

  let Dp : PlanePoint Geo rho :=
    ⟨D, hDrho⟩
  let Jp : PlanePoint Geo rho :=
    ⟨J, hJrho⟩

  have hRayJJPlane :
      HilbertSameRay (PlaneGeo Geo rho) Dp Jp Jp :=
    hilbert_sameRay_refl
      (PlaneGeo Geo rho) Dp Jp
      (by
        intro hEq
        exact hDJ.symm (congrArg Subtype.val hEq))

  have hRayJJ : HilbertSameRay Geo D J J := by
    have hAmbient :=
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo) rho Dp Jp Jp).mp hRayJJPlane
    simpa [Dp, Jp] using hAmbient

  have hMeet : HilbertRayMeetsSegment Geo D J E G :=
    ⟨J, hEJG, hRayJJ⟩

  rcases
      hilbert_XI26_copy_first_exterior_point_strong
        (Geo := Geo)
        sigma
        D J E
        A M M B0 G
        hAux hJDE hJDG hMeet with
    ⟨K,
      hKsigma,
      hEDG,
      hMAK,
      hB0AK,
      hDG_AK,
      _hJG_MK,
      hEG_B0K,
      hJDG_MAK,
      hEDG_B0AK⟩

  have hLAMdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) L A M hLAM

  have hMAL : Geo.Between M A L :=
    hLAMdata.2.2.2.2

  have hJDC : Geo.Between J D C :=
    hCDJdata.2.2.2.2

  have hGDC_KAL :
      Geo.AngleCongruent G D C K A L :=
    hilbert_space_adjacent_angles_congruent
      (Geo := Geo)
      J D G C
      M A K L
      hJDC hMAL
      hJDG hMAK
      hJDG_MAK

  have hCDG_LAK :
      Geo.AngleCongruent C D G L A K :=
    (Geo.angle_congruent_reverse_second
      C D G K A L).mp
      ((Geo.angle_congruent_reverse_first
        G D C K A L).mp hGDC_KAL)

  have hLA : Ne L A :=
    hilbert_noncollinear_ne_first
      Geo L A B0
      (by
        intro h
        exact hCopy.copy_proper
          (PrimCollinearSymm Geo L A B0 h))

  have hAL : Ne A L := hLA.symm

  have hLAK : Not (PrimCollinear Geo L A K) := by
    intro hCol
    have hMALcol : PrimCollinear Geo M A L :=
      PrimCollinearSymm Geo L A M hLAMdata.2.2.2.1
    have hALK : PrimCollinear Geo A L K :=
      PrimCollinearSwap Geo L A K hCol
    have hMAKcol : PrimCollinear Geo M A K :=
      hilbert_primCollinear_trans
        Geo M A L K
        hAL
        hMALcol hALK
    exact hMAK hMAKcol

  have hDCG : Not (PrimCollinear Geo D C G) := by
    intro h
    exact hCDG (PrimCollinearSwap Geo D C G h)

  have hALK : Not (PrimCollinear Geo A L K) := by
    intro h
    exact hLAK (PrimCollinearSwap Geo A L K h)

  have hCG_LK : Geo.Congruent C G L K :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      D C G
      A L K
      hDCG hALK
      hCopy.second_side
      hDG_AK
      hCDG_LAK

  refine Exists.intro K ?_
  refine And.intro hKsigma ?_
  refine And.intro hEDG ?_
  refine And.intro hB0AK ?_
  refine And.intro hLAK ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hCG_LK ?_
  refine And.intro hEDG_B0AK ?_
  exact hCDG_LAK


/--
Euclid XI.26 for the cyclic/opposite position of the projection ray.

The hypotheses `hCDJ` and `hEJG` are exactly the fourth alternative of
`hilbert_space_three_rays_order_or_cyclic_in_plane`.
-/
theorem euclid_proposition_11_26_of_cyclic_projection
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G J : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hCDG : Not (PrimCollinear Geo C D G))
    (hCDJ : Geo.Between C D J)
    (hEJG : Geo.Between E J G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  rcases
      hilbert_XI26_copy_base_triangle_on_ray
        (Geo := Geo)
        D E C A B hTri.1 hAB with
    ⟨sigma, B0, L, hCopy⟩

  rcases
      hilbert_XI26_copy_cyclic_point_strong
        (Geo := Geo)
        sigma D E C A B B0 L G J
        hCopy hTri.1 hCDG hCDJ hEJG with
    ⟨K,
      hKsigma,
      hEDG,
      hB0AK,
      hLAK,
      hDG_AK,
      hEG_B0K,
      hCG_LK,
      _hEDG_B0AK,
      _hCDG_LAK⟩

  rcases
      hilbert_XI26_lift_base_point_copy
        (Geo := Geo)
        D E C F A B
        pi sigma normal
        G B0 L K
        hTri
        hDpi hEpi hCpi
        hFnormal hPerp
        hCopy hKsigma
        hEDG hCDG
        hB0AK hLAK
        hDG_AK hEG_B0K hCG_LK with
    ⟨H, hRealizes⟩

  exact
    Exists.intro L
      (Exists.intro H hRealizes)


/-!
# Euclid XI.26: opposite boundary of the first base ray

The remaining boundary position treated here is

    E-D-G.

Thus the projection ray DG is the ray opposite DE.

This file first records a generic lifting theorem whose hypotheses are
the six endpoint inequalities actually needed by the metric lifting
argument.  Unlike `hilbert_XI26_lift_base_point_copy`, it does not require
the radial angles EDG and B0AK to be proper.  This is necessary on the
present boundary, where both triples are collinear.

The planar metric construction is elementary:

* extend B0-A beyond A;
* lay off DG on that opposite target ray, obtaining K;
* segment additivity gives EG ~= B0K from E-D-G and B0-A-K;
* spatial Theorem 14 transports the supplementary angle CDG to LAK;
* spatial SAS gives CG ~= LK.

No angle-addition theorem is used.
-/

/--
Generic XI.26 lifting once the three copied base distances are known,
with endpoint nondegeneracy supplied directly.

This is the same lifting argument as
`hilbert_XI26_lift_base_point_copy`, but it also applies when one radial
angle is degenerate (as in the opposite-boundary cases).
-/
theorem hilbert_XI26_lift_base_point_copy_ne
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi sigma : S.Plane)
    (normal : Geo.Line)
    (G B0 L K : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hKsigma : S.OnPlane K sigma)
    (hDG : Ne D G)
    (hEG : Ne E G)
    (hCG : Ne C G)
    (hAK : Ne A K)
    (hB0K : Ne B0 K)
    (hLK : Ne L K)
    (hDG_AK : Geo.Congruent D G A K)
    (hEG_B0K : Geo.Congruent E G B0 K)
    (hCG_LK : Geo.Congruent C G L K) :
    exists H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  have hGpi : S.OnPlane G pi :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp).2

  have hFG : Ne F G := by
    intro hEq
    have hFpi : S.OnPlane F pi := by
      rw [hEq]
      exact hGpi
    exact hTri.2.2.2
      (Exists.intro pi
        (And.intro hDpi
          (And.intro hEpi
            (And.intro hCpi hFpi))))

  rcases
      euclid_proposition_11_12
        (Geo := Geo) sigma K hKsigma with
    ⟨targetNormal, hTargetPerp⟩

  have hKnormal : Hinc.OnLine K targetNormal :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hTargetPerp).1

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) targetNormal K with
    ⟨R, hOtherData⟩

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo) G F K R hOtherData.1.symm with
    ⟨H, hHeightData⟩

  have hRayH : HilbertSameRay Geo K R H :=
    hHeightData.1

  have hHK : Ne H K :=
    hRayH.2.1

  have hHnormal : Hinc.OnLine H targetNormal :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hOtherData.1.symm
      hKnormal hOtherData.2
      hRayH.2.2.1

  have hHeight : Geo.Congruent G F K H :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      K H G F
      hHK.symm hHeightData.2

  have hHsigma : Not (S.OnPlane H sigma) := by
    intro hOn
    exact hHK
      (hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        sigma targetNormal K H
        hTargetPerp hHnormal hOn)

  have hDF_AH : Geo.Congruent D F A H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F D K H A
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hDpi hCopy.A_on
      hDG hAK
      hDG_AK hHeight

  have hEF_B0H : Geo.Congruent E F B0 H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F E K H B0
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hEpi hCopy.B0_on
      hEG hB0K
      hEG_B0K hHeight

  have hCF_LH : Geo.Congruent C F L H :=
    hilbert_space_lifted_distance_of_equal_base_height
      (Geo := Geo)
      pi sigma normal targetNormal
      G F C K H L
      hPerp hTargetPerp
      hFnormal hHnormal
      hFG hHK
      hCpi hCopy.L_on
      hCG hLK
      hCG_LK hHeight

  have hTargetTri : HilbertTrihedralConfiguration Geo A B L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo)
      sigma A B L H
      hCopy.A_on hCopy.B_on hCopy.L_on
      hCopy.base_proper hHsigma

  have hAuxTri : HilbertTrihedralConfiguration Geo A B0 L H :=
    hilbert_space_trihedral_of_point_off_base
      (Geo := Geo)
      sigma A B0 L H
      hCopy.A_on hCopy.B0_on hCopy.L_on
      hCopy.copy_proper hHsigma

  have hDEF : Not (PrimCollinear Geo D E F) := by
    intro hCol
    exact hTri.2.2.1
      (PrimCollinearSymm Geo E D F
        (PrimCollinearSwap Geo D E F hCol))

  have hDCF : Not (PrimCollinear Geo D C F) := by
    intro hCol
    exact hTri.2.1
      (PrimCollinearSwap Geo D C F hCol)

  have hAB0H : Not (PrimCollinear Geo A B0 H) := by
    intro hCol
    exact hAuxTri.2.2.1
      (PrimCollinearSymm Geo B0 A H
        (PrimCollinearSwap Geo A B0 H hCol))

  have hALH : Not (PrimCollinear Geo A L H) := by
    intro hCol
    exact hTargetTri.2.1
      (PrimCollinearSwap Geo A L H hCol)

  have hEDF_B0AH : Geo.AngleCongruent E D F B0 A H :=
    hilbert_space_sss_angleA
      (Geo := Geo)
      D E F A B0 H
      hDEF hAB0H
      hCopy.first_side hEF_B0H hDF_AH

  have hCDF_LAH : Geo.AngleCongruent C D F L A H :=
    hilbert_space_sss_angleA
      (Geo := Geo)
      D C F A L H
      hDCF hALH
      hCopy.second_side hCF_LH hDF_AH

  have hSecond : Geo.AngleCongruent L A H C D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo C D F L A H hCDF_LAH

  have hB0AH_EDF : Geo.AngleCongruent B0 A H E D F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo E D F B0 A H hEDF_B0AH

  have hHAB0_FDE : Geo.AngleCongruent H A B0 F D E :=
    (Geo.angle_congruent_reverse_second
      H A B0 E D F).mp
      ((Geo.angle_congruent_reverse_first
        B0 A H E D F).mp hB0AH_EDF)

  have hAngleEq : Geo.Angle H A B = Geo.Angle H A B0 :=
    hilbert_space_angle_eq_of_sameRay_second
      (Geo := Geo)
      A H B B0 hCopy.first_ray

  have hThird : Geo.AngleCongruent H A B F D E := by
    unfold Geometry.Geo.AngleCongruent at hHAB0_FDE |-
    rw [hAngleEq]
    exact hHAB0_FDE

  exact
    Exists.intro H
      (And.intro hTargetTri
        (And.intro hCopy.base_angle
          (And.intro hSecond hThird)))


/--
Metric copy for the boundary position E-D-G.

The copied radial point K lies on the ray from A opposite AB0, so
B0-A-K.  All three base distances are obtained without any degenerate
angle congruence.
-/
theorem hilbert_XI26_copy_opposite_first_ray_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hEDG : Geo.Between E D G) :
    exists K : Geo.Point,
      S.OnPlane K sigma /\
      Geo.Between B0 A K /\
      Not (PrimCollinear Geo C D G) /\
      Not (PrimCollinear Geo L A K) /\
      Geo.Congruent D G A K /\
      Geo.Congruent E G B0 K /\
      Geo.Congruent C G L K /\
      Geo.AngleCongruent C D G L A K := by

  have hEDGdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) E D G hEDG

  have hDG : Ne D G :=
    hEDGdata.2.1

  have hEDGcol : PrimCollinear Geo E D G :=
    hEDGdata.2.2.2.1

  have hB0A : Ne B0 A :=
    hilbert_noncollinear_ne_first
      Geo B0 A L hCopy.copy_proper

  have hAB0 : Ne A B0 :=
    hB0A.symm

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo) B0 A hB0A with
    ⟨T, hB0AT⟩

  have hB0ATdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) B0 A T hB0AT

  have hAT : Ne A T :=
    hB0ATdata.2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo) D G A T hAT with
    ⟨K, hRayTK, hAK_DG⟩

  have hAK : Ne A K :=
    hRayTK.2.1.symm

  have hDG_AK : Geo.Congruent D G A K :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A K D G
      hAK hAK_DG

  have hRayB0B0 : HilbertSameRay Geo A B0 B0 := by
    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          A B0 hAB0 with
      ⟨carrier, hAcarrier, hB0carrier⟩
    refine
      ⟨hB0A,
       hB0A,
       ?_,
       ?_⟩
    · exact
        ⟨carrier,
         hAcarrier,
         hB0carrier,
         hB0carrier⟩
    · intro hB0AB0
      exact
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          B0 A B0 hB0AB0).2.2.1 rfl

  have hB0AK : Geo.Between B0 A K :=
    hilbert_space_between_transport_sameRays
      (Geo := Geo)
      B0 A T
      B0 K
      hB0AT
      hRayB0B0
      hRayTK

  have hB0AKdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) B0 A K hB0AK

  have hB0AKcol : PrimCollinear Geo B0 A K :=
    hB0AKdata.2.2.2.1

  have hKsigma : S.OnPlane K sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma B0 A K hB0A
      hCopy.B0_on hCopy.A_on hB0AKcol

  have hED_B0A : Geo.Congruent E D B0 A :=
    (Geo.congruent_reverse_second
      E D A B0).mp
      ((Geo.congruent_reverse_first
        D E A B0).mp hCopy.first_side)

  have hEG_B0K : Geo.Congruent E G B0 K :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      E D G
      B0 A K
      hEDG
      hB0AK
      hED_B0A
      hDG_AK

  have hCDG : Not (PrimCollinear Geo C D G) := by
    intro hCol
    have hDGC : PrimCollinear Geo D G C :=
      PrimCollinearCycle Geo C D G hCol
    have hEDCcol : PrimCollinear Geo E D C :=
      hilbert_primCollinear_trans
        Geo E D G C
        hDG
        hEDGcol
        hDGC
    exact hEDC hEDCcol

  have hLAK : Not (PrimCollinear Geo L A K) := by
    intro hCol
    have hAKL : PrimCollinear Geo A K L :=
      PrimCollinearCycle Geo L A K hCol
    have hB0AL : PrimCollinear Geo B0 A L :=
      hilbert_primCollinear_trans
        Geo B0 A K L
        hAK
        hB0AKcol
        hAKL
    exact hCopy.copy_proper hB0AL

  have hEDC_B0AL :
      Geo.AngleCongruent E D C B0 A L :=
    Geometry.Geo.angle_congruent_symmetry
      Geo B0 A L E D C hCopy.copy_angle

  have hCDG_LAK :
      Geo.AngleCongruent C D G L A K :=
    hilbert_space_adjacent_angles_congruent
      (Geo := Geo)
      E D C G
      B0 A L K
      hEDG hB0AK
      hEDC hCopy.copy_proper
      hEDC_B0AL

  have hDCG : Not (PrimCollinear Geo D C G) := by
    intro h
    exact hCDG
      (PrimCollinearSwap Geo D C G h)

  have hALK : Not (PrimCollinear Geo A L K) := by
    intro h
    exact hLAK
      (PrimCollinearSwap Geo A L K h)

  have hCG_LK : Geo.Congruent C G L K :=
    hilbert_space_sas_third_side
      (Geo := Geo)
      D C G
      A L K
      hDCG hALK
      hCopy.second_side
      hDG_AK
      hCDG_LAK

  refine Exists.intro K ?_
  refine And.intro hKsigma ?_
  refine And.intro hB0AK ?_
  refine And.intro hCDG ?_
  refine And.intro hLAK ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hCG_LK ?_
  exact hCDG_LAK


/--
Euclid XI.26 when the projection foot G lies on the ray from D opposite E,
that is, E-D-G.
-/
theorem euclid_proposition_11_26_of_projection_opposite_first_ray
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hEDG : Geo.Between E D G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  rcases
      hilbert_XI26_copy_base_triangle_on_ray
        (Geo := Geo)
        D E C A B hTri.1 hAB with
    ⟨sigma, B0, L, hCopy⟩

  rcases
      hilbert_XI26_copy_opposite_first_ray_point
        (Geo := Geo)
        sigma D E C A B B0 L G
        hCopy hTri.1 hEDG with
    ⟨K,
      hKsigma,
      hB0AK,
      hCDG,
      hLAK,
      hDG_AK,
      hEG_B0K,
      hCG_LK,
      _hCDG_LAK⟩

  have hEDGdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) E D G hEDG

  have hB0AKdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) B0 A K hB0AK

  have hDG : Ne D G :=
    hEDGdata.2.1

  have hEG : Ne E G :=
    hEDGdata.2.2.1

  have hCG : Ne C G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) C D G hCDG

  have hAK : Ne A K :=
    hB0AKdata.2.1

  have hB0K : Ne B0 K :=
    hB0AKdata.2.2.1

  have hLK : Ne L K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) L A K hLAK

  rcases
      hilbert_XI26_lift_base_point_copy_ne
        (Geo := Geo)
        D E C F A B
        pi sigma normal
        G B0 L K
        hTri
        hDpi hEpi hCpi
        hFnormal hPerp
        hCopy hKsigma
        hDG hEG hCG
        hAK hB0K hLK
        hDG_AK hEG_B0K hCG_LK with
    ⟨H, hRealizes⟩

  exact
    Exists.intro L
      (Exists.intro H hRealizes)


/--
Strong point-copy theorem for the boundary position C-D-G.

This is `hilbert_XI26_copy_opposite_first_ray_point` applied to the
swapped source and target base triangles.
-/
theorem hilbert_XI26_copy_opposite_second_ray_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (D E C A B B0 L G : Geo.Point)
    (hCopy : HilbertXI26BaseCopy Geo sigma D E C A B B0 L)
    (hEDC : Not (PrimCollinear Geo E D C))
    (hCDG : Geo.Between C D G) :
    exists K : Geo.Point,
      S.OnPlane K sigma /\
      Geo.Between L A K /\
      Not (PrimCollinear Geo E D G) /\
      Not (PrimCollinear Geo B0 A K) /\
      Geo.Congruent D G A K /\
      Geo.Congruent E G B0 K /\
      Geo.Congruent C G L K /\
      Geo.AngleCongruent E D G B0 A K := by

  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro h
    exact hEDC
      (PrimCollinearSymm Geo C D E h)

  have hSwap :
      HilbertXI26BaseCopy Geo sigma D C E A L L B0 :=
    hilbert_XI26_swap_base_copy
      (Geo := Geo)
      sigma D E C A B B0 L hCopy

  rcases
      hilbert_XI26_copy_opposite_first_ray_point
        (Geo := Geo)
        sigma
        D C E
        A L L B0 G
        hSwap hCDE hCDG with
    ⟨K,
      hKsigma,
      hLAK,
      hEDG,
      hB0AK,
      hDG_AK,
      hCG_LK,
      hEG_B0K,
      hEDG_B0AK⟩

  refine Exists.intro K ?_
  refine And.intro hKsigma ?_
  refine And.intro hLAK ?_
  refine And.intro hEDG ?_
  refine And.intro hB0AK ?_
  refine And.intro hDG_AK ?_
  refine And.intro hEG_B0K ?_
  refine And.intro hCG_LK ?_
  exact hEDG_B0AK


/--
Euclid XI.26 when the projection foot G lies on the ray from D opposite C,
that is, C-D-G.
-/
theorem euclid_proposition_11_26_of_projection_opposite_second_ray
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (pi : S.Plane)
    (normal : Geo.Line)
    (G : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B)
    (hDpi : S.OnPlane D pi)
    (hEpi : S.OnPlane E pi)
    (hCpi : S.OnPlane C pi)
    (hFnormal : Hinc.OnLine F normal)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo normal pi G)
    (hCDG : Geo.Between C D G) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  rcases
      hilbert_XI26_copy_base_triangle_on_ray
        (Geo := Geo)
        D E C A B hTri.1 hAB with
    ⟨sigma, B0, L, hCopy⟩

  rcases
      hilbert_XI26_copy_opposite_second_ray_point
        (Geo := Geo)
        sigma D E C A B B0 L G
        hCopy hTri.1 hCDG with
    ⟨K,
      hKsigma,
      hLAK,
      hEDG,
      hB0AK,
      hDG_AK,
      hEG_B0K,
      hCG_LK,
      _hEDG_B0AK⟩

  have hCDGdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) C D G hCDG

  have hLAKdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo) L A K hLAK

  have hDG : Ne D G :=
    hCDGdata.2.1

  have hCG : Ne C G :=
    hCDGdata.2.2.1

  have hEG : Ne E G :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) E D G hEDG

  have hAK : Ne A K :=
    hLAKdata.2.1

  have hLK : Ne L K :=
    hLAKdata.2.2.1

  have hB0K : Ne B0 K :=
    hilbert_noncollinear_endpoints_ne_XI
      (Geo := Geo) B0 A K hB0AK

  rcases
      hilbert_XI26_lift_base_point_copy_ne
        (Geo := Geo)
        D E C F A B
        pi sigma normal
        G B0 L K
        hTri
        hDpi hEpi hCpi
        hFnormal hPerp
        hCopy hKsigma
        hDG hEG hCG
        hAK hB0K hLK
        hDG_AK hEG_B0K hCG_LK with
    ⟨H, hRealizes⟩

  exact
    Exists.intro L
      (Exists.intro H hRealizes)


/-!
# Euclid XI.26: complete theorem

All local projection positions have now been solved:

* G = D;
* DG on ray DE;
* E-D-G;
* DG on ray DC;
* C-D-G;
* the two adjacent exterior sectors;
* the interior sector;
* the cyclic/opposite sector.

This file supplies the remaining order dispatcher and assembles the
unrestricted Euclid XI.26 theorem.

No new geometric construction is introduced here.
-/

/--
Euclid XI.26.

Given a trihedral angle at D and a prescribed ray AB, construct at A a
trihedral angle whose three face angles are respectively congruent to
the three face angles of the given trihedral angle.

The proof projects F orthogonally to the base plane EDC and dispatches
the projection foot G through the complete synthetic position
classification developed in the preceding test files.
-/
theorem euclid_proposition_11_26
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B) :
    exists L H : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H E D C C D F F D E := by

  rcases
      hilbert_XI26_source_projection
        (Geo := Geo)
        D E C F hTri with
    ⟨pi, normal, G,
      hDpi, hEpi, hCpi,
      _hFpi,
      hFnormal,
      hGpi,
      _hFG,
      hPerp⟩

  have hED : Ne E D :=
    hilbert_noncollinear_ne_first
      Geo E D C hTri.1

  have hDE : Ne D E := hED.symm

  have hCDE : Not (PrimCollinear Geo C D E) := by
    intro h
    exact hTri.1
      (PrimCollinearSymm Geo C D E h)

  have hCD : Ne C D :=
    hilbert_noncollinear_ne_first
      Geo C D E hCDE

  have hDC : Ne D C := hCD.symm

  by_cases hEDGcol : PrimCollinear Geo E D G

  · have hDEGcol : PrimCollinear Geo D E G :=
      PrimCollinearSwap Geo E D G hEDGcol

    rcases
        hilbert_space_collinear_ray_position_in_plane
          (Geo := Geo)
          pi D E G
          hDpi hEpi hGpi
          hDE hDEGcol with
      hGD | hRayDEG | hEDG

    · exact
        euclid_proposition_11_26_of_projection_foot_eq_vertex
          (Geo := Geo)
          D E C F A B
          pi normal G
          hTri hAB
          hDpi hEpi hCpi
          hFnormal hPerp
          hGD

    · exact
        euclid_proposition_11_26_of_projection_on_first_ray
          (Geo := Geo)
          D E C F A B
          pi normal G
          hTri hAB
          hDpi hEpi hCpi
          hFnormal hPerp
          hRayDEG

    · exact
        euclid_proposition_11_26_of_projection_opposite_first_ray
          (Geo := Geo)
          D E C F A B
          pi normal G
          hTri hAB
          hDpi hEpi hCpi
          hFnormal hPerp
          hEDG

  · have hEDG : Not (PrimCollinear Geo E D G) :=
      hEDGcol

    by_cases hCDGcol : PrimCollinear Geo C D G

    · have hDCGcol : PrimCollinear Geo D C G :=
        PrimCollinearSwap Geo C D G hCDGcol

      rcases
          hilbert_space_collinear_ray_position_in_plane
            (Geo := Geo)
            pi D C G
            hDpi hCpi hGpi
            hDC hDCGcol with
        hGD | hRayDCG | hCDG

      · exact
          euclid_proposition_11_26_of_projection_foot_eq_vertex
            (Geo := Geo)
            D E C F A B
            pi normal G
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hGD

      · exact
          euclid_proposition_11_26_of_projection_on_second_ray
            (Geo := Geo)
            D E C F A B
            pi normal G
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hRayDCG

      · exact
          euclid_proposition_11_26_of_projection_opposite_second_ray
            (Geo := Geo)
            D E C F A B
            pi normal G
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hCDG

    · have hCDG : Not (PrimCollinear Geo C D G) :=
        hCDGcol

      rcases
          hilbert_space_three_rays_order_or_cyclic_in_plane
            (Geo := Geo)
            pi D E C G
            hDpi hEpi hCpi hGpi
            hTri.1 hEDG hCDG with
        hFirst |
        hSecond |
        hInterior |
        hCyclic

      · exact
          euclid_proposition_11_26_of_first_exterior_projection
            (Geo := Geo)
            D E C F A B
            pi normal G
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hEDG hFirst

      · exact
          euclid_proposition_11_26_of_second_exterior_projection
            (Geo := Geo)
            D E C F A B
            pi normal G
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hCDG hSecond

      · exact
          euclid_proposition_11_26_of_interior_projection
            (Geo := Geo)
            D E C F A B
            pi normal G
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hInterior

      · rcases hCyclic with
          ⟨J, hCDJ, hEJG⟩
        exact
          euclid_proposition_11_26_of_cyclic_projection
            (Geo := Geo)
            D E C F A B
            pi normal G J
            hTri hAB
            hDpi hEpi hCpi
            hFnormal hPerp
            hCDG hCDJ hEJG

end Geometry

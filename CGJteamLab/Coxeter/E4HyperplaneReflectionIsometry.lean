import CGJteamLab.Coxeter.E4NormalSectionReflectionRestriction
import CGJteamLab.Coxeter.ReflectionIsometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection isometry: segment layer

This module ports the old experimental E4 reflection-isometry argument
to the corrected dimension-safe architecture.

No ambient `HilbertSpaceIncidence Geo`, `HilbertSpaceOrder Geo`, or
`HilbertSpaceCongruence Geo` instance is installed.

The proof uses:

* `HilbertDimensionFreeIncidence` / Smith-Wyler for plane carriers;
* corrected E4 normal uniqueness and XI.6 parallelism;
* exact plane-hyperplane intersection from the corrected E4 layer;
* the already validated restriction theorem
  `hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith`;
* ordinary planar `lineReflect_preserves_congruence`.

The final theorem is

  `hyperplaneReflect4_corrected_preserves_congruence`.
-/

/-! ## Neutral ambient segment helpers -/

/--
Segment congruence is reflexive under the corrected ambient E4 Group III
interface.
-/
theorem hilbert4D_ambient_congruent_reflexive_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (A B : Geo.Point) :
    Geo.Congruent A B A B := by

  by_cases hAB : A = B

  case pos =>
    subst B
    exact bookZero_nullSegment2 Geo A A

  case neg =>
    have hRExists :=
      smithCore_exists_point_ne
        (Geo := Geo)
        A

    let R : Geo.Point :=
      Classical.choose hRExists

    have hRA :
        Ne R A :=
      Classical.choose_spec hRExists

    have hAR :
        Ne A R :=
      hRA.symm

    have hXExists :=
      H4C.segment_construction
        A B A R hAR

    let X : Geo.Point :=
      Classical.choose hXExists

    have hXData :=
      Classical.choose_spec hXExists

    have hAXAB :
        Geo.Congruent A X A B :=
      hXData.2

    exact
      H4C.segment_congruence_common
        A X
        A B
        A B
        hAXAB hAXAB


/--
Symmetry of segment congruence derived from corrected ambient Group III.
-/
theorem hilbert4D_ambient_congruent_symm_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by

  have hRefl :
      Geo.Congruent A B A B :=
    hilbert4D_ambient_congruent_reflexive_corrected
      (Geo := Geo)
      A B

  exact
    H4C.segment_congruence_common
      A B
      C D
      A B
      h hRefl


/-! ## Basic corrected reflection data -/

/--
A point of the reflecting hyperplane is fixed.
-/
theorem hyperplaneReflect4_corrected_of_on_hyperplane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (hPSigma : Q.OnHyperplane P Sigma) :
    hyperplaneReflect4_corrected Geo Sigma P = P := by

  exact
    (hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      Sigma P).mpr hPSigma


/--
Canonical reflection data for an off-hyperplane point.
-/
theorem hyperplaneReflect4_corrected_off_hyperplane_data
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point)
    (hPoff : Not (Q.OnHyperplane P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P /\
      HilbertIsMidpoint Geo F P
        (hyperplaneReflect4_corrected Geo Sigma P) := by

  have hSpec :=
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma P

  rcases hSpec with hFixed | hOff

  case inl =>
    exact False.elim (hPoff hFixed.1)

  case inr =>
    exact hOff.2


/--
The reflected image remains on the normal line used in the reflection
configuration.
-/
theorem hyperplaneReflect4_corrected_on_normal_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P F : Geo.Point)
    (l : Geo.Line)
    (hPl : H.OnLine P l)
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMid :
      HilbertIsMidpoint Geo F P
        (hyperplaneReflect4_corrected Geo Sigma P)) :
    H.OnLine
      (hyperplaneReflect4_corrected Geo Sigma P)
      l := by

  have hFl :
      H.OnLine F l :=
    hNormal.1

  have hData :=
    H4O.between_incidence
      P F
      (hyperplaneReflect4_corrected Geo Sigma P)
      hMid.1

  have hPF :
      Ne P F :=
    hData.1

  have hCol :
      PrimCollinear
        Geo P F
        (hyperplaneReflect4_corrected Geo Sigma P) :=
    hData.2.2.2.1

  exact
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hPF
      hPl hFl
      hCol


/--
A corrected hyperplane normal meets its hyperplane only at its foot.
-/
theorem hilbert4D_normal_intersection_unique_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    {Sigma : Q.Hyperplane}
    {l : Geo.Line}
    {F X : Geo.Point}
    (hNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hXl : H.OnLine X l)
    (hXSigma : Q.OnHyperplane X Sigma) :
    X = F := by

  by_contra hXF

  have hFX :
      Ne F X := by
    intro hFX
    exact hXF hFX.symm

  have hlSigma :
      HilbertLineInHyperplane4 Geo l Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      F X hFX
      l hNormal.1 hXl
      Sigma hNormal.2.1 hXSigma

  exact
    hNormal.not_line_in_hyperplane
      (Geo := Geo)
      hlSigma


/--
Every corrected E4 hyperplane contains a point distinct from a prescribed
point of that hyperplane.
-/
theorem hilbert4D_hyperplane_other_point_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (F : Geo.Point)
    (hFSigma : Q.OnHyperplane F Sigma) :
    exists T : Geo.Point,
      Ne T F /\
      Q.OnHyperplane T Sigma := by

  let Fp : HyperplanePoint4 Geo Sigma :=
    Subtype.mk F hFSigma

  have hABCExists :=
    HilbertPlaneIncidence.three_noncollinear
      (Geo := HyperplaneGeo4 Geo Sigma)

  let A : HyperplanePoint4 Geo Sigma :=
    Classical.choose hABCExists

  have hBCExists :=
    Classical.choose_spec hABCExists

  let B : HyperplanePoint4 Geo Sigma :=
    Classical.choose hBCExists

  have hCExists :=
    Classical.choose_spec hBCExists

  let C : HyperplanePoint4 Geo Sigma :=
    Classical.choose hCExists

  have hABC :
      Not
        (PrimCollinear
          (HyperplaneGeo4 Geo Sigma)
          A B C) :=
    Classical.choose_spec hCExists

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      (HyperplaneGeo4 Geo Sigma)
      A B C hABC

  by_cases hAF :
      A = Fp

  case pos =>
    refine Exists.intro B.1 ?_
    constructor

    case left =>
      intro hBF
      apply hAB
      apply Subtype.ext
      have hAval : A.1 = F :=
        congrArg Subtype.val hAF
      exact hAval.trans hBF.symm

    case right =>
      exact B.2

  case neg =>
    refine Exists.intro A.1 ?_
    constructor

    case left =>
      intro hAFval
      apply hAF
      apply Subtype.ext
      exact hAFval

    case right =>
      exact A.2


/-! ## Mirror-point equidistance -/

/--
Every point of the mirror hyperplane is equidistant from a point and its
corrected E4 reflected image.
-/
theorem hyperplaneReflect4_corrected_hyperplane_point_equidistant
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [H4C : Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R : Geo.Point)
    (hRSigma : Q.OnHyperplane R Sigma) :
    Geo.Congruent
      R P
      R (hyperplaneReflect4_corrected Geo Sigma P) := by

  by_cases hPSigma :
      Q.OnHyperplane P Sigma

  case pos =>
    have hFix :
        hyperplaneReflect4_corrected Geo Sigma P = P :=
      hyperplaneReflect4_corrected_of_on_hyperplane
        (Geo := Geo)
        Sigma P hPSigma

    rw [hFix]

    exact
      hilbert4D_ambient_congruent_reflexive_corrected
        (Geo := Geo)
        R P

  case neg =>
    have hFootExists :=
      hyperplaneReflect4_corrected_off_hyperplane_data
        (Geo := Geo)
        Sigma P hPSigma

    let F : Geo.Point :=
      Classical.choose hFootExists

    have hFootData :=
      Classical.choose_spec hFootExists

    have hPerp :
        PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P :=
      hFootData.1

    have hMid :
        HilbertIsMidpoint Geo F P
          (hyperplaneReflect4_corrected Geo Sigma P) :=
      hFootData.2

    let l : Geo.Line :=
      Classical.choose hPerp

    have hLData :=
      Classical.choose_spec hPerp

    have hPl :
        H.OnLine P l :=
      hLData.1

    have hNormal :
        HilbertLinePerpendicularHyperplaneAt4_corrected
          Geo l Sigma F :=
      hLData.2

    have hFl :
        H.OnLine F l :=
      hNormal.1

    by_cases hRF :
        R = F

    case pos =>
      subst R

      exact
        (Geometry.Geo.congruent_reverse_first
          Geo
          P F
          F (hyperplaneReflect4_corrected Geo Sigma P)).mp
          hMid.2

    case neg =>
      have hFR :
          Ne F R := by
        intro hFR
        exact hRF hFR.symm

      have hRl :
          Not (H.OnLine R l) := by
        intro hRl
        have hEq :=
          hilbert4D_normal_intersection_unique_corrected
            (Geo := Geo)
            hNormal hRl hRSigma
        exact hRF hEq

      let : SmithIncidenceCore Geo :=
        smithIncidenceCore_of_dimensionFree
          (Geo := Geo)

      have hPiExists :=
        smithCore_plane_through_line_and_external_point
          (Geo := Geo)
          l R hRl

      let pi : Q.toHilbertSpacePrimitive.Plane :=
        Classical.choose hPiExists

      have hPiData :=
        Classical.choose_spec hPiExists

      have hlpi :
          HilbertLineInPlane Geo l pi :=
        hPiData.1

      have hRpi :
          Q.toHilbertSpacePrimitive.OnPlane R pi :=
        hPiData.2

      have hFpi :
          Q.toHilbertSpacePrimitive.OnPlane F pi :=
        hlpi F hFl

      have hPpi :
          Q.toHilbertSpacePrimitive.OnPlane P pi :=
        hlpi P hPl

      have hP'l :
          H.OnLine
            (hyperplaneReflect4_corrected Geo Sigma P)
            l :=
        hyperplaneReflect4_corrected_on_normal_line
          (Geo := Geo)
          Sigma P F l hPl hNormal hMid

      have hP'pi :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma P)
            pi :=
        hlpi
          (hyperplaneReflect4_corrected Geo Sigma P)
          hP'l

      have hPF :
          Ne P F :=
        (H4O.between_incidence
          P F
          (hyperplaneReflect4_corrected Geo Sigma P)
          hMid.1).1

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

      let : HilbertCongruence (PlaneGeo Geo pi) :=
        planeGeoHilbertCongruence4_corrected
          (Geo := Geo)
          pi
          P F R
          hPpi hFpi hRpi
          hPFR

      have hTraceExists :=
        hilbert4D_normal_plane_intersection_line
          (Geo := Geo)
          hNormal pi hlpi

      let s : Geo.Line :=
        Classical.choose hTraceExists

      have hTraceData :=
        Classical.choose_spec hTraceExists

      have hFs :
          H.OnLine F s :=
        hTraceData.1

      have hspi :
          HilbertLineInPlane Geo s pi :=
        hTraceData.2.1

      have hsSigma :
          HilbertLineInHyperplane4 Geo s Sigma :=
        hTraceData.2.2.1

      have hTrace :=
        hTraceData.2.2.2

      have hRs :
          H.OnLine R s :=
        (hTrace R).mp
          (And.intro hRpi hRSigma)

      let Fp : PlanePoint Geo pi :=
        Subtype.mk F hFpi

      let Rp : PlanePoint Geo pi :=
        Subtype.mk R hRpi

      let Pp : PlanePoint Geo pi :=
        Subtype.mk P hPpi

      let Pp' : PlanePoint Geo pi :=
        Subtype.mk
          (hyperplaneReflect4_corrected Geo Sigma P)
          hP'pi

      let sp : PlaneLine Geo pi :=
        Subtype.mk s hspi

      have hFRp :
          Ne Fp Rp := by
        intro hEq
        apply hFR
        exact congrArg Subtype.val hEq

      let axis :
          ReflectionAxis (PlaneGeo Geo pi) :=
        {
          carrier := sp
          A := Fp
          B := Rp
          hAB := hFRp
          hA := hFs
          hB := hRs
        }

      have hRestricted :
          IsLineReflection
            (PlaneGeo Geo pi)
            axis Pp Pp' :=
        hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
          (Geo := Geo)
          (N := pi)
          Sigma F
          l s
          hlpi
          hNormal
          hspi
          hTrace
          axis
          rfl
          Pp Pp'
          (hyperplaneReflect4_corrected_spec
            (Geo := Geo)
            Sigma P)

      have hRaxis :
          HilbertIncidence.OnLine
            (Geo := PlaneGeo Geo pi)
            Rp axis.carrier :=
        hRs

      have hCongPlane :
          (PlaneGeo Geo pi).Congruent
            Rp Pp Rp Pp' :=
        line_reflection_axis_point_equidistant
          (PlaneGeo Geo pi)
          axis
          Pp Pp'
          Rp
          hRaxis
          hRestricted

      exact
        (planeGeo_congruent
          (Geo := Geo)
          pi Rp Pp Rp Pp').mp
          hCongPlane


/-! ## Endpoint-on-mirror cases -/

/--
If the first endpoint belongs to the mirror hyperplane, corrected
hyperplane reflection preserves the segment.
-/
theorem hyperplaneReflect4_corrected_preserves_congruence_left_on_hyperplane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R : Geo.Point)
    (hPSigma : Q.OnHyperplane P Sigma) :
    Geo.Congruent
      P R
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma R) := by

  have hFixP :
      hyperplaneReflect4_corrected Geo Sigma P = P :=
    hyperplaneReflect4_corrected_of_on_hyperplane
      (Geo := Geo)
      Sigma P hPSigma

  rw [hFixP]

  exact
    hyperplaneReflect4_corrected_hyperplane_point_equidistant
      (Geo := Geo)
      Sigma R P hPSigma


/--
If the second endpoint belongs to the mirror hyperplane, corrected
hyperplane reflection preserves the segment.
-/
theorem hyperplaneReflect4_corrected_preserves_congruence_right_on_hyperplane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R : Geo.Point)
    (hRSigma : Q.OnHyperplane R Sigma) :
    Geo.Congruent
      P R
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma R) := by

  have hFixR :
      hyperplaneReflect4_corrected Geo Sigma R = R :=
    hyperplaneReflect4_corrected_of_on_hyperplane
      (Geo := Geo)
      Sigma R hRSigma

  rw [hFixR]

  have hRP :
      Geo.Congruent
        R P
        R (hyperplaneReflect4_corrected Geo Sigma P) :=
    hyperplaneReflect4_corrected_hyperplane_point_equidistant
      (Geo := Geo)
      Sigma P R hRSigma

  have hPR_RP' :
      Geo.Congruent
        P R
        R (hyperplaneReflect4_corrected Geo Sigma P) :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      R P
      R (hyperplaneReflect4_corrected Geo Sigma P)).mp
      hRP

  exact
    (Geometry.Geo.congruent_reverse_second
      Geo
      P R
      R (hyperplaneReflect4_corrected Geo Sigma P)).mp
      hPR_RP'


/-! ## Two off-hyperplane points -/

/--
Two off-hyperplane points with the same perpendicular foot are reflected
inside one common planar slice, hence their segment is preserved.
-/
theorem hyperplaneReflect4_corrected_preserves_congruence_same_foot
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R F : Geo.Point)
    (_hPoff : Not (Q.OnHyperplane P Sigma))
    (_hRoff : Not (Q.OnHyperplane R Sigma))
    (hPerpP :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P)
    (hMidP :
      HilbertIsMidpoint Geo F P
        (hyperplaneReflect4_corrected Geo Sigma P))
    (hPerpR :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F R)
    (hMidR :
      HilbertIsMidpoint Geo F R
        (hyperplaneReflect4_corrected Geo Sigma R)) :
    Geo.Congruent
      P R
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma R) := by

  let l : Geo.Line :=
    Classical.choose hPerpP

  have hLData :=
    Classical.choose_spec hPerpP

  have hPl :
      H.OnLine P l :=
    hLData.1

  have hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F :=
    hLData.2

  let m : Geo.Line :=
    Classical.choose hPerpR

  have hMData :=
    Classical.choose_spec hPerpR

  have hRm :
      H.OnLine R m :=
    hMData.1

  have hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma F :=
    hMData.2

  have hlm :
      l = m :=
    hilbert4D_normal_same_foot_unique_corrected
      (Geo := Geo)
      Sigma l m F
      hLNormal hMNormal

  have hRl :
      H.OnLine R l := by
    rw [hlm]
    exact hRm

  have hFl :
      H.OnLine F l :=
    hLNormal.1

  have hFSigma :
      Q.OnHyperplane F Sigma :=
    hLNormal.2.1

  have hTExists :=
    hilbert4D_hyperplane_other_point_corrected
      (Geo := Geo)
      Sigma F hFSigma

  let T : Geo.Point :=
    Classical.choose hTExists

  have hTData :=
    Classical.choose_spec hTExists

  have hTF :
      Ne T F :=
    hTData.1

  have hTSigma :
      Q.OnHyperplane T Sigma :=
    hTData.2

  have hTl :
      Not (H.OnLine T l) := by
    intro hTl
    have hEq :=
      hilbert4D_normal_intersection_unique_corrected
        (Geo := Geo)
        hLNormal hTl hTSigma
    exact hTF hEq

  let : SmithIncidenceCore Geo :=
    smithIncidenceCore_of_dimensionFree
      (Geo := Geo)

  have hPiExists :=
    smithCore_plane_through_line_and_external_point
      (Geo := Geo)
      l T hTl

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hPiExists

  have hPiData :=
    Classical.choose_spec hPiExists

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    hPiData.1

  have hTpi :
      Q.toHilbertSpacePrimitive.OnPlane T pi :=
    hPiData.2

  have hFpi :
      Q.toHilbertSpacePrimitive.OnPlane F pi :=
    hlpi F hFl

  have hPpi :
      Q.toHilbertSpacePrimitive.OnPlane P pi :=
    hlpi P hPl

  have hRpi :
      Q.toHilbertSpacePrimitive.OnPlane R pi :=
    hlpi R hRl

  have hP'l :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma P)
        l :=
    hyperplaneReflect4_corrected_on_normal_line
      (Geo := Geo)
      Sigma P F l hPl hLNormal hMidP

  have hR'l :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma R)
        l :=
    hyperplaneReflect4_corrected_on_normal_line
      (Geo := Geo)
      Sigma R F l hRl hLNormal hMidR

  have hP'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma P)
        pi :=
    hlpi _ hP'l

  have hR'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma R)
        pi :=
    hlpi _ hR'l

  have hPF :
      Ne P F :=
    (H4O.between_incidence
      P F
      (hyperplaneReflect4_corrected Geo Sigma P)
      hMidP.1).1

  have hPFT :
      Not (PrimCollinear Geo P F T) := by
    intro hCol
    have hTl' :
        H.OnLine T l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hCol
    exact hTl hTl'

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi
      P F T
      hPpi hFpi hTpi
      hPFT

  have hTraceExists :=
    hilbert4D_normal_plane_intersection_line
      (Geo := Geo)
      hLNormal pi hlpi

  let s : Geo.Line :=
    Classical.choose hTraceExists

  have hTraceData :=
    Classical.choose_spec hTraceExists

  have hFs :
      H.OnLine F s :=
    hTraceData.1

  have hspi :
      HilbertLineInPlane Geo s pi :=
    hTraceData.2.1

  have hTrace :=
    hTraceData.2.2.2

  have hTs :
      H.OnLine T s :=
    (hTrace T).mp
      (And.intro hTpi hTSigma)

  let Fp : PlanePoint Geo pi :=
    Subtype.mk F hFpi

  let Tp : PlanePoint Geo pi :=
    Subtype.mk T hTpi

  let Pp : PlanePoint Geo pi :=
    Subtype.mk P hPpi

  let Rp : PlanePoint Geo pi :=
    Subtype.mk R hRpi

  let Pp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma P)
      hP'pi

  let Rp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma R)
      hR'pi

  let sp : PlaneLine Geo pi :=
    Subtype.mk s hspi

  have hFTp :
      Ne Fp Tp := by
    intro hEq
    apply hTF
    exact (congrArg Subtype.val hEq).symm

  let axis :
      ReflectionAxis (PlaneGeo Geo pi) :=
    {
      carrier := sp
      A := Fp
      B := Tp
      hAB := hFTp
      hA := hFs
      hB := hTs
    }

  have hRefP :
      IsLineReflection
        (PlaneGeo Geo pi)
        axis Pp Pp' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := pi)
      Sigma F
      l s
      hlpi
      hLNormal
      hspi
      hTrace
      axis rfl
      Pp Pp'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P)

  have hRefR :
      IsLineReflection
        (PlaneGeo Geo pi)
        axis Rp Rp' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := pi)
      Sigma F
      l s
      hlpi
      hLNormal
      hspi
      hTrace
      axis rfl
      Rp Rp'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma R)

  have hEqP :
      lineReflect
          (PlaneGeo Geo pi)
          axis Pp =
        Pp' :=
    line_reflection_unique
      (PlaneGeo Geo pi)
      axis Pp
      (lineReflect (PlaneGeo Geo pi) axis Pp)
      Pp'
      (lineReflect_spec
        (PlaneGeo Geo pi)
        axis Pp)
      hRefP

  have hEqR :
      lineReflect
          (PlaneGeo Geo pi)
          axis Rp =
        Rp' :=
    line_reflection_unique
      (PlaneGeo Geo pi)
      axis Rp
      (lineReflect (PlaneGeo Geo pi) axis Rp)
      Rp'
      (lineReflect_spec
        (PlaneGeo Geo pi)
        axis Rp)
      hRefR

  have hCongPlane :
      (PlaneGeo Geo pi).Congruent
        Pp Rp
        (lineReflect (PlaneGeo Geo pi) axis Pp)
        (lineReflect (PlaneGeo Geo pi) axis Rp) :=
    lineReflect_preserves_congruence
      (PlaneGeo Geo pi)
      axis Pp Rp

  have hCongPlane' :
      (PlaneGeo Geo pi).Congruent
        Pp Rp Pp' Rp' := by
    simpa only [hEqP, hEqR]
      using hCongPlane

  exact
    (planeGeo_congruent
      (Geo := Geo)
      pi Pp Rp Pp' Rp').mp
      hCongPlane'


/--
Two off-hyperplane points with distinct perpendicular feet are reflected
inside the common plane of their parallel normals.
-/
theorem hyperplaneReflect4_corrected_preserves_congruence_distinct_feet
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R F G : Geo.Point)
    (_hPoff : Not (Q.OnHyperplane P Sigma))
    (_hRoff : Not (Q.OnHyperplane R Sigma))
    (hFG : Ne F G)
    (hPerpP :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P)
    (hMidP :
      HilbertIsMidpoint Geo F P
        (hyperplaneReflect4_corrected Geo Sigma P))
    (hPerpR :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma G R)
    (hMidR :
      HilbertIsMidpoint Geo G R
        (hyperplaneReflect4_corrected Geo Sigma R)) :
    Geo.Congruent
      P R
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma R) := by

  let l : Geo.Line :=
    Classical.choose hPerpP

  have hLData :=
    Classical.choose_spec hPerpP

  have hPl :
      H.OnLine P l :=
    hLData.1

  have hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F :=
    hLData.2

  let m : Geo.Line :=
    Classical.choose hPerpR

  have hMData :=
    Classical.choose_spec hPerpR

  have hRm :
      H.OnLine R m :=
    hMData.1

  have hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G :=
    hMData.2

  have hParallel :
      Hilbert4DLinesParallel_corrected Geo l m :=
    hilbert4D_normals_to_same_hyperplane_parallel_corrected
      (Geo := Geo)
      Sigma
      l m
      F G
      hFG
      hLNormal
      hMNormal

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hParallel

  have hPiData :=
    Classical.choose_spec hParallel

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    hPiData.1

  have hmpi :
      HilbertLineInPlane Geo m pi :=
    hPiData.2.1

  have hFl :
      H.OnLine F l :=
    hLNormal.1

  have hGm :
      H.OnLine G m :=
    hMNormal.1

  have hFpi :
      Q.toHilbertSpacePrimitive.OnPlane F pi :=
    hlpi F hFl

  have hGpi :
      Q.toHilbertSpacePrimitive.OnPlane G pi :=
    hmpi G hGm

  have hPpi :
      Q.toHilbertSpacePrimitive.OnPlane P pi :=
    hlpi P hPl

  have hRpi :
      Q.toHilbertSpacePrimitive.OnPlane R pi :=
    hmpi R hRm

  have hP'l :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma P)
        l :=
    hyperplaneReflect4_corrected_on_normal_line
      (Geo := Geo)
      Sigma P F l hPl hLNormal hMidP

  have hR'm :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma R)
        m :=
    hyperplaneReflect4_corrected_on_normal_line
      (Geo := Geo)
      Sigma R G m hRm hMNormal hMidR

  have hP'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma P)
        pi :=
    hlpi _ hP'l

  have hR'pi :
      Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma R)
        pi :=
    hmpi _ hR'm

  have hPF :
      Ne P F :=
    (H4O.between_incidence
      P F
      (hyperplaneReflect4_corrected Geo Sigma P)
      hMidP.1).1

  have hPFG :
      Not (PrimCollinear Geo P F G) := by
    intro hCol

    have hGl :
        H.OnLine G l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hPF
        hPl hFl
        hCol

    have hlSigma :
        HilbertLineInHyperplane4 Geo l Sigma :=
      Hilbert4DAmbientIncidence.line_in_hyperplane
        (Geo := Geo)
        F G hFG
        l hFl hGl
        Sigma hLNormal.2.1 hMNormal.2.1

    exact
      hLNormal.not_line_in_hyperplane
        (Geo := Geo)
        hlSigma

  let : HilbertCongruence (PlaneGeo Geo pi) :=
    planeGeoHilbertCongruence4_corrected
      (Geo := Geo)
      pi
      P F G
      hPpi hFpi hGpi
      hPFG

  have hTraceExists :=
    hilbert4D_normal_plane_intersection_line
      (Geo := Geo)
      hLNormal pi hlpi

  let s : Geo.Line :=
    Classical.choose hTraceExists

  have hTraceData :=
    Classical.choose_spec hTraceExists

  have hFs :
      H.OnLine F s :=
    hTraceData.1

  have hspi :
      HilbertLineInPlane Geo s pi :=
    hTraceData.2.1

  have hTrace :=
    hTraceData.2.2.2

  have hGs :
      H.OnLine G s :=
    (hTrace G).mp
      (And.intro hGpi hMNormal.2.1)

  let Fp : PlanePoint Geo pi :=
    Subtype.mk F hFpi

  let Gp : PlanePoint Geo pi :=
    Subtype.mk G hGpi

  let Pp : PlanePoint Geo pi :=
    Subtype.mk P hPpi

  let Rp : PlanePoint Geo pi :=
    Subtype.mk R hRpi

  let Pp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma P)
      hP'pi

  let Rp' : PlanePoint Geo pi :=
    Subtype.mk
      (hyperplaneReflect4_corrected Geo Sigma R)
      hR'pi

  let sp : PlaneLine Geo pi :=
    Subtype.mk s hspi

  have hFGp :
      Ne Fp Gp := by
    intro hEq
    apply hFG
    exact congrArg Subtype.val hEq

  let axis :
      ReflectionAxis (PlaneGeo Geo pi) :=
    {
      carrier := sp
      A := Fp
      B := Gp
      hAB := hFGp
      hA := hFs
      hB := hGs
    }

  have hRefP :
      IsLineReflection
        (PlaneGeo Geo pi)
        axis Pp Pp' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := pi)
      Sigma F
      l s
      hlpi
      hLNormal
      hspi
      hTrace
      axis rfl
      Pp Pp'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P)

  have hRefR :
      IsLineReflection
        (PlaneGeo Geo pi)
        axis Rp Rp' :=
    hilbert4D_hyperplaneReflection_restricts_to_lineReflection_smith
      (Geo := Geo)
      (N := pi)
      Sigma G
      m s
      hmpi
      hMNormal
      hspi
      hTrace
      axis rfl
      Rp Rp'
      (hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma R)

  have hEqP :
      lineReflect
          (PlaneGeo Geo pi)
          axis Pp =
        Pp' :=
    line_reflection_unique
      (PlaneGeo Geo pi)
      axis Pp
      (lineReflect (PlaneGeo Geo pi) axis Pp)
      Pp'
      (lineReflect_spec
        (PlaneGeo Geo pi)
        axis Pp)
      hRefP

  have hEqR :
      lineReflect
          (PlaneGeo Geo pi)
          axis Rp =
        Rp' :=
    line_reflection_unique
      (PlaneGeo Geo pi)
      axis Rp
      (lineReflect (PlaneGeo Geo pi) axis Rp)
      Rp'
      (lineReflect_spec
        (PlaneGeo Geo pi)
        axis Rp)
      hRefR

  have hCongPlane :
      (PlaneGeo Geo pi).Congruent
        Pp Rp
        (lineReflect (PlaneGeo Geo pi) axis Pp)
        (lineReflect (PlaneGeo Geo pi) axis Rp) :=
    lineReflect_preserves_congruence
      (PlaneGeo Geo pi)
      axis Pp Rp

  have hCongPlane' :
      (PlaneGeo Geo pi).Congruent
        Pp Rp Pp' Rp' := by
    simpa only [hEqP, hEqR]
      using hCongPlane

  exact
    (planeGeo_congruent
      (Geo := Geo)
      pi Pp Rp Pp' Rp').mp
      hCongPlane'


/--
Congruence preservation for two points outside the mirror.
-/
theorem hyperplaneReflect4_corrected_preserves_congruence_off_hyperplane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R : Geo.Point)
    (hPoff : Not (Q.OnHyperplane P Sigma))
    (hRoff : Not (Q.OnHyperplane R Sigma)) :
    Geo.Congruent
      P R
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma R) := by

  have hPData :=
    hyperplaneReflect4_corrected_off_hyperplane_data
      (Geo := Geo)
      Sigma P hPoff

  let F : Geo.Point :=
    Classical.choose hPData

  have hPFData :=
    Classical.choose_spec hPData

  have hRData :=
    hyperplaneReflect4_corrected_off_hyperplane_data
      (Geo := Geo)
      Sigma R hRoff

  let G : Geo.Point :=
    Classical.choose hRData

  have hRGData :=
    Classical.choose_spec hRData

  by_cases hFG :
      F = G

  case pos =>
    have hPerpR_F :
        PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F R := by
      rw [hFG]
      exact hRGData.1

    have hMidR_F :
        HilbertIsMidpoint Geo F R
          (hyperplaneReflect4_corrected Geo Sigma R) := by
      rw [hFG]
      exact hRGData.2

    exact
      hyperplaneReflect4_corrected_preserves_congruence_same_foot
        (Geo := Geo)
        Sigma
        P R F
        hPoff hRoff
        hPFData.1 hPFData.2
        hPerpR_F hMidR_F

  case neg =>
    exact
      hyperplaneReflect4_corrected_preserves_congruence_distinct_feet
        (Geo := Geo)
        Sigma
        P R F G
        hPoff hRoff hFG
        hPFData.1 hPFData.2
        hRGData.1 hRGData.2


/-! ## Global segment-isometry theorem -/

/--
Corrected E4 hyperplane reflection preserves segment congruence for every
pair of ambient points.
-/
theorem hyperplaneReflect4_corrected_preserves_congruence
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P R : Geo.Point) :
    Geo.Congruent
      P R
      (hyperplaneReflect4_corrected Geo Sigma P)
      (hyperplaneReflect4_corrected Geo Sigma R) := by

  by_cases hPSigma :
      Q.OnHyperplane P Sigma

  case pos =>
    exact
      hyperplaneReflect4_corrected_preserves_congruence_left_on_hyperplane
        (Geo := Geo)
        Sigma P R hPSigma

  case neg =>
    by_cases hRSigma :
        Q.OnHyperplane R Sigma

    case pos =>
      exact
        hyperplaneReflect4_corrected_preserves_congruence_right_on_hyperplane
          (Geo := Geo)
          Sigma P R hRSigma

    case neg =>
      exact
        hyperplaneReflect4_corrected_preserves_congruence_off_hyperplane
          (Geo := Geo)
          Sigma P R
          hPSigma hRSigma

end Geometry

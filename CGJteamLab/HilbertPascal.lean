import CGJteamLab.HilbertGrundlagen
import CGJteamLab.HilbertBookZero

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]


/-!
# HilbertPascal

Experimental development associated with Euclid I.39.

The present file is used to isolate a lower-level obstruction in the
Hilbert development before the permanent theory is extended further.

At this stage Hilbert Theorem 21 is assumed temporarily.  The purpose
is to determine which circle results actually become available from
the existing Grundlagen once congruence of right angles is supplied.

Nothing in this file is part of the permanent Hilbert theory.
-/


/--
For two rays from the same foot into the same half-plane,
their angles with the fixed base ray satisfy angle trichotomy.
-/
theorem proposition39_test_same_foot_angle_cases
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base) :
    Geo.AngleCongruent X F A X F D ∨
    HilbertAngleLess Geo X F A X F D ∨
    HilbertAngleLess Geo X F D X F A := by

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      base
      hFX.symm
      hXbase
      hFbase
      hSame.1

  have hXFD :
      ¬ PrimCollinear Geo X F D :=
    hilbert_not_collinear_of_off_line
      Geo
      X F D
      base
      hFX.symm
      hXbase
      hFbase
      hSame.2.1

  exact
    angle_trichotomy
      Geo
      X F A
      X F D
      hXFA
      hXFD

/--
If angle XFA is strictly smaller than angle XFD, with A and D
on the same side of the base XF, then ray FA meets the open
segment XD.
-/
theorem proposition39_test_angle_less_ray_inside
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    HilbertRayMeetsSegment Geo F A X D := by

  rcases hLess with
    ⟨hXFA, hXFD, J, hInsideJ, hAngle⟩

  rcases hInsideJ with
    ⟨H, hXHD, hRayFJH⟩

  have hDHX :
      Geo.Between D H X :=
    (HilbertOrder.between_incidence
      X H D hXHD).2.2.2.2

  have hDXF :
      ¬ PrimCollinear Geo D X F := by
    intro h
    exact
      hXFD
        (PrimCollinearCycle
          Geo D X F h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        D H F X
        hDHX
        hDXF
    with
    ⟨lineFX,
      hFlineFX,
      hXlineFX,
      hDHSame_lineFX⟩

  have hLineEq :
      lineFX = base :=
    HilbertPlaneIncidence.line_unique
      F X hFX
      lineFX base
      hFlineFX hXlineFX
      hFbase hXbase

  have hDHSame :
      HilbertSameSide Geo D H base := by
    rw [← hLineEq]
    exact hDHSame_lineFX

  have hAHSame :
      HilbertSameSide Geo A H base :=
    hilbert_sameSide_trans
      Geo
      A D H
      base
      hSame
      hDHSame

  have hXFJ :
      ¬ PrimCollinear Geo X F J :=
    (hilbert_interior_angle_less
      Geo
      F J X D
      hXFD
      ⟨H, hXHD, hRayFJH⟩).1

  have hFJ :
      F ≠ J :=
    hRayFJH.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        F J hFJ
    with
    ⟨lineFJ,
      hFlineFJ,
      hJlineFJ⟩

  have hXoffFJ :
      ¬ HilbertIncidence.OnLine X lineFJ := by
    intro hXline
    exact
      hXFJ
        ⟨lineFJ,
          hXline,
          hFlineFJ,
          hJlineFJ⟩

  have hRayFJJ :
      HilbertSameRay Geo F J J :=
    hilbert_sameRay_refl
      Geo F J hFJ.symm

  have hJHSame :
      HilbertSameSide Geo J H base :=
    hilbert_sameRay_points_sameSide
      Geo
      F J
      J H
      X
      lineFJ base
      hFlineFJ
      hJlineFJ
      hFbase
      hXbase
      hXoffFJ
      hRayFJJ
      hRayFJH

  have hHJSame :
      HilbertSameSide Geo H J base :=
    hilbert_sameSide_symm
      Geo J H base hJHSame

  have hAJSame :
      HilbertSameSide Geo A J base :=
    hilbert_sameSide_trans
      Geo
      A H J
      base
      hAHSame
      hHJSame

  rcases
      hilbert_angle_unique_common_ray
        Geo
        X F A J
        base
        hFX.symm
        hXbase
        hFbase
        hAJSame.1
        hAJSame
        hAngle
    with
    ⟨Z,
      hRayZA,
      hRayZJ⟩

  have hRayAJ :
      HilbertSameRay Geo F A J :=
    hilbert_sameRay_of_common
      Geo
      F Z A J
      hRayZA
      hRayZJ

  have hRayJA :
      HilbertSameRay Geo F J A :=
    hilbert_sameRay_symm
      Geo
      F A J
      hRayAJ

  have hRayFAH :
      HilbertSameRay Geo F A H :=
    hilbert_sameRay_of_common
      Geo
      F J A H
      hRayJA
      hRayFJH

  exact
    ⟨H,
      hXHD,
      hRayFAH⟩

/--
A right angle may be expressed using any chosen point on the
opposite base ray.
-/
theorem proposition39_test_right_angle_chosen_supplement
    [HilbertCongruence Geo]
    (D F X Y : Geo.Point)
    (hXFY : Geo.Between X F Y)
    (hXFD : ¬ PrimCollinear Geo X F D)
    (hRight : HilbertRightAngle Geo X F D) :
    Geo.AngleCongruent X F D D F Y := by

  rcases hRight with
    ⟨E, hXFE, hRightE⟩

  have hRefl :
      Geo.AngleCongruent X F D X F D :=
    Geo.angle_congruent_reflexive
      X F D

  have hSupp :
      Geo.AngleCongruent D F E D F Y :=
    hilbert_adjacent_angles_congruent
      Geo
      X F D E
      X F D Y
      hXFE
      hXFY
      hXFD
      hXFD
      hRefl

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X F D
      D F E
      D F Y
      hRightE
      hSupp

/--
If ray FA meets the open segment XD and X-F-Y, then ray FD
meets the open segment AY, provided A and D lie on the same
side of the base XY.
-/
theorem proposition39_test_inside_flip
    [HilbertOrder Geo]
    (A D F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hSame : HilbertSameSide Geo A D base)
    (hXFY : Geo.Between X F Y)
    (hInside :
      HilbertRayMeetsSegment Geo F A X D) :
    HilbertRayMeetsSegment Geo F D A Y := by

  rcases hInside with
    ⟨H, hXHD, hRayFAH⟩

  have hFA :
      F ≠ A := by
    intro h
    subst A
    exact hSame.1 hFbase

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFY :
      F ≠ Y :=
    hXFYData.2.1

  have hXY :
      X ≠ Y :=
    hXFYData.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        F A hFA
    with
    ⟨lineFA,
      hFlineFA,
      hAlineFA⟩

  have hHlineFA :
      HilbertIncidence.OnLine H lineFA :=
    hilbert_collinear_on_line
      Geo
      F A H
      lineFA
      hFA
      hFlineFA
      hAlineFA
      hRayFAH.2.2.1

  have hXYD :
      ¬ Collinear Geo X Y D :=
    hilbert_not_collinear_of_off_line
      Geo
      X Y D
      base
      hXY
      hXbase
      hYbase
      hSame.2.1

  have hYDsame :
      HilbertSameSide Geo Y D lineFA :=
    hilbert_third_side_endpoints_sameSide
      Geo
      X Y D
      F H
      lineFA
      hXYD
      hXFY
      hXHD
      hFlineFA
      hHlineFA

  have hDYsame :
      HilbertSameSide Geo D Y lineFA :=
    hilbert_sameSide_symm
      Geo Y D lineFA hYDsame

  have hFYD :
      ¬ Collinear Geo F Y D :=
    hilbert_not_collinear_of_off_line
      Geo
      F Y D
      base
      hFY
      hFbase
      hYbase
      hSame.2.1

  have hDFY :
      ¬ Collinear Geo D F Y := by
    intro h
    exact
      hFYD
        (PrimCollinearCycle
          Geo D F Y h)

  rcases
      hilbert_sameSide_rays_order
        Geo
        F D A Y
        lineFA
        hFA
        hFlineFA
        hAlineFA
        hDYsame.1
        hDYsame.2.1
        hDYsame
        hDFY
    with
    hFD | hFYmeet

  · rcases hFD with
      ⟨K, hYKA, hRayFDK⟩

    have hAKY :
        Geo.Between A K Y :=
      (HilbertOrder.between_incidence
        Y K A hYKA).2.2.2.2

    exact
      ⟨K,
        hAKY,
        hRayFDK⟩

  · rcases hFYmeet with
      ⟨K, hDKA, hRayFYK⟩

    have hKbase :
        HilbertIncidence.OnLine K base :=
      hilbert_collinear_on_line
        Geo
        F Y K
        base
        hFY
        hFbase
        hYbase
        hRayFYK.2.2.1

    have hOppDA :
        HilbertOppositeSide Geo D A base :=
      ⟨hSame.2.1,
        hSame.1,
        ⟨K,
          hDKA,
          hKbase⟩⟩

    have hSameDA :
        HilbertSameSide Geo D A base :=
      hilbert_sameSide_symm
        Geo A D base hSame

    exact
      False.elim
        ((hilbert_oppositeSide_not_sameSide
            Geo D A base hOppDA)
          hSameDA)

/--
A strict inequality between two right angles with the same first
base ray is impossible when their second rays lie in the same
half-plane.
-/
theorem proposition39_test_right_angle_less_impossible
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    False := by

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hLess.1

  have hXFD :
      ¬ PrimCollinear Geo X F D :=
    hLess.2.1

  rcases
      HilbertOrder.between_extension
        X F hFX.symm
    with
    ⟨Y, hXFY⟩

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFY :
      F ≠ Y :=
    hXFYData.2.1

  have hYbase :
      HilbertIncidence.OnLine Y base :=
    hilbert_collinear_on_line
      Geo
      X F Y
      base
      hXFYData.1
      hXbase
      hFbase
      hXFYData.2.2.2.1

  have hInsideA :
      HilbertRayMeetsSegment Geo F A X D :=
    proposition39_test_angle_less_ray_inside
      Geo
      A D F X
      base
      hFbase
      hXbase
      hFX
      hSame
      hLess

  have hInsideD :
      HilbertRayMeetsSegment Geo F D A Y :=
    proposition39_test_inside_flip
      Geo
      A D F X Y
      base
      hFbase
      hXbase
      hYbase
      hSame
      hXFY
      hInsideA

  have hAFY :
      ¬ PrimCollinear Geo A F Y := by

    have hFYA :
        ¬ PrimCollinear Geo F Y A :=
      hilbert_not_collinear_of_off_line
        Geo
        F Y A
        base
        hFY
        hFbase
        hYbase
        hSame.1

    intro h

    exact
      hFYA
        (PrimCollinearCycle
          Geo A F Y h)

  have hDFY :
      ¬ PrimCollinear Geo D F Y := by

    have hFYD :
        ¬ PrimCollinear Geo F Y D :=
      hilbert_not_collinear_of_off_line
        Geo
        F Y D
        base
        hFY
        hFbase
        hYbase
        hSame.2.1

    intro h

    exact
      hFYD
        (PrimCollinearCycle
          Geo D F Y h)

  have hXFA_AFY :
      Geo.AngleCongruent X F A A F Y :=
    proposition39_test_right_angle_chosen_supplement
      Geo
      A F X Y
      hXFY
      hXFA
      hRightA

  have hXFD_DFY :
      Geo.AngleCongruent X F D D F Y :=
    proposition39_test_right_angle_chosen_supplement
      Geo
      D F X Y
      hXFY
      hXFD
      hRightD

  have hXFA_DFY :
      HilbertAngleLess Geo X F A D F Y :=
    hilbert_angleLess_transport_right
      Geo
      X F A
      X F D
      D F Y
      hLess
      hDFY
      hXFD_DFY

  have hAFY_XFA :
      Geo.AngleCongruent A F Y X F A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X F A
      A F Y
      hXFA_AFY

  have hAFY_DFY :
      HilbertAngleLess Geo A F Y D F Y :=
    hilbert_angleLess_transport_left
      Geo
      X F A
      A F Y
      D F Y
      hXFA_DFY
      hAFY
      hAFY_XFA

  rcases hInsideD with
    ⟨K, hAKY, hRayFDK⟩

  have hYKA :
      Geo.Between Y K A :=
    (HilbertOrder.between_incidence
      A K Y hAKY).2.2.2.2

  have hInsideDrev :
      HilbertRayMeetsSegment Geo F D Y A :=
    ⟨K,
      hYKA,
      hRayFDK⟩

  have hYFA :
      ¬ PrimCollinear Geo Y F A := by

    intro h

    exact
      hAFY
        (PrimCollinearSymm
          Geo Y F A h)

  have hYFD_YFA :
      HilbertAngleLess Geo Y F D Y F A :=
    hilbert_interior_angle_less
      Geo
      F D Y A
      hYFA
      hInsideDrev

  have hYFDrefl :
      Geo.AngleCongruent Y F D Y F D :=
    Geo.angle_congruent_reflexive
      Y F D

  have hDFY_YFD :
      Geo.AngleCongruent D F Y Y F D :=
    (Geo.angle_congruent_reverse_first
      Y F D
      Y F D).mp
      hYFDrefl

  have hDFY_YFA :
      HilbertAngleLess Geo D F Y Y F A :=
    hilbert_angleLess_transport_left
      Geo
      Y F D
      D F Y
      Y F A
      hYFD_YFA
      hDFY
      hDFY_YFD

  have hYFArefl :
      Geo.AngleCongruent Y F A Y F A :=
    Geo.angle_congruent_reflexive
      Y F A

  have hYFA_AFY :
      Geo.AngleCongruent Y F A A F Y :=
    (Geo.angle_congruent_reverse_second
      Y F A
      Y F A).mp
      hYFArefl

  have hDFY_AFY :
      HilbertAngleLess Geo D F Y A F Y :=
    hilbert_angleLess_transport_right
      Geo
      D F Y
      Y F A
      A F Y
      hDFY_YFA
      hAFY
      hYFA_AFY

  have hCycle :
      HilbertAngleLess Geo A F Y A F Y :=
    hilbert_angleLess_trans
      Geo
      A F Y
      D F Y
      A F Y
      hAFY_DFY
      hDFY_AFY

  exact
    (hilbert_angleLess_irrefl
      Geo A F Y)
      hCycle

/--
Two right angles erected from the same base ray into the same
half-plane are congruent.
-/
theorem proposition39_test_same_base_right_angles_congruent
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D) :
    Geo.AngleCongruent X F A X F D := by

  rcases
      proposition39_test_same_foot_angle_cases
        Geo
        A D F X
        base
        hFbase
        hXbase
        hFX
        hSame
    with
    hCong | hLessAD | hLessDA

  · exact hCong

  · exact
      False.elim
        (proposition39_test_right_angle_less_impossible
          Geo
          A D F X
          base
          hFbase
          hXbase
          hFX
          hSame
          hRightA
          hRightD
          hLessAD)

  · have hSameDA :
        HilbertSameSide Geo D A base :=
      hilbert_sameSide_symm
        Geo A D base hSame

    exact
      False.elim
        (proposition39_test_right_angle_less_impossible
          Geo
          D A F X
          base
          hFbase
          hXbase
          hFX
          hSameDA
          hRightD
          hRightA
          hLessDA)

/--
All right angles are congruent.

This is Hilbert Theorem 21 in a form with explicit carrier lines
for the two first arms.
-/
theorem proposition39_test_all_right_angles_congruent
    [HilbertCongruence Geo]
    (A D F G X E : Geo.Point)
    (base1 base2 : Geo.Line)
    (hFbase1 : HilbertIncidence.OnLine F base1)
    (hXbase1 : HilbertIncidence.OnLine X base1)
    (hAoff : Not (HilbertIncidence.OnLine A base1))
    (hGbase2 : HilbertIncidence.OnLine G base2)
    (hEbase2 : HilbertIncidence.OnLine E base2)
    (hDoff : Not (HilbertIncidence.OnLine D base2))
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo E G D) :
    Geo.AngleCongruent X F A E G D := by

  rcases hRightA with
    ⟨Y, hXFY, hRightAeq⟩

  rcases hRightD with
    ⟨T, hEGT, hRightDeq⟩

  have hXF :
      X ≠ F :=
    (HilbertOrder.between_incidence
      X F Y hXFY).1

  have hEG :
      E ≠ G :=
    (HilbertOrder.between_incidence
      E G T hEGT).1

  have hGE :
      G ≠ E :=
    hEG.symm

  have hXFA :
      Not (PrimCollinear Geo X F A) :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      base1
      hXF
      hXbase1
      hFbase1
      hAoff

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X F A
        E G D
        hXFA
        hEG
        base2
        hEbase2
        hGbase2
        hDoff
    with
    ⟨K, hKDSame, hCopy, _hUnique⟩

  have hEGK :
      Not (PrimCollinear Geo E G K) :=
    hilbert_not_collinear_of_off_line
      Geo
      E G K
      base2
      hEG
      hEbase2
      hGbase2
      hKDSame.1

  have hSupp :
      Geo.AngleCongruent A F Y K G T :=
    hilbert_adjacent_angles_congruent
      Geo
      X F A Y
      E G K T
      hXFY
      hEGT
      hXFA
      hEGK
      hCopy

  have hEGK_XFA :
      Geo.AngleCongruent E G K X F A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X F A
      E G K
      hCopy

  have hEGK_AFY :
      Geo.AngleCongruent E G K A F Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G K
      X F A
      A F Y
      hEGK_XFA
      hRightAeq

  have hEGK_KGT :
      Geo.AngleCongruent E G K K G T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G K
      A F Y
      K G T
      hEGK_AFY
      hSupp

  have hRightK :
      HilbertRightAngle Geo E G K :=
    ⟨T,
      hEGT,
      hEGK_KGT⟩

  have hRightD' :
      HilbertRightAngle Geo E G D :=
    ⟨T,
      hEGT,
      hRightDeq⟩

  have hKGD :
      Geo.AngleCongruent E G K E G D :=
    proposition39_test_same_base_right_angles_congruent
      Geo
      K D G E
      base2
      hGbase2
      hEbase2
      hGE
      hKDSame
      hRightK
      hRightD'

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X F A
      E G K
      E G D
      hCopy
      hKGD

theorem proposition39_test_theorem_21
    [HilbertCongruence Geo]
    (A O B A' O' B' : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'OB' : Not (PrimCollinear Geo A' O' B'))
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B') :
    Geo.AngleCongruent A O B A' O' B' := by

  have hAO :
      A ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A O B hAOB

  have hA'O' :
      A' ≠ O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hA'OB'

  rcases
      HilbertPlaneIncidence.line_through
        A O hAO
    with
    ⟨base1, hAbase1, hObase1⟩

  rcases
      HilbertPlaneIncidence.line_through
        A' O' hA'O'
    with
    ⟨base2, hA'base2, hO'base2⟩

  have hBoff :
      Not (HilbertIncidence.OnLine B base1) := by
    intro hBbase1
    exact
      hAOB
        ⟨base1,
          hAbase1,
          hObase1,
          hBbase1⟩

  have hB'off :
      Not (HilbertIncidence.OnLine B' base2) := by
    intro hB'base2
    exact
      hA'OB'
        ⟨base2,
          hA'base2,
          hO'base2,
          hB'base2⟩

  exact
    proposition39_test_all_right_angles_congruent
      Geo
      B B'
      O O'
      A A'
      base1 base2
      hObase1
      hAbase1
      hBoff
      hO'base2
      hA'base2
      hB'off
      hRight
      hRight'




------------------------------------------------------------------------
-- Circle theory after Theorem 21
------------------------------------------------------------------------

/-
First problem.

Determine whether the existing Hilbert development, together with
temporary Theorem 21, suffices to reconstruct the elementary circle
theorems used by Hilbert after Section 6.

The immediate concrete case is the circle argument occurring in the
special Pascal configuration of Section 14.
-/


------------------------------------------------------------------------
-- First consequence of temporary Theorem 21
------------------------------------------------------------------------

/--
Two lines perpendicular to the same transversal are parallel.

The points O and P lie on the transversal, with E between them.
The rays OB and PD lie on opposite sides of the transversal.

Theorem 21 gives congruence of the two right angles EOB and EPD.
Hilbert Theorem 30 then converts the equal alternate angles into
parallelism of OB and PD.
-/
theorem proposition39_test_perpendiculars_parallel
    [HilbertCongruence Geo]
    (O E P B D : Geo.Point)
    (trans : Geo.Line)
    (hOEP : Geo.Between O E P)
    (hOtrans : HilbertIncidence.OnLine O trans)
    (hPtrans : HilbertIncidence.OnLine P trans)
    (hOpp : HilbertOppositeSide Geo B D trans)
    (hEOB : Not (PrimCollinear Geo E O B))
    (hEPD : Not (PrimCollinear Geo E P D))
    (hRightO : HilbertRightAngle Geo E O B)
    (hRightP : HilbertRightAngle Geo E P D) :
    Geo.Parallel O B P D := by

  have hAngles :
      Geo.AngleCongruent E O B E P D :=
    proposition39_test_theorem_21
      Geo
      E O B
      E P D
      hEOB
      hEPD
      hRightO
      hRightP

  exact
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      O B
      P E D
      trans
      hOEP
      hOtrans
      hPtrans
      hOpp
      hAngles

theorem proposition39_test_right_angle_exists
    [HilbertCongruence Geo]
    (A O C : Geo.Point)
    (hAOC : Geo.Between A O C) :
    ∃ B : Geo.Point,
      Not (PrimCollinear Geo A O B) ∧
      HilbertRightAngle Geo A O B := by

  exact
    hilbert_right_angle_exists_nondegenerate
      Geo A O C hAOC

------------------------------------------------------------------------
-- Copying a right angle to the opposite side of a transversal
------------------------------------------------------------------------

/--
A right angle erected at O can be copied at P on the opposite side
of the common transversal.

The construction uses Hilbert III.4.  The point S is obtained by
extending BO through O; hence B and S lie on opposite sides of the
transversal.  The copied ray PD is constructed on the side containing
S, so B and D are on opposite sides.

Notice that Theorem 21 is not needed here: the second right angle is
congruent to the first one by construction.
-/
theorem proposition39_test_copy_right_angle_opposite_side
    [HilbertCongruence Geo]
    (A O P B : Geo.Point)
    (trans : Geo.Line)
    (hAOP : Geo.Between A O P)
    (hAtrans : HilbertIncidence.OnLine A trans)
    (hOtrans : HilbertIncidence.OnLine O trans)
    (hPtrans : HilbertIncidence.OnLine P trans)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRightO : HilbertRightAngle Geo A O B) :
    ∃ D : Geo.Point,
      Not (PrimCollinear Geo O P D) ∧
      HilbertRightAngle Geo O P D ∧
      HilbertOppositeSide Geo B D trans ∧
      Geo.AngleCongruent A O B O P D := by

  have hOP :
      O ≠ P :=
    (HilbertOrder.between_incidence
      A O P hAOP).2.1

  have hBO :
      B ≠ O := by
    intro hBO
    subst B
    exact
      hAOB
        (PrimCollinear.mk
          (Geo := Geo)
          hAtrans
          hOtrans
          hOtrans)

  have hBoff :
      Not (HilbertIncidence.OnLine B trans) := by
    intro hBtrans
    exact
      hAOB
        (PrimCollinear.mk
          (Geo := Geo)
          hAtrans
          hOtrans
          hBtrans)

  --------------------------------------------------------------------
  -- Extend BO through O:
  --
  --     B - O - S.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        B O hBO
    with
    ⟨S, hBOS⟩

  have hBOSData :=
    HilbertOrder.between_incidence
      B O S hBOS

  have hOS :
      O ≠ S :=
    hBOSData.2.1

  have hBOScol :
      PrimCollinear Geo B O S :=
    hBOSData.2.2.2.1

  --------------------------------------------------------------------
  -- S is off the transversal.
  --------------------------------------------------------------------

  have hSoff :
      Not (HilbertIncidence.OnLine S trans) := by

    intro hStrans

    have hOSB :
        PrimCollinear Geo O S B :=
      PrimCollinearCycle
        Geo B O S hBOScol

    have hBtrans :
        HilbertIncidence.OnLine B trans :=
      hilbert_collinear_on_line
        Geo
        O S B
        trans
        hOS
        hOtrans
        hStrans
        hOSB

    exact hBoff hBtrans

  --------------------------------------------------------------------
  -- B and S are on opposite sides of the transversal because
  -- segment BS meets it at O.
  --------------------------------------------------------------------

  have hOppBS :
      HilbertOppositeSide Geo B S trans :=
    ⟨hBoff,
      hSoff,
      ⟨O, hBOS, hOtrans⟩⟩

  --------------------------------------------------------------------
  -- Copy angle AOB at P with first ray PO, choosing the side
  -- containing S.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A O B
        O P S
        hAOB
        hOP
        trans
        hOtrans
        hPtrans
        hSoff
    with
    ⟨D, hDSsame, hAngle, _hUnique⟩

  have hDoff :
      Not (HilbertIncidence.OnLine D trans) :=
    hDSsame.1

  have hOPD :
      Not (PrimCollinear Geo O P D) :=
    hilbert_not_collinear_of_off_line
      Geo
      O P D
      trans
      hOP
      hOtrans
      hPtrans
      hDoff

  --------------------------------------------------------------------
  -- Congruence transports rightness to the copied angle.
  --------------------------------------------------------------------

  have hRightP :
      HilbertRightAngle Geo O P D :=
    hilbert_right_angle_transport
      Geo
      A O B
      O P D
      hAOB
      hOPD
      hRightO
      hAngle

  --------------------------------------------------------------------
  -- D lies on the same side as S, hence on the opposite side from B.
  --------------------------------------------------------------------

  have hSDsame :
      HilbertSameSide Geo S D trans :=
    hilbert_sameSide_symm
      Geo D S trans hDSsame

  have hOppBD :
      HilbertOppositeSide Geo B D trans :=
    hilbert_oppositeSide_transport_right
      Geo
      B S D
      trans
      hOppBS
      hSDsame

  exact
    ⟨D,
      hOPD,
      hRightP,
      hOppBD,
      hAngle⟩

------------------------------------------------------------------------
-- Parallelism of the copied perpendicular
------------------------------------------------------------------------

/--
A right angle at O can be copied at P so that the two perpendicular
lines are parallel.

The proof uses the opposite-side construction above and the neutral
direction of Hilbert Theorem 30: congruent alternate angles imply
parallel lines.

Theorem 21 is still not needed.
-/
theorem proposition39_test_copied_right_angle_parallel
    [HilbertCongruence Geo]
    (A O P B : Geo.Point)
    (trans : Geo.Line)
    (hAOP : Geo.Between A O P)
    (hAtrans : HilbertIncidence.OnLine A trans)
    (hOtrans : HilbertIncidence.OnLine O trans)
    (hPtrans : HilbertIncidence.OnLine P trans)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRightO : HilbertRightAngle Geo A O B) :
    ∃ D : Geo.Point,
      HilbertRightAngle Geo O P D ∧
      HilbertOppositeSide Geo B D trans ∧
      Geo.Parallel O B P D := by

  rcases
      proposition39_test_copy_right_angle_opposite_side
        Geo
        A O P B
        trans
        hAOP
        hAtrans
        hOtrans
        hPtrans
        hAOB
        hRightO
    with
    ⟨D,
      hOPD,
      hRightP,
      hOppBD,
      hAOB_OPD⟩

  have hOP :
      O ≠ P :=
    (HilbertOrder.between_incidence
      A O P hAOP).2.1

  --------------------------------------------------------------------
  -- Choose E strictly between O and P.
  --------------------------------------------------------------------

  rcases
      hilbert_between_exists
        Geo O P hOP
    with
    ⟨E, hOEP⟩

  have hEtrans :
      HilbertIncidence.OnLine E trans :=
    hilbert_between_on_line
      Geo
      O E P
      trans
      hOtrans
      hPtrans
      hOEP

  --------------------------------------------------------------------
  -- Since A-O-P and O-E-P, we also have A-O-E.
  --------------------------------------------------------------------

  have hPEO :
      Geo.Between P E O :=
    (HilbertOrder.between_incidence
      O E P hOEP).2.2.2.2

  have hPOA :
      Geo.Between P O A :=
    (HilbertOrder.between_incidence
      A O P hAOP).2.2.2.2

  have hEOA :
      Geo.Between E O A :=
    (hilbert_between_inner_trans
      Geo
      P E O A
      hPEO
      hPOA).1

  have hAOE :
      Geo.Between A O E :=
    (HilbertOrder.between_incidence
      E O A hEOA).2.2.2.2

  --------------------------------------------------------------------
  -- Because AOB is right, replacing OA by its opposite ray OE
  -- gives the same angle.
  --------------------------------------------------------------------

  have hAOB_BOE :
      Geo.AngleCongruent A O B B O E :=
    hilbert_right_angle_opposite_extension
      Geo
      A O B E
      hAOB
      hRightO
      hAOE

  have hAOB_EOB :
      Geo.AngleCongruent A O B E O B :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      B O E).mp hAOB_BOE

  have hEOB_AOB :
      Geo.AngleCongruent E O B A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      E O B
      hAOB_EOB

  have hEOB_OPD :
      Geo.AngleCongruent E O B O P D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E O B
      A O B
      O P D
      hEOB_AOB
      hAOB_OPD

  --------------------------------------------------------------------
  -- O and E determine the same ray from P.
  --------------------------------------------------------------------

  have hRayPEO :
      HilbertSameRay Geo P E O :=
    hilbert_sameRay_of_between
      Geo P E O hPEO

  have hRayPOE :
      HilbertSameRay Geo P O E :=
    hilbert_sameRay_symm
      Geo P E O hRayPEO

  have hAtP :
      Geo.Angle O P D =
      Geo.Angle E P D :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      P O E D
      hRayPOE

  have hAlternate :
      Geo.AngleCongruent E O B E P D := by

    unfold Geometry.Geo.AngleCongruent
      at hEOB_OPD ⊢

    rw [← hAtP]

    exact hEOB_OPD

  --------------------------------------------------------------------
  -- Equal alternate angles imply parallel lines.
  --------------------------------------------------------------------

  have hParallel :
      Geo.Parallel O B P D :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      O B
      P E D
      trans
      hOEP
      hOtrans
      hPtrans
      hOppBD
      hAlternate

  exact
    ⟨D,
      hRightP,
      hOppBD,
      hParallel⟩

------------------------------------------------------------------------
-- Perpendicular bisector: construction data
------------------------------------------------------------------------

/--
For every nondegenerate segment AB there is a midpoint M and a line
through M perpendicular to AB.

At this stage this is only construction data:
M lies between A and B, AM is congruent to MB, and MX is a
nondegenerate perpendicular direction through M.
-/
theorem proposition39_test_perpendicular_bisector_exists
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ M X : Geo.Point,
    ∃ perp : Geo.Line,
      Geo.Between A M B ∧
      Geo.Congruent A M M B ∧
      HilbertIncidence.OnLine M perp ∧
      HilbertIncidence.OnLine X perp ∧
      Not (PrimCollinear Geo A M X) ∧
      HilbertRightAngle Geo A M X := by

  --------------------------------------------------------------------
  -- Midpoint of AB.
  --------------------------------------------------------------------

  rcases
      hilbert_midpoint_exists
        Geo A B hAB
    with
    ⟨M, hAMB, hAM_MB⟩

  --------------------------------------------------------------------
  -- Erect a right angle at the midpoint.
  --------------------------------------------------------------------

  rcases
      proposition39_test_right_angle_exists
        Geo A M B hAMB
    with
    ⟨X, hAMX, hRight⟩

  have hAM :
      A ≠ M :=
    (HilbertOrder.between_incidence
      A M B hAMB).1

  --------------------------------------------------------------------
  -- M and X are distinct.
  --------------------------------------------------------------------

  have hMX :
      M ≠ X := by

    intro hMX
    subst X

    apply hAMX

    rcases
        HilbertPlaneIncidence.line_through
          A M hAM
      with
      ⟨base, hAbase, hMbase⟩

    exact
      PrimCollinear.mk
        (Geo := Geo)
        hAbase
        hMbase
        hMbase

  --------------------------------------------------------------------
  -- Carrier of the perpendicular direction MX.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        M X hMX
    with
    ⟨perp, hMperp, hXperp⟩

  exact
    ⟨M, X, perp,
      hAMB,
      hAM_MB,
      hMperp,
      hXperp,
      hAMX,
      hRight⟩

------------------------------------------------------------------------
-- Perpendicular bisector: the constructed point is equidistant
------------------------------------------------------------------------

/--
Let M be the midpoint of AB and let MX be perpendicular to AB.
Then X is equidistant from A and B.

The proof is the standard SAS argument for triangles MAX and MBX.
No use of Theorem 21 is required.
-/
theorem proposition39_test_perpendicular_bisector_point_equidistant
    [HilbertCongruence Geo]
    (A M B X : Geo.Point)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X) :
    Geo.Congruent A X B X := by

  --------------------------------------------------------------------
  -- Nondegeneracy of triangle MAX.
  --------------------------------------------------------------------

  have hMAX :
      Not (PrimCollinear Geo M A X) := by
    intro h
    exact
      hAMX
        (PrimCollinearSwap
          Geo M A X h)

  --------------------------------------------------------------------
  -- Nondegeneracy of triangle MBX.
  --------------------------------------------------------------------

  have hMB :
      M ≠ B :=
    (HilbertOrder.between_incidence
      A M B hAMB).2.1

  have hAMBcol :
      PrimCollinear Geo A M B :=
    (HilbertOrder.between_incidence
      A M B hAMB).2.2.2.1

  have hMBX :
      Not (PrimCollinear Geo M B X) := by

    intro hMBX

    have hAMXcol :
        PrimCollinear Geo A M X :=
      hilbert_primCollinear_trans
        Geo
        A M B X
        hMB
        hAMBcol
        hMBX

    exact hAMX hAMXcol

  --------------------------------------------------------------------
  -- MA is congruent to MB.
  --------------------------------------------------------------------

  have hMA_MB :
      Geo.Congruent M A M B :=
    (Geometry.Geo.congruent_reverse_first
      Geo A M M B).mp hAM_MB

  --------------------------------------------------------------------
  -- The right angle AMX is congruent to BMX.
  --
  -- Since A-M-B, the rays MA and MB are opposite.
  --------------------------------------------------------------------

  have hAMX_XMB :
      Geo.AngleCongruent A M X X M B :=
    hilbert_right_angle_opposite_extension
      Geo
      A M X B
      hAMX
      hRight
      hAMB

  have hAMX_BMX :
      Geo.AngleCongruent A M X B M X :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A M X
      X M B).mp hAMX_XMB

  --------------------------------------------------------------------
  -- MX is common.
  --------------------------------------------------------------------

  have hMX_MX :
      Geo.Congruent M X M X :=
    hilbert_congruent_reflexive
      Geo M X

  --------------------------------------------------------------------
  -- SAS for triangles MAX and MBX.
  --------------------------------------------------------------------

  have hTriangles :
      TriangleCongruenceResult
        Geo
        M A X
        M B X :=
    hilbert_theorem_12_SAS
      Geo
      M A X
      M B X
      hMAX
      hMBX
      hMA_MB
      hAMX_BMX
      hMX_MX

  exact hTriangles.sideBC

------------------------------------------------------------------------
-- Right angle along the same perpendicular ray
------------------------------------------------------------------------

/--
Moving the second side of a right angle along the same ray preserves
the right angle.

This is purely ray invariance of the angle; Theorem 21 is not used.
-/
theorem proposition39_test_right_angle_sameRay_second
    [HilbertCongruence Geo]
    (A M X P : Geo.Point)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X)
    (hRay : HilbertSameRay Geo M X P) :
    Not (PrimCollinear Geo A M P) ∧
    HilbertRightAngle Geo A M P := by

  have hMP :
      M ≠ P :=
    hRay.2.1.symm

  have hMXP :
      PrimCollinear Geo M X P :=
    hRay.2.2.1

  have hMPX :
      PrimCollinear Geo M P X :=
    PrimCollinearRotate
      Geo M X P hMXP

  --------------------------------------------------------------------
  -- AMP is noncollinear.
  --------------------------------------------------------------------

  have hAMP :
      Not (PrimCollinear Geo A M P) := by

    intro hAMP

    have hAMXcol :
        PrimCollinear Geo A M X :=
      hilbert_primCollinear_trans
        Geo
        A M P X
        hMP
        hAMP
        hMPX

    exact hAMX hAMXcol

  --------------------------------------------------------------------
  -- X and P determine the same ray from M, hence the same angle.
  --------------------------------------------------------------------

  have hAngleEq :
      Geo.Angle A M X =
      Geo.Angle A M P :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      M A X P
      hRay

  have hRefl :
      Geo.AngleCongruent
        A M X
        A M X :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A M X
      hAMX

  have hAngle :
      Geo.AngleCongruent
        A M X
        A M P := by

    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢

    rw [← hAngleEq]

    exact hRefl

  --------------------------------------------------------------------
  -- Transport rightness along the congruent angle.
  --------------------------------------------------------------------

  have hRightP :
      HilbertRightAngle Geo A M P :=
    hilbert_right_angle_transport
      Geo
      A M X
      A M P
      hAMX
      hAMP
      hRight
      hAngle

  exact ⟨hAMP, hRightP⟩

------------------------------------------------------------------------
-- Perpendicular bisector: equidistance on one ray
------------------------------------------------------------------------

/--
Every point P on the ray MX of the perpendicular bisector of AB
is equidistant from A and B.

First the right angle AMX is transported along the ray MX to AMP.
Then the standard SAS argument for triangles MAP and MBP applies.
-/
theorem proposition39_test_perpendicular_bisector_sameRay_equidistant
    [HilbertCongruence Geo]
    (A M B X P : Geo.Point)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X)
    (hRay : HilbertSameRay Geo M X P) :
    Geo.Congruent A P B P := by

  --------------------------------------------------------------------
  -- The perpendicular direction is unchanged along ray MX.
  --------------------------------------------------------------------

  rcases
      proposition39_test_right_angle_sameRay_second
        Geo
        A M X P
        hAMX
        hRight
        hRay
    with
    ⟨hAMP, hRightP⟩

  --------------------------------------------------------------------
  -- Apply the midpoint + right-angle SAS lemma at P.
  --------------------------------------------------------------------

  exact
    proposition39_test_perpendicular_bisector_point_equidistant
      Geo
      A M B P
      hAMB
      hAM_MB
      hAMP
      hRightP

------------------------------------------------------------------------
-- Right angle on the opposite perpendicular ray
------------------------------------------------------------------------

/--
If AMX is right and X-M-P, then AMP is right as well.

The two pairs of vertical angles transfer the defining congruence
of the right angle from the ray MX to its opposite ray MP.
No use of Theorem 21 is required.
-/
theorem proposition39_test_right_angle_oppositeRay_second
    [HilbertCongruence Geo]
    (A M X P : Geo.Point)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X)
    (hXMP : Geo.Between X M P) :
    Not (PrimCollinear Geo A M P) ∧
    HilbertRightAngle Geo A M P := by

  have hXMPData :=
    HilbertOrder.between_incidence
      X M P hXMP

  have hMP :
      M ≠ P :=
    hXMPData.2.1

  have hXMPcol :
      PrimCollinear Geo X M P :=
    hXMPData.2.2.2.1

  have hPMX :
      Geo.Between P M X :=
    hXMPData.2.2.2.2

  --------------------------------------------------------------------
  -- AMP is noncollinear.
  --------------------------------------------------------------------

  have hAMP :
      Not (PrimCollinear Geo A M P) := by

    intro hAMP

    have hMPX :
        PrimCollinear Geo M P X :=
      PrimCollinearCycle
        Geo X M P hXMPcol

    have hAMXcol :
        PrimCollinear Geo A M X :=
      hilbert_primCollinear_trans
        Geo
        A M P X
        hMP
        hAMP
        hMPX

    exact hAMX hAMXcol

  --------------------------------------------------------------------
  -- Unpack the defining opposite ray of the right angle AMX.
  --
  --     A - M - C
  --------------------------------------------------------------------

  rcases hRight with
    ⟨C, hAMC, hAMX_XMC⟩

  have hAMCData :=
    HilbertOrder.between_incidence
      A M C hAMC

  have hMC :
      M ≠ C :=
    hAMCData.2.1

  have hAMCcol :
      PrimCollinear Geo A M C :=
    hAMCData.2.2.2.1

  have hCMA :
      Geo.Between C M A :=
    hAMCData.2.2.2.2

  --------------------------------------------------------------------
  -- PMC is also noncollinear.
  --------------------------------------------------------------------

  have hPMC :
      Not (PrimCollinear Geo P M C) := by

    intro hPMC

    have hMCP :
        PrimCollinear Geo M C P :=
      PrimCollinearCycle
        Geo P M C hPMC

    have hAMPcol :
        PrimCollinear Geo A M P :=
      hilbert_primCollinear_trans
        Geo
        A M C P
        hMC
        hAMCcol
        hMCP

    exact hAMP hAMPcol

  --------------------------------------------------------------------
  -- First vertical pair:
  --
  --     angle AMP = angle CMX = angle XMC.
  --------------------------------------------------------------------

  have hAMP_CMX :
      Geo.AngleCongruent A M P C M X :=
    hilbert_vertical_angles
      Geo
      A M P C X
      hAMC
      hPMX
      hAMP

  have hAMP_XMC :
      Geo.AngleCongruent A M P X M C :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A M P
      C M X).mp hAMP_CMX

  --------------------------------------------------------------------
  -- Second vertical pair:
  --
  --     angle PMC = angle XMA = angle AMX.
  --------------------------------------------------------------------

  have hPMC_XMA :
      Geo.AngleCongruent P M C X M A :=
    hilbert_vertical_angles
      Geo
      P M C X A
      hPMX
      hCMA
      hPMC

  have hPMC_AMX :
      Geo.AngleCongruent P M C A M X :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      P M C
      X M A).mp hPMC_XMA

  have hXMC_AMX :
      Geo.AngleCongruent X M C A M X :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A M X
      X M C
      hAMX_XMC

  have hAMX_PMC :
      Geo.AngleCongruent A M X P M C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      P M C
      A M X
      hPMC_AMX

  --------------------------------------------------------------------
  -- Chain:
  --
  --     AMP ~= XMC ~= AMX ~= PMC.
  --------------------------------------------------------------------

  have hAMP_AMX :
      Geo.AngleCongruent A M P A M X :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A M P
      X M C
      A M X
      hAMP_XMC
      hXMC_AMX

  have hAMP_PMC :
      Geo.AngleCongruent A M P P M C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A M P
      A M X
      P M C
      hAMP_AMX
      hAMX_PMC

  exact
    ⟨hAMP,
      ⟨C, hAMC, hAMP_PMC⟩⟩

------------------------------------------------------------------------
-- Perpendicular bisector: equidistance on the opposite ray
------------------------------------------------------------------------

/--
Every point P on the ray opposite to MX is equidistant from A and B.

If X-M-P, the preceding lemma shows that AMP is again a right angle.
The midpoint + right-angle SAS argument then gives AP congruent to BP.
-/
theorem proposition39_test_perpendicular_bisector_oppositeRay_equidistant
    [HilbertCongruence Geo]
    (A M B X P : Geo.Point)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X)
    (hXMP : Geo.Between X M P) :
    Geo.Congruent A P B P := by

  rcases
      proposition39_test_right_angle_oppositeRay_second
        Geo
        A M X P
        hAMX
        hRight
        hXMP
    with
    ⟨hAMP, hRightP⟩

  exact
    proposition39_test_perpendicular_bisector_point_equidistant
      Geo
      A M B P
      hAMB
      hAM_MB
      hAMP
      hRightP

------------------------------------------------------------------------
-- Perpendicular bisector: every point is equidistant
------------------------------------------------------------------------

/--
Every point of the perpendicular bisector of AB is equidistant
from A and B.

For P distinct from M and X, Hilbert Theorem 4 orders the three
collinear points M, X, P.  The two same-ray cases reduce to the
same-ray lemma; the remaining case X-M-P reduces to the
opposite-ray lemma.
-/
theorem proposition39_test_perpendicular_bisector_equidistant
    [HilbertCongruence Geo]
    (A M B X P : Geo.Point)
    (perp : Geo.Line)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hMperp : HilbertIncidence.OnLine M perp)
    (hXperp : HilbertIncidence.OnLine X perp)
    (hPperp : HilbertIncidence.OnLine P perp)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X) :
    Geo.Congruent A P B P := by

  --------------------------------------------------------------------
  -- The midpoint itself is equidistant from A and B.
  --------------------------------------------------------------------

  by_cases hPM : P = M

  · subst P

    exact
      (Geometry.Geo.congruent_reverse_second
        Geo
        A M
        M B).mp hAM_MB

  --------------------------------------------------------------------
  -- The distinguished point X is already covered by the SAS lemma.
  --------------------------------------------------------------------

  by_cases hPX : P = X

  · subst P

    exact
      proposition39_test_perpendicular_bisector_point_equidistant
        Geo
        A M B X
        hAMB
        hAM_MB
        hAMX
        hRight

  --------------------------------------------------------------------
  -- M, X and P are now three distinct points on the same line.
  --------------------------------------------------------------------

  have hAM :
      A ≠ M :=
    (HilbertOrder.between_incidence
      A M B hAMB).1

  have hMX :
      M ≠ X := by

    intro h
    subst X

    apply hAMX

    rcases
        HilbertPlaneIncidence.line_through
          A M hAM
      with
      ⟨base, hAbase, hMbase⟩

    exact
      PrimCollinear.mk
        (Geo := Geo)
        hAbase
        hMbase
        hMbase

  have hXP :
      X ≠ P :=
    Ne.symm hPX

  have hMP :
      M ≠ P :=
    Ne.symm hPM

  have hMXPcol :
      PrimCollinear Geo M X P :=
    PrimCollinear.mk
      (Geo := Geo)
      hMperp
      hXperp
      hPperp

  --------------------------------------------------------------------
  -- Hilbert Theorem 4: exactly one of the three points lies between
  -- the other two.
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        M X P
        hMX
        hXP
        hMP
        hMXPcol
    with
    hMXP | hXMP | hMPX

  --------------------------------------------------------------------
  -- M-X-P: P lies on ray MX.
  --------------------------------------------------------------------

  · have hRay :
        HilbertSameRay Geo M X P :=
      hilbert_sameRay_of_between
        Geo M X P hMXP

    exact
      proposition39_test_perpendicular_bisector_sameRay_equidistant
        Geo
        A M B X P
        hAMB
        hAM_MB
        hAMX
        hRight
        hRay

  --------------------------------------------------------------------
  -- X-M-P: P lies on the ray opposite MX.
  --------------------------------------------------------------------

  · exact
      proposition39_test_perpendicular_bisector_oppositeRay_equidistant
        Geo
        A M B X P
        hAMB
        hAM_MB
        hAMX
        hRight
        hXMP

  --------------------------------------------------------------------
  -- M-P-X: P again lies on ray MX.
  --------------------------------------------------------------------

  · have hRayPX :
        HilbertSameRay Geo M P X :=
      hilbert_sameRay_of_between
        Geo M P X hMPX

    have hRayXP :
        HilbertSameRay Geo M X P :=
      hilbert_sameRay_symm
        Geo M P X hRayPX

    exact
      proposition39_test_perpendicular_bisector_sameRay_equidistant
        Geo
        A M B X P
        hAMB
        hAM_MB
        hAMX
        hRight
        hRayXP

------------------------------------------------------------------------
-- Perpendicular bisector and circle language
------------------------------------------------------------------------

/--
Every point P of the perpendicular bisector of AB is the center of
a circle through A and B.

The reference radius is PA.
-/
theorem proposition39_test_perpendicular_bisector_circle
    [HilbertCongruence Geo]
    (A M B X P : Geo.Point)
    (perp : Geo.Line)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hMperp : HilbertIncidence.OnLine M perp)
    (hXperp : HilbertIncidence.OnLine X perp)
    (hPperp : HilbertIncidence.OnLine P perp)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X) :
    HilbertCircle Geo P A A ∧
    HilbertCircle Geo P A B := by

  have hAP_BP :
      Geo.Congruent A P B P :=
    proposition39_test_perpendicular_bisector_equidistant
      Geo
      A M B X P
      perp
      hAMB
      hAM_MB
      hMperp
      hXperp
      hPperp
      hAMX
      hRight

  --------------------------------------------------------------------
  -- PA is congruent to itself.
  --------------------------------------------------------------------

  have hPA_PA :
      Geo.Congruent P A P A :=
    hilbert_congruent_reflexive
      Geo P A

  --------------------------------------------------------------------
  -- Rewrite AP ~= BP as PB ~= PA.
  --------------------------------------------------------------------

  have hBP_AP :
      Geo.Congruent B P A P :=
    CongruentSymmetry
      Geo
      A P
      B P
      hAP_BP

  have hPB_AP :
      Geo.Congruent P B A P :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      B P
      A P).mp hBP_AP

  have hPB_PA :
      Geo.Congruent P B P A :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      P B
      A P).mp hPB_AP

  exact
    ⟨hPA_PA,
      hPB_PA⟩

------------------------------------------------------------------------
-- Two perpendicular bisectors of a noncollinear triangle
------------------------------------------------------------------------

/--
For a noncollinear triangle ABC, the sides AB and AC admit
perpendicular-bisector construction data.
-/
theorem proposition39_test_two_perpendicular_bisectors_exist
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    ∃ M X perpAB N Y perpAC,
      Geo.Between A M B ∧
      Geo.Congruent A M M B ∧
      HilbertIncidence.OnLine M perpAB ∧
      HilbertIncidence.OnLine X perpAB ∧
      Not (PrimCollinear Geo A M X) ∧
      HilbertRightAngle Geo A M X ∧
      Geo.Between A N C ∧
      Geo.Congruent A N N C ∧
      HilbertIncidence.OnLine N perpAC ∧
      HilbertIncidence.OnLine Y perpAC ∧
      Not (PrimCollinear Geo A N Y) ∧
      HilbertRightAngle Geo A N Y := by

  have hAB :
      A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC :
      A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo
      A C B
      (fun h =>
        hABC
          (PrimCollinearRotate
            Geo A C B h))

  rcases
      proposition39_test_perpendicular_bisector_exists
        Geo A B hAB
    with
    ⟨M, X, perpAB,
      hAMB,
      hAM_MB,
      hMperpAB,
      hXperpAB,
      hAMX,
      hRightAB⟩

  rcases
      proposition39_test_perpendicular_bisector_exists
        Geo A C hAC
    with
    ⟨N, Y, perpAC,
      hANC,
      hAN_NC,
      hNperpAC,
      hYperpAC,
      hANY,
      hRightAC⟩

  exact
    ⟨M, X, perpAB,
      N, Y, perpAC,
      hAMB,
      hAM_MB,
      hMperpAB,
      hXperpAB,
      hAMX,
      hRightAB,
      hANC,
      hAN_NC,
      hNperpAC,
      hYperpAC,
      hANY,
      hRightAC⟩


/--
Two disjoint Hilbert incidence lines determine parallel point-lines,
provided the chosen endpoint pairs are nondegenerate.
-/
theorem proposition39_test_parallel_of_disjoint_lines
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (lineAB lineCD : Geo.Line)
    (hAB : Ne A B)
    (hCD : Ne C D)
    (hAab : HilbertIncidence.OnLine A lineAB)
    (hBab : HilbertIncidence.OnLine B lineAB)
    (hCcd : HilbertIncidence.OnLine C lineCD)
    (hDcd : HilbertIncidence.OnLine D lineCD)
    (hDisjoint : HilbertLinesDisjoint Geo lineAB lineCD) :
    Geo.Parallel A B C D := by

  refine
    ⟨hAB, hCD, ?_⟩

  apply Set.disjoint_left.mpr

  intro P hPAB hPCD

  have hPab :
      HilbertIncidence.OnLine P lineAB :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      A B P
      lineAB
      hAB
      hAab
      hBab).mp hPAB

  have hPcd :
      HilbertIncidence.OnLine P lineCD :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      C D P
      lineCD
      hCD
      hCcd
      hDcd).mp hPCD

  exact
    hDisjoint
      ⟨P, hPab, hPcd⟩

/--
If the two perpendicular-bisector incidence lines are disjoint,
their nondegenerate point-line carriers are parallel.
-/
theorem proposition39_test_bisector_lines_parallel_of_disjoint
    [HilbertOrder Geo]
    (A M X N Y : Geo.Point)
    (perpAB perpAC : Geo.Line)
    (hMperpAB : HilbertIncidence.OnLine M perpAB)
    (hXperpAB : HilbertIncidence.OnLine X perpAB)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hNperpAC : HilbertIncidence.OnLine N perpAC)
    (hYperpAC : HilbertIncidence.OnLine Y perpAC)
    (hANY : Not (PrimCollinear Geo A N Y))
    (hDisjoint : HilbertLinesDisjoint Geo perpAB perpAC) :
    Geo.Parallel M X N Y := by

  have hMXA :
      Not (PrimCollinear Geo M X A) := by
    intro h

    exact
      hAMX
        (PrimCollinearCycle
          Geo X A M
          (PrimCollinearCycle
            Geo M X A h))

  have hMX :
      Ne M X :=
    hilbert_noncollinear_ne_first
      Geo M X A hMXA

  have hNYA :
      Not (PrimCollinear Geo N Y A) := by
    intro h

    exact
      hANY
        (PrimCollinearCycle
          Geo Y A N
          (PrimCollinearCycle
            Geo N Y A h))

  have hNY :
      Ne N Y :=
    hilbert_noncollinear_ne_first
      Geo N Y A hNYA

  exact
    proposition39_test_parallel_of_disjoint_lines
      Geo
      M X N Y
      perpAB perpAC
      hMX
      hNY
      hMperpAB
      hXperpAB
      hNperpAC
      hYperpAC
      hDisjoint

/--
Two right-angle rays erected at the same point on the same side
of the reference line coincide.
-/
theorem proposition39_test_same_foot_perpendicular_same_ray
    [HilbertCongruence Geo]
    (X F A D : Geo.Point)
    (base : Geo.Line)
    (hXF : Ne X F)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFbase : HilbertIncidence.OnLine F base)
    (hAoff : Not (HilbertIncidence.OnLine A base))
    (hSame : HilbertSameSide Geo A D base)
    (hXFA : Not (PrimCollinear Geo X F A))
    (hXFD : Not (PrimCollinear Geo X F D))
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D) :
    HilbertSameRay Geo F A D := by

  have hAngles :
      Geo.AngleCongruent X F A X F D :=
    proposition39_test_theorem_21
      Geo
      X F A
      X F D
      hXFA
      hXFD
      hRightA
      hRightD

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X F A
        X F A
        hXFA
        hXF
        base
        hXbase
        hFbase
        hAoff
    with
    ⟨Z, _hZASame, _hAngleZ, hUnique⟩

  have hAASame :
      HilbertSameSide Geo A A base :=
    hilbert_sameSide_refl
      Geo A base hAoff

  have hAngleRefl :
      Geo.AngleCongruent X F A X F A :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      X F A
      hXFA

  have hRayZA :
      HilbertSameRay Geo F Z A :=
    hUnique
      A
      hAASame
      hAngleRefl

  have hDASame :
      HilbertSameSide Geo D A base :=
    hilbert_sameSide_symm
      Geo A D base hSame

  have hRayZD :
      HilbertSameRay Geo F Z D :=
    hUnique
      D
      hDASame
      hAngles

  exact
    bookZero_36_ray3
      Geo
      F Z A D
      hRayZA
      hRayZD

/--
Reversing the perpendicular ray preserves a right angle.
-/
theorem proposition39_test_right_angle_opposite_perp
    [HilbertCongruence Geo]
    (A A' F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hAoff : Not (HilbertIncidence.OnLine A base))
    (hAFA' : Geo.Between A F A')
    (hRight : HilbertRightAngle Geo X F A) :
    HilbertRightAngle Geo X F A' := by

  rcases hRight with
    ⟨Y, hXFY, hRightEq⟩

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFX : Ne F X :=
    hXFYData.1.symm

  have hFY : Ne F Y :=
    hXFYData.2.1

  have hYbase :
      HilbertIncidence.OnLine Y base :=
    hilbert_collinear_on_line
      Geo
      X F Y
      base
      hXFYData.1
      hXbase
      hFbase
      hXFYData.2.2.2.1

  have hFXA :
      Not (PrimCollinear Geo F X A) :=
    hilbert_not_collinear_of_off_line
      Geo
      F X A
      base
      hFX
      hFbase
      hXbase
      hAoff

  have hAFX :
      Not (PrimCollinear Geo A F X) := by
    intro h

    exact
      hFXA
        (PrimCollinearCycle
          Geo A F X h)

  have hFYA :
      Not (PrimCollinear Geo F Y A) :=
    hilbert_not_collinear_of_off_line
      Geo
      F Y A
      base
      hFY
      hFbase
      hYbase
      hAoff

  have hAFY :
      Not (PrimCollinear Geo A F Y) := by
    intro h

    exact
      hFYA
        (PrimCollinearCycle
          Geo A F Y h)

  have hAFX_AFY :
      Geo.AngleCongruent A F X A F Y :=
    (Geo.angle_congruent_reverse_first
      X F A
      A F Y).mp hRightEq

  have hSupp :
      Geo.AngleCongruent X F A' Y F A' :=
    hilbert_adjacent_angles_congruent
      Geo
      A F X A'
      A F Y A'
      hAFA'
      hAFA'
      hAFX
      hAFY
      hAFX_AFY

  have hTarget :
      Geo.AngleCongruent X F A' A' F Y :=
    (Geo.angle_congruent_reverse_second
      X F A'
      Y F A').mp hSupp

  exact
    ⟨Y, hXFY, hTarget⟩

/--
Reversing the base ray of a right angle preserves rightness.
-/
theorem proposition39_test_right_angle_opposite_base
    [HilbertCongruence Geo]
    (A A' F X : Geo.Point)
    (hAFA' : Geo.Between A F A')
    (hAFX : Not (PrimCollinear Geo A F X))
    (hRight : HilbertRightAngle Geo A F X) :
    HilbertRightAngle Geo A' F X := by

  rcases hRight with
    ⟨Y, hAFY, hRightEq⟩

  have hAFYData :=
    HilbertOrder.between_incidence
      A F Y hAFY

  have hFY :
      Ne F Y :=
    hAFYData.2.1

  have hAFYcol :
      PrimCollinear Geo A F Y :=
    hAFYData.2.2.2.1

  --------------------------------------------------------------------
  -- Y-F-X is noncollinear.
  --------------------------------------------------------------------

  have hYFX :
      Not (PrimCollinear Geo Y F X) := by

    intro hYFX

    have hFXY :
        PrimCollinear Geo F X Y :=
      PrimCollinearCycle
        Geo Y F X hYFX

    have hFYX :
        PrimCollinear Geo F Y X :=
      PrimCollinearRotate
        Geo F X Y hFXY

    have hAFXcol :
        PrimCollinear Geo A F X :=
      hilbert_primCollinear_trans
        Geo
        A F Y X
        hFY
        hAFYcol
        hFYX

    exact hAFX hAFXcol

  --------------------------------------------------------------------
  -- Reverse A-F-Y to Y-F-A.
  --------------------------------------------------------------------

  have hYFA :
      Geo.Between Y F A :=
    (HilbertOrder.between_incidence
      A F Y hAFY).2.2.2.2

  --------------------------------------------------------------------
  -- Rightness says
  --
  --     angle AFX ~= angle XFY.
  --
  -- Since angles are unoriented, reverse the second angle:
  --
  --     angle AFX ~= angle YFX.
  --------------------------------------------------------------------

  have hInitial :
      Geo.AngleCongruent A F X Y F X :=
    (Geo.angle_congruent_reverse_second
      A F X
      X F Y).mp hRightEq

  --------------------------------------------------------------------
  -- Apply Hilbert Theorem 14 to
  --
  --     A - F - A'
  --     Y - F - A.
  --
  -- This gives
  --
  --     angle XFA' ~= angle XFA.
  --------------------------------------------------------------------

  have hAdjacent :
      Geo.AngleCongruent X F A' X F A :=
    hilbert_adjacent_angles_congruent
      Geo
      A F X A'
      Y F X A
      hAFA'
      hYFA
      hAFX
      hYFX
      hInitial

  --------------------------------------------------------------------
  -- Reverse the first angle:
  --
  --     angle A'FX ~= angle XFA.
  --------------------------------------------------------------------

  have hTarget :
      Geo.AngleCongruent A' F X X F A :=
    (Geo.angle_congruent_reverse_first
      X F A'
      X F A).mp hAdjacent

  have hA'FA :
      Geo.Between A' F A :=
    (HilbertOrder.between_incidence
      A F A' hAFA').2.2.2.2

  exact
    ⟨A, hA'FA, hTarget⟩

/--
From a perpendicular at the midpoint M of AB, construct through A
a line parallel to that perpendicular.
-/
theorem proposition39_test_perpendicular_parallel_through_endpoint
    [HilbertCongruence Geo]
    (A B M X : Geo.Point)
    (hAMB : Geo.Between A M B)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X) :
    ∃ D : Geo.Point,
      HilbertRightAngle Geo M A D ∧
      Geo.Parallel M X A D := by

  have hAMBData :=
    HilbertOrder.between_incidence
      A M B hAMB

  have hMB :
      M ≠ B :=
    hAMBData.2.1

  have hAMBcol :
      PrimCollinear Geo A M B :=
    hAMBData.2.2.2.1

  --------------------------------------------------------------------
  -- Reverse the base ray of the right angle:
  --
  --     angle AMX right
  --
  -- gives
  --
  --     angle BMX right.
  --------------------------------------------------------------------

  have hRightB :
      HilbertRightAngle Geo B M X :=
    proposition39_test_right_angle_opposite_base
      Geo
      A B M X
      hAMB
      hAMX
      hRight

  --------------------------------------------------------------------
  -- BMX is noncollinear.
  --------------------------------------------------------------------

  have hBMX :
      Not (PrimCollinear Geo B M X) := by

    intro hBMX

    have hMBX :
        PrimCollinear Geo M B X :=
      PrimCollinearSwap
        Geo B M X hBMX

    have hAMXcol :
        PrimCollinear Geo A M X :=
      hilbert_primCollinear_trans
        Geo
        A M B X
        hMB
        hAMBcol
        hMBX

    exact hAMX hAMXcol

  --------------------------------------------------------------------
  -- Read A-M-B in the opposite direction B-M-A.
  --------------------------------------------------------------------

  have hBMA :
      Geo.Between B M A :=
    hAMBData.2.2.2.2

  --------------------------------------------------------------------
  -- Obtain the carrier of AB.
  --------------------------------------------------------------------

  rcases hAMBcol with
    ⟨trans,
      hAtrans,
      hMtrans,
      hBtrans⟩

  --------------------------------------------------------------------
  -- Copy the right angle from M to A.
  --
  -- The existing neutral construction returns
  --
  --     RightAngle M A D
  --     MX || AD.
  --------------------------------------------------------------------

  rcases
      proposition39_test_copied_right_angle_parallel
        Geo
        B M A X
        trans
        hBMA
        hBtrans
        hMtrans
        hAtrans
        hBMX
        hRightB
    with
    ⟨D,
      hRightA,
      _,
      hParallel⟩

  exact
    ⟨D,
      hRightA,
      hParallel⟩

/--
Two parallels through the same point determine the same extensional line.
-/
theorem proposition39_test_parallel_through_same_point_unique
    [HilbertEuclideanPlane Geo]
    (A D E N Y : Geo.Point)
    (hAD_NY : Geo.Parallel A D N Y)
    (hAE_NY : Geo.Parallel A E N Y) :
    Geo.PointLine A D = Geo.PointLine A E := by

  by_contra hDistinct

  have hAD_AE :
      Geo.Parallel A D A E :=
    hilbert_parallel_transitive_distinct
      Geo
      A D
      A E
      N Y
      hAD_NY
      hAE_NY
      hDistinct

  have hAinAD :
      A ∈ Geo.PointLine A D := by
    change Geo.LineCollinear A D A
    exact Or.inr (Or.inl rfl)

  have hAinAE :
      A ∈ Geo.PointLine A E := by
    change Geo.LineCollinear A E A
    exact Or.inr (Or.inl rfl)

  exact
    Set.disjoint_left.mp
      hAD_AE.2.2
      hAinAD
      hAinAE

/--
A line through A parallel to the first perpendicular bisector is also
parallel to the second perpendicular bisector, provided the two
perpendicular bisectors are parallel.
-/
theorem proposition39_test_endpoint_parallel_to_second_bisector
    [HilbertEuclideanPlane Geo]
    (A D M X N Y : Geo.Point)
    (perpAC : Geo.Line)
    (hNperpAC : HilbertIncidence.OnLine N perpAC)
    (hYperpAC : HilbertIncidence.OnLine Y perpAC)
    (hANY : Not (PrimCollinear Geo A N Y))
    (hMX_NY : Geo.Parallel M X N Y)
    (hMX_AD : Geo.Parallel M X A D) :
    Geo.Parallel A D N Y := by

  have hNYA :
      Not (PrimCollinear Geo N Y A) := by
    intro h

    exact
      hANY
        (PrimCollinearCycle
          Geo Y A N
          (PrimCollinearCycle
            Geo N Y A h))

  have hNY :
      Ne N Y :=
    hilbert_noncollinear_ne_first
      Geo N Y A hNYA

  --------------------------------------------------------------------
  -- A does not lie on the carrier NY.
  --------------------------------------------------------------------

  have hA_not_NY :
      Not ((Geo.PointLine N Y) A) := by

    intro hAinNY

    have hAperpAC :
        HilbertIncidence.OnLine A perpAC :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        N Y A
        perpAC
        hNY
        hNperpAC
        hYperpAC).mp hAinNY

    exact
      hANY
        ⟨perpAC,
          hAperpAC,
          hNperpAC,
          hYperpAC⟩

  --------------------------------------------------------------------
  -- Therefore PointLine AD and PointLine NY are distinct.
  --------------------------------------------------------------------

  have hDistinct :
      Ne (Geo.PointLine A D) (Geo.PointLine N Y) := by

    intro hEq

    have hAinAD :
        (Geo.PointLine A D) A := by
      change Geo.LineCollinear A D A
      exact Or.inr (Or.inl rfl)

    have hAinNY :
        (Geo.PointLine N Y) A := by
      rw [← hEq]
      exact hAinAD

    exact hA_not_NY hAinNY

  --------------------------------------------------------------------
  -- Both AD and NY are parallel to MX.
  --------------------------------------------------------------------

  have hAD_MX :
      Geo.Parallel A D M X :=
    (Geometry.Geo.parallel_symmetry
      Geo M X A D).mp hMX_AD

  have hNY_MX :
      Geo.Parallel N Y M X :=
    (Geometry.Geo.parallel_symmetry
      Geo M X N Y).mp hMX_NY

  exact
    hilbert_parallel_transitive_distinct
      Geo
      A D
      N Y
      M X
      hAD_MX
      hNY_MX
      hDistinct

/--
If the two perpendicular bisectors are parallel, then the two lines
constructed through A parallel to them determine the same carrier.
-/
theorem proposition39_test_endpoint_parallels_same_carrier
    [HilbertEuclideanPlane Geo]
    (A D E M X N Y : Geo.Point)
    (perpAC : Geo.Line)
    (hNperpAC : HilbertIncidence.OnLine N perpAC)
    (hYperpAC : HilbertIncidence.OnLine Y perpAC)
    (hANY : Not (PrimCollinear Geo A N Y))
    (hMX_NY : Geo.Parallel M X N Y)
    (hMX_AD : Geo.Parallel M X A D)
    (hNY_AE : Geo.Parallel N Y A E) :
    Geo.PointLine A D = Geo.PointLine A E := by

  have hAD_NY :
      Geo.Parallel A D N Y :=
    proposition39_test_endpoint_parallel_to_second_bisector
      Geo
      A D M X N Y
      perpAC
      hNperpAC
      hYperpAC
      hANY
      hMX_NY
      hMX_AD

  have hAE_NY :
      Geo.Parallel A E N Y :=
    (Geometry.Geo.parallel_symmetry
      Geo N Y A E).mp hNY_AE

  exact
    proposition39_test_parallel_through_same_point_unique
      Geo
      A D E N Y
      hAD_NY
      hAE_NY

/--
Swapping the two arms of a right angle preserves rightness.
-/
theorem proposition39_test_right_angle_swap
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo B O A := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h

    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hRefl :
      Geo.AngleCongruent A O B A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hAngle :
      Geo.AngleCongruent A O B B O A :=
    (Geo.angle_congruent_reverse_second
      A O B
      A O B).mp hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      B O A
      hAOB
      hBOA
      hRight
      hAngle

/--
If AD and AE have the same extensional carrier, then A, D and E
lie on one Hilbert incidence line.
-/
theorem proposition39_test_common_carrier_line
    [HilbertEuclideanPlane Geo]
    (A D E : Geo.Point)
    (hAD : A ≠ D)
    (hCarrier :
      Geo.PointLine A D =
      Geo.PointLine A E) :
    ∃ base : Geo.Line,
      HilbertIncidence.OnLine A base ∧
      HilbertIncidence.OnLine D base ∧
      HilbertIncidence.OnLine E base := by

  rcases
      HilbertPlaneIncidence.line_through
        A D hAD
    with
    ⟨base, hAbase, hDbase⟩

  have hEinAD :
      (Geo.PointLine A D) E := by

    rw [hCarrier]

    change Geo.LineCollinear A E E

    exact
      Or.inr
        (Or.inr
          (Or.inl rfl))

  have hEbase :
      HilbertIncidence.OnLine E base :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      A D E
      base
      hAD
      hAbase
      hDbase).mp hEinAD

  exact
    ⟨base,
      hAbase,
      hDbase,
      hEbase⟩

/--
Moving the first side of a right angle along the same ray preserves
the right angle.
-/
theorem proposition39_test_right_angle_sameRay_first
    [HilbertCongruence Geo]
    (A A' F X : Geo.Point)
    (hAFX : Not (PrimCollinear Geo A F X))
    (hRight : HilbertRightAngle Geo A F X)
    (hRay : HilbertSameRay Geo F A A') :
    HilbertRightAngle Geo A' F X := by

  --------------------------------------------------------------------
  -- Swap the two arms:
  --
  --     RightAngle A F X
  --
  -- becomes
  --
  --     RightAngle X F A.
  --------------------------------------------------------------------

  have hXFA :
      Not (PrimCollinear Geo X F A) := by
    intro h

    exact
      hAFX
        (PrimCollinearSymm
          Geo X F A h)

  have hRightSwap :
      HilbertRightAngle Geo X F A :=
    proposition39_test_right_angle_swap
      Geo
      A F X
      hAFX
      hRight

  --------------------------------------------------------------------
  -- Now A and A' are on the same ray from F, so use the already
  -- established transport for the second arm.
  --------------------------------------------------------------------

  have hTransport :=
    proposition39_test_right_angle_sameRay_second
      Geo
      X F A A'
      hXFA
      hRightSwap
      hRay

  have hXFA' :
      Not (PrimCollinear Geo X F A') :=
    hTransport.1

  have hRightSwap' :
      HilbertRightAngle Geo X F A' :=
    hTransport.2

  --------------------------------------------------------------------
  -- Swap the arms back.
  --------------------------------------------------------------------

  exact
    proposition39_test_right_angle_swap
      Geo
      X F A'
      hXFA'
      hRightSwap'

/--
If D and E lie on the same carrier through A, a right angle with
second arm AE can be transferred to the second arm AD.
-/
theorem proposition39_test_right_angle_collinear_second
    [HilbertCongruence Geo]
    (N A D E : Geo.Point)
    (hAD : A ≠ D)
    (hAE : A ≠ E)
    (hADE : PrimCollinear Geo A D E)
    (hNAE : Not (PrimCollinear Geo N A E))
    (hRightE : HilbertRightAngle Geo N A E) :
    HilbertRightAngle Geo N A D := by

  by_cases hDE : D = E

  --------------------------------------------------------------------
  -- Degenerate comparison: D = E.
  --------------------------------------------------------------------

  · subst E
    exact hRightE

  --------------------------------------------------------------------
  -- D and E are distinct.
  --------------------------------------------------------------------

  · have hAED :
        PrimCollinear Geo A E D :=
      PrimCollinearRotate
        Geo A D E hADE

    rcases
        hilbert_between_trichotomy
          Geo
          A E D
          hAE
          (Ne.symm hDE)
          hAD
          hAED
      with
      hAEDbet | hEADbet | hADEbet

    ------------------------------------------------------------------
    -- A-E-D: E and D lie on the same ray from A.
    ------------------------------------------------------------------

    · have hRay :
          HilbertSameRay Geo A E D :=
        hilbert_sameRay_of_between
          Geo A E D hAEDbet

      exact
        (proposition39_test_right_angle_sameRay_second
          Geo
          N A E D
          hNAE
          hRightE
          hRay).2

    ------------------------------------------------------------------
    -- E-A-D: E and D lie on opposite rays from A.
    ------------------------------------------------------------------

    · have hEAN :
          Not (PrimCollinear Geo E A N) := by
        intro h

        exact
          hNAE
            (PrimCollinearSymm
              Geo E A N h)

      have hRightEAN :
          HilbertRightAngle Geo E A N :=
        proposition39_test_right_angle_swap
          Geo
          N A E
          hNAE
          hRightE

      have hRightDAN :
          HilbertRightAngle Geo D A N :=
        proposition39_test_right_angle_opposite_base
          Geo
          E D A N
          hEADbet
          hEAN
          hRightEAN

      have hEADcol :
          PrimCollinear Geo E A D :=
        (HilbertOrder.between_incidence
          E A D hEADbet).2.2.2.1

      have hDAN :
          Not (PrimCollinear Geo D A N) := by
        intro h

        have hADN :
            PrimCollinear Geo A D N :=
          PrimCollinearSwap
            Geo D A N h

        have hEANcol :
            PrimCollinear Geo E A N :=
          hilbert_primCollinear_trans
            Geo
            E A D N
            hAD
            hEADcol
            hADN

        exact hEAN hEANcol

      exact
        proposition39_test_right_angle_swap
          Geo
          D A N
          hDAN
          hRightDAN

    ------------------------------------------------------------------
    -- A-D-E: again E and D lie on the same ray from A.
    ------------------------------------------------------------------

    · have hRayDE :
          HilbertSameRay Geo A D E :=
        hilbert_sameRay_of_between
          Geo A D E hADEbet

      have hRayED :
          HilbertSameRay Geo A E D :=
        hilbert_sameRay_symm
          Geo A D E hRayDE

      exact
        (proposition39_test_right_angle_sameRay_second
          Geo
          N A E D
          hNAE
          hRightE
          hRayED).2

/--
Two perpendicular directions through the same foot to the same base
are collinear with that foot.
-/
theorem proposition39_test_two_perpendiculars_same_foot_collinear
    [HilbertEuclideanPlane Geo]
    (M N A D : Geo.Point)
    (base : Geo.Line)
    (hAD : A ≠ D)
    (hAbase : HilbertIncidence.OnLine A base)
    (hDbase : HilbertIncidence.OnLine D base)
    (hMAD : Not (PrimCollinear Geo M A D))
    (hNAD : Not (PrimCollinear Geo N A D))
    (hRightM : HilbertRightAngle Geo M A D)
    (hRightN : HilbertRightAngle Geo N A D) :
    PrimCollinear Geo M A N := by

  --------------------------------------------------------------------
  -- M and N are off the common base AD.
  --------------------------------------------------------------------

  have hMoff :
      Not (HilbertIncidence.OnLine M base) := by
    intro hMbase
    exact
      hMAD
        ⟨base,
          hMbase,
          hAbase,
          hDbase⟩

  have hNoff :
      Not (HilbertIncidence.OnLine N base) := by
    intro hNbase
    exact
      hNAD
        ⟨base,
          hNbase,
          hAbase,
          hDbase⟩

  --------------------------------------------------------------------
  -- Normalize both right angles so that the fixed base ray is AD.
  --------------------------------------------------------------------

  have hDAM :
      Not (PrimCollinear Geo D A M) := by
    intro h
    exact
      hMAD
        (PrimCollinearSymm
          Geo D A M h)

  have hDAN :
      Not (PrimCollinear Geo D A N) := by
    intro h
    exact
      hNAD
        (PrimCollinearSymm
          Geo D A N h)

  have hRightDAM :
      HilbertRightAngle Geo D A M :=
    proposition39_test_right_angle_swap
      Geo
      M A D
      hMAD
      hRightM

  have hRightDAN :
      HilbertRightAngle Geo D A N :=
    proposition39_test_right_angle_swap
      Geo
      N A D
      hNAD
      hRightN

  --------------------------------------------------------------------
  -- First case: M and N lie on the same side of AD.
  --------------------------------------------------------------------

  by_cases hSameMN :
      HilbertSameSide Geo M N base

  · have hRayMN :
        HilbertSameRay Geo A M N :=
      proposition39_test_same_foot_perpendicular_same_ray
        Geo
        D A M N
        base
        hAD.symm
        hDbase
        hAbase
        hMoff
        hSameMN
        hDAM
        hDAN
        hRightDAM
        hRightDAN

    exact
      PrimCollinearSwap
        Geo A M N
        hRayMN.2.2.1

  --------------------------------------------------------------------
  -- Second case: M and N lie on opposite sides of AD.
  --------------------------------------------------------------------

  · have hOppMN :
        HilbertOppositeSide Geo M N base :=
      hilbert_oppositeSide_of_not_sameSide
        Geo
        M N
        base
        hMoff
        hNoff
        hSameMN

    ------------------------------------------------------------------
    -- Assume M,A,N were noncollinear.
    ------------------------------------------------------------------

    by_contra hMAN

    ------------------------------------------------------------------
    -- The definition of the right angle at A supplies C with
    --
    --     M-A-C.
    ------------------------------------------------------------------

    have hRightM0 := hRightM

    rcases hRightM with
      ⟨C, hMAC, _hAngleM⟩

    have hMACData :=
      HilbertOrder.between_incidence
        M A C hMAC

    have hAC :
        A ≠ C :=
      hMACData.2.1

    have hMACcol :
        PrimCollinear Geo M A C :=
      hMACData.2.2.2.1

    ------------------------------------------------------------------
    -- Since M and N are opposite across AD and M-A-C,
    -- the opposite extension C lies on the same side as N.
    ------------------------------------------------------------------

    have hSameNC :
        HilbertSameSide Geo N C base :=
      hilbert_sameSide_after_opposite_extension
        Geo
        M A N C
        base
        hAbase
        hMAN
        hMAC
        hOppMN

    have hSameCN :
        HilbertSameSide Geo C N base :=
      hilbert_sameSide_symm
        Geo N C base hSameNC

    ------------------------------------------------------------------
    -- Reversing M through A preserves the right angle.
    ------------------------------------------------------------------

    have hRightCAD :
        HilbertRightAngle Geo C A D :=
      proposition39_test_right_angle_opposite_base
        Geo
        M C A D
        hMAC
        hMAD
        hRightM0

    have hADC :
        Not (PrimCollinear Geo A D C) :=
      hilbert_not_collinear_of_off_line
        Geo
        A D C
        base
        hAD
        hAbase
        hDbase
        hSameCN.1

    have hCAD :
        Not (PrimCollinear Geo C A D) := by
      intro h
      exact
        hADC
          (PrimCollinearCycle
            Geo C A D h)

    have hDAC :
        Not (PrimCollinear Geo D A C) := by
      intro h
      exact
        hCAD
          (PrimCollinearSymm
            Geo D A C h)

    have hRightDAC :
        HilbertRightAngle Geo D A C :=
      proposition39_test_right_angle_swap
        Geo
        C A D
        hCAD
        hRightCAD

    ------------------------------------------------------------------
    -- C and N are now two perpendicular rays from the same foot,
    -- on the same side of AD.
    ------------------------------------------------------------------

    have hRayCN :
        HilbertSameRay Geo A C N :=
      proposition39_test_same_foot_perpendicular_same_ray
        Geo
        D A C N
        base
        hAD.symm
        hDbase
        hAbase
        hSameCN.1
        hSameCN
        hDAC
        hDAN
        hRightDAC
        hRightDAN

    have hACN :
        PrimCollinear Geo A C N :=
      hRayCN.2.2.1

    ------------------------------------------------------------------
    -- M-A-C and A-C-N force M-A-N.
    ------------------------------------------------------------------

    have hMANcol :
        PrimCollinear Geo M A N :=
      hilbert_primCollinear_trans
        Geo
        M A C N
        hAC
        hMACcol
        hACN

    exact hMAN hMANcol

/--
The perpendicular bisectors of AB and AC meet when ABC is
noncollinear.
-/
theorem proposition39_test_perpendicular_bisectors_meet
    [HilbertEuclideanPlane Geo]
    (A B C M X N Y : Geo.Point)
    (perpAB perpAC : Geo.Line)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAMB : Geo.Between A M B)
    (_hAM_MB : Geo.Congruent A M M B)
    (hMperpAB : HilbertIncidence.OnLine M perpAB)
    (hXperpAB : HilbertIncidence.OnLine X perpAB)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRightAB : HilbertRightAngle Geo A M X)
    (hANC : Geo.Between A N C)
    (_hAN_NC : Geo.Congruent A N N C)
    (hNperpAC : HilbertIncidence.OnLine N perpAC)
    (hYperpAC : HilbertIncidence.OnLine Y perpAC)
    (hANY : Not (PrimCollinear Geo A N Y))
    (hRightAC : HilbertRightAngle Geo A N Y) :
    ∃ O : Geo.Point,
      HilbertIncidence.OnLine O perpAB ∧
      HilbertIncidence.OnLine O perpAC := by

  --------------------------------------------------------------------
  -- Assume the two perpendicular bisectors do not meet.
  --------------------------------------------------------------------

  by_contra hNoMeet

  have hDisjoint :
      HilbertLinesDisjoint Geo perpAB perpAC := by
    intro hMeet
    rcases hMeet with
      ⟨O, hOperpAB, hOperpAC⟩

    exact
      hNoMeet
        ⟨O, hOperpAB, hOperpAC⟩

  --------------------------------------------------------------------
  -- Hence their point-pair carriers MX and NY are parallel.
  --------------------------------------------------------------------

  have hMX_NY :
      Geo.Parallel M X N Y :=
    proposition39_test_bisector_lines_parallel_of_disjoint
      Geo
      A M X N Y
      perpAB perpAC
      hMperpAB
      hXperpAB
      hAMX
      hNperpAC
      hYperpAC
      hANY
      hDisjoint

  --------------------------------------------------------------------
  -- Through A construct a line AD parallel to MX.
  --------------------------------------------------------------------

  rcases
      proposition39_test_perpendicular_parallel_through_endpoint
        Geo
        A B M X
        hAMB
        hAMX
        hRightAB
    with
    ⟨D,
      hRightMAD,
      hMX_AD⟩

  --------------------------------------------------------------------
  -- Through A construct a line AE parallel to NY.
  --------------------------------------------------------------------

  rcases
      proposition39_test_perpendicular_parallel_through_endpoint
        Geo
        A C N Y
        hANC
        hANY
        hRightAC
    with
    ⟨E,
      hRightNAE,
      hNY_AE⟩

  have hAD :
      A ≠ D :=
    hMX_AD.2.1

  have hAE :
      A ≠ E :=
    hNY_AE.2.1

  --------------------------------------------------------------------
  -- Since MX || NY and MX || AD, also AD || NY.
  --------------------------------------------------------------------

  have hAD_NY :
      Geo.Parallel A D N Y :=
    proposition39_test_endpoint_parallel_to_second_bisector
      Geo
      A D M X N Y
      perpAC
      hNperpAC
      hYperpAC
      hANY
      hMX_NY
      hMX_AD

  --------------------------------------------------------------------
  -- AD and AE are both parallels through A to NY, so they have the
  -- same carrier.
  --------------------------------------------------------------------

  have hCarrier :
      Geo.PointLine A D =
      Geo.PointLine A E :=
    proposition39_test_endpoint_parallels_same_carrier
      Geo
      A D E M X N Y
      perpAC
      hNperpAC
      hYperpAC
      hANY
      hMX_NY
      hMX_AD
      hNY_AE

  --------------------------------------------------------------------
  -- Recover an actual Hilbert line carrying A, D and E.
  --------------------------------------------------------------------

  rcases
      proposition39_test_common_carrier_line
        Geo
        A D E
        hAD
        hCarrier
    with
    ⟨base,
      hAbase,
      hDbase,
      hEbase⟩

  have hADE :
      PrimCollinear Geo A D E :=
    ⟨base,
      hAbase,
      hDbase,
      hEbase⟩

  --------------------------------------------------------------------
  -- M is off AD because MX || AD.
  --------------------------------------------------------------------

  have hMX :
      M ≠ X :=
    hMX_AD.1

  have hMoff :
      Not (HilbertIncidence.OnLine M base) := by

    intro hMbase

    have hMinMX :
        (Geo.PointLine M X) M :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        M X M
        perpAB
        hMX
        hMperpAB
        hXperpAB).mpr
        hMperpAB

    have hMinAD :
        (Geo.PointLine A D) M :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A D M
        base
        hAD
        hAbase
        hDbase).mpr
        hMbase

    exact
      Set.disjoint_left.mp
        hMX_AD.2.2
        hMinMX
        hMinAD

  --------------------------------------------------------------------
  -- N is off AD because AD || NY.
  --------------------------------------------------------------------

  have hNY :
      N ≠ Y :=
    hAD_NY.2.1

  have hNoff :
      Not (HilbertIncidence.OnLine N base) := by

    intro hNbase

    have hNinAD :
        (Geo.PointLine A D) N :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        A D N
        base
        hAD
        hAbase
        hDbase).mpr
        hNbase

    have hNinNY :
        (Geo.PointLine N Y) N :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        N Y N
        perpAC
        hNY
        hNperpAC
        hYperpAC).mpr
        hNperpAC

    exact
      Set.disjoint_left.mp
        hAD_NY.2.2
        hNinAD
        hNinNY

  --------------------------------------------------------------------
  -- Required noncollinearities at A.
  --------------------------------------------------------------------

  have hADM :
      Not (PrimCollinear Geo A D M) :=
    hilbert_not_collinear_of_off_line
      Geo
      A D M
      base
      hAD
      hAbase
      hDbase
      hMoff

  have hMAD :
      Not (PrimCollinear Geo M A D) := by
    intro h

    exact
      hADM
        (PrimCollinearCycle
          Geo M A D h)

  have hADN :
      Not (PrimCollinear Geo A D N) :=
    hilbert_not_collinear_of_off_line
      Geo
      A D N
      base
      hAD
      hAbase
      hDbase
      hNoff

  have hNAD :
      Not (PrimCollinear Geo N A D) := by
    intro h

    exact
      hADN
        (PrimCollinearCycle
          Geo N A D h)

  have hAEN :
      Not (PrimCollinear Geo A E N) :=
    hilbert_not_collinear_of_off_line
      Geo
      A E N
      base
      hAE
      hAbase
      hEbase
      hNoff

  have hNAE :
      Not (PrimCollinear Geo N A E) := by
    intro h

    exact
      hAEN
        (PrimCollinearCycle
          Geo N A E h)

  --------------------------------------------------------------------
  -- Transport the second right angle from AE to AD.
  --------------------------------------------------------------------

  have hRightNAD :
      HilbertRightAngle Geo N A D :=
    proposition39_test_right_angle_collinear_second
      Geo
      N A D E
      hAD
      hAE
      hADE
      hNAE
      hRightNAE

  --------------------------------------------------------------------
  -- Thus M and N are two perpendicular directions erected at A to
  -- the same base AD.  They must be collinear with A.
  --------------------------------------------------------------------

  have hMAN :
      PrimCollinear Geo M A N :=
    proposition39_test_two_perpendiculars_same_foot_collinear
      Geo
      M N A D
      base
      hAD
      hAbase
      hDbase
      hMAD
      hNAD
      hRightMAD
      hRightNAD

  --------------------------------------------------------------------
  -- But M lies on AB and N lies on AC.  Therefore ABC would be
  -- collinear.
  --------------------------------------------------------------------

  have hAMBData :=
    HilbertOrder.between_incidence
      A M B hAMB

  have hANCData :=
    HilbertOrder.between_incidence
      A N C hANC

  have hAM :
      A ≠ M :=
    hAMBData.1

  have hAN :
      A ≠ N :=
    hANCData.1

  have hAMBcol :
      PrimCollinear Geo A M B :=
    hAMBData.2.2.2.1

  have hANCcol :
      PrimCollinear Geo A N C :=
    hANCData.2.2.2.1

  have hBAM :
      PrimCollinear Geo B A M :=
    PrimCollinearCycle
      Geo
      M B A
      (PrimCollinearCycle
        Geo A M B hAMBcol)

  have hAMN :
      PrimCollinear Geo A M N :=
    PrimCollinearCycle
      Geo
      N A M
      (PrimCollinearSymm
        Geo M A N hMAN)

  have hBAN :
      PrimCollinear Geo B A N :=
    hilbert_primCollinear_trans
      Geo
      B A M N
      hAM
      hBAM
      hAMN

  have hBAC :
      PrimCollinear Geo B A C :=
    hilbert_primCollinear_trans
      Geo
      B A N C
      hAN
      hBAN
      hANCcol

  have hABCcol :
      PrimCollinear Geo A B C :=
    PrimCollinearSwap
      Geo B A C hBAC

  exact
    hABC hABCcol


------------------------------------------------------------------------
-- Circumcenter from two perpendicular bisectors
------------------------------------------------------------------------

/--
A noncollinear triangle has a point O equidistant from its three
vertices, provided the two constructed perpendicular bisectors meet.

The equidistance statements themselves follow from the previously
proved perpendicular-bisector theorem.
-/
theorem proposition39_test_circumcenter_exists
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    ∃ O : Geo.Point,
      Geo.Congruent O A O B ∧
      Geo.Congruent O A O C := by

  --------------------------------------------------------------------
  -- Construct perpendicular bisectors of AB and AC.
  --------------------------------------------------------------------

  rcases
      proposition39_test_two_perpendicular_bisectors_exist
        Geo
        A B C
        hABC
    with
    ⟨M, X, perpAB,
      N, Y, perpAC,
      hAMB,
      hAM_MB,
      hMperpAB,
      hXperpAB,
      hAMX,
      hRightAB,
      hANC,
      hAN_NC,
      hNperpAC,
      hYperpAC,
      hANY,
      hRightAC⟩

  --------------------------------------------------------------------
  -- Their common point.
  --------------------------------------------------------------------

  rcases
      proposition39_test_perpendicular_bisectors_meet
        Geo
        A B C
        M X N Y
        perpAB perpAC
        hABC
        hAMB
        hAM_MB
        hMperpAB
        hXperpAB
        hAMX
        hRightAB
        hANC
        hAN_NC
        hNperpAC
        hYperpAC
        hANY
        hRightAC
    with
    ⟨O, hOperpAB, hOperpAC⟩

  --------------------------------------------------------------------
  -- O lies on the perpendicular bisector of AB.
  --------------------------------------------------------------------

  have hAO_BO :
      Geo.Congruent A O B O :=
    proposition39_test_perpendicular_bisector_equidistant
      Geo
      A M B X O
      perpAB
      hAMB
      hAM_MB
      hMperpAB
      hXperpAB
      hOperpAB
      hAMX
      hRightAB

  have hOA_BO :
      Geo.Congruent O A B O :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      A O
      B O).mp hAO_BO

  have hOA_OB :
      Geo.Congruent O A O B :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      O A
      B O).mp hOA_BO

  --------------------------------------------------------------------
  -- O lies on the perpendicular bisector of AC.
  --------------------------------------------------------------------

  have hAO_CO :
      Geo.Congruent A O C O :=
    proposition39_test_perpendicular_bisector_equidistant
      Geo
      A N C Y O
      perpAC
      hANC
      hAN_NC
      hNperpAC
      hYperpAC
      hOperpAC
      hANY
      hRightAC

  have hOA_CO :
      Geo.Congruent O A C O :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      A O
      C O).mp hAO_CO

  have hOA_OC :
      Geo.Congruent O A O C :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      O A
      C O).mp hOA_CO

  exact
    ⟨O,
      hOA_OB,
      hOA_OC⟩

------------------------------------------------------------------------
-- Circumcircle of a noncollinear triangle
------------------------------------------------------------------------

/--
A noncollinear triangle lies on a common Hilbert circle.

The center is the intersection point of the two perpendicular
bisectors constructed above.  The reference radius is OA.
-/
theorem proposition39_test_circumcircle_exists
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    ∃ O : Geo.Point,
      HilbertCircle Geo O A A ∧
      HilbertCircle Geo O A B ∧
      HilbertCircle Geo O A C := by

  rcases
      proposition39_test_circumcenter_exists
        Geo
        A B C
        hABC
    with
    ⟨O, hOA_OB, hOA_OC⟩

  have hOA_OA :
      Geo.Congruent O A O A :=
    hilbert_congruent_reflexive
      Geo O A

  have hOB_OA :
      Geo.Congruent O B O A :=
    CongruentSymmetry
      Geo
      O A
      O B
      hOA_OB

  have hOC_OA :
      Geo.Congruent O C O A :=
    CongruentSymmetry
      Geo
      O A
      O C
      hOA_OC

  exact
    ⟨O,
      hOA_OA,
      hOB_OA,
      hOC_OA⟩



------------------------------------------------------------------------
-- Temporary circle theorem used in Hilbert sec. 14
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Hilbert sec. 7
-- Circle theorem: converse in the crossing-chord configuration
------------------------------------------------------------------------
theorem proposition39_test_first_secant_noncollinear
    [HilbertOrder Geo]
    (O A C B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    Not (PrimCollinear Geo A C B) := by

  intro hACB

  have hOAC :
      PrimCollinear Geo O A C :=
    hRayAC.2.2.1

  have hOAB :
      PrimCollinear Geo O A B :=
    hilbert_primCollinear_trans
      Geo
      O A C B
      hAC
      hOAC
      hACB

  have hABO :
      PrimCollinear Geo A B O :=
    PrimCollinearCycle
      Geo O A B hOAB

  have hAOB' :
      PrimCollinear Geo A O B :=
    PrimCollinearRotate
      Geo A B O hABO

  exact hAOB hAOB'


theorem proposition39_test_second_secant_noncollinear
    [HilbertOrder Geo]
    (O A B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayBD : HilbertSameRay Geo O B D)
    (hBD : B ≠ D) :
    Not (PrimCollinear Geo A D B) := by

  intro hADB

  have hOBD :
      PrimCollinear Geo O B D :=
    hRayBD.2.2.1

  have hBDO :
      PrimCollinear Geo B D O :=
    PrimCollinearCycle
      Geo O B D hOBD

  have hABD :
      PrimCollinear Geo A B D :=
    PrimCollinearRotate
      Geo A D B hADB

  have hABO :
      PrimCollinear Geo A B O :=
    hilbert_primCollinear_trans
      Geo
      A B D O
      hBD
      hABD
      hBDO

  have hAOB' :
      PrimCollinear Geo A O B :=
    PrimCollinearRotate
      Geo A B O hABO

  exact hAOB hAOB'

theorem proposition39_test_circle_crossing_chords_concyclic_degenerate
    [HilbertEuclideanPlane Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hDeg : A = C ∨ B = D) :
    HilbertConcyclic4 Geo A C D B := by

  rcases hDeg with hACeq | hBDeq

  --------------------------------------------------------------------
  -- A = C
  --------------------------------------------------------------------

  · subst C

    by_cases hBD : B = D

    --------------------------------------------------------------
    -- A = C and B = D.
    -- Use the circumcircle of the genuine triangle AOB.
    --------------------------------------------------------------

    · subst D

      rcases
          proposition39_test_circumcircle_exists
            Geo
            A O B
            hAOB
        with
        ⟨K, hA, hO, hB⟩

      exact
        hilbert_concyclic4_of_circle
          Geo
          K A
          A A B B
          hA
          hA
          hB
          hB

    --------------------------------------------------------------
    -- A = C, but B != D.
    -- The triangle ADB is noncollinear.
    --------------------------------------------------------------

    · have hADB :
          Not (PrimCollinear Geo A D B) :=
        proposition39_test_second_secant_noncollinear
          Geo
          O A B D
          hAOB
          hRayBD
          hBD

      rcases
          proposition39_test_circumcircle_exists
            Geo
            A D B
            hADB
        with
        ⟨K, hA, hD, hB⟩

      exact
        hilbert_concyclic4_of_circle
          Geo
          K A
          A A D B
          hA
          hA
          hD
          hB

  --------------------------------------------------------------------
  -- B = D
  --------------------------------------------------------------------

  · subst D

    by_cases hAC : A = C

    --------------------------------------------------------------
    -- Again A = C and B = D.
    --------------------------------------------------------------

    · subst C

      rcases
          proposition39_test_circumcircle_exists
            Geo
            A O B
            hAOB
        with
        ⟨K, hA, hO, hB⟩

      exact
        hilbert_concyclic4_of_circle
          Geo
          K A
          A A B B
          hA
          hA
          hB
          hB

    --------------------------------------------------------------
    -- B = D, but A != C.
    -- The triangle ACB is noncollinear.
    --------------------------------------------------------------

    · have hACB :
          Not (PrimCollinear Geo A C B) :=
        proposition39_test_first_secant_noncollinear
          Geo
          O A C B
          hAOB
          hRayAC
          hAC

      rcases
          proposition39_test_circumcircle_exists
            Geo
            A C B
            hACB
        with
        ⟨K, hA, hC, hB⟩

      exact
        hilbert_concyclic4_of_circle
          Geo
          K A
          A C B B
          hA
          hC
          hB
          hB

theorem proposition39_test_circle_crossing_chords_nondegenerate_data
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D) :
    Not (PrimCollinear Geo O A D) ∧
    Not (PrimCollinear Geo O B C) ∧
    (Geo.Between O A C ∨ Geo.Between O C A) ∧
    (Geo.Between O B D ∨ Geo.Between O D B) := by

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAC.1

  have hRayBB :
      HilbertSameRay Geo O B B :=
    hilbert_sameRay_refl
      Geo O B hRayBD.1

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  have hOAD :
      Not (PrimCollinear Geo O A D) := by
    intro h
    exact
      hAOD
        (PrimCollinearSwap
          Geo O A D h)

  have hCOB :
      Not (PrimCollinear Geo C O B) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C B
      hAOB
      hRayAC
      hRayBB

  have hOBC :
      Not (PrimCollinear Geo O B C) := by
    intro h
    exact
      hCOB
        (PrimCollinearRotate
          Geo
          C B O
          (PrimCollinearSymm
            Geo O B C h))

  have hOrderAC :
      Geo.Between O A C ∨
      Geo.Between O C A := by

    rcases
        hilbert_sameRay_cases
          Geo O A C hRayAC
      with hEq | hOAC | hOCA

    · exact False.elim (hAC hEq)

    · exact Or.inl hOAC

    · exact Or.inr hOCA

  have hOrderBD :
      Geo.Between O B D ∨
      Geo.Between O D B := by

    rcases
        hilbert_sameRay_cases
          Geo O B D hRayBD
      with hEq | hOBD | hODB

    · exact False.elim (hBD hEq)

    · exact Or.inl hOBD

    · exact Or.inr hODB

  exact
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩


theorem proposition39_test_circle_crossing_chords_angle_at_O
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D) :
    Geo.AngleCongruent
      A O D
      B O C := by

  have hAOB_AOD :
      Geo.Angle A O B =
      Geo.Angle A O D :=
    hilbert_angle_eq_of_sameRay_second
      Geo O A B D hRayBD

  have hBOA_BOC :
      Geo.Angle B O A =
      Geo.Angle B O C :=
    hilbert_angle_eq_of_sameRay_second
      Geo O B A C hRayAC

  have hAOB_BOA :
      Geo.AngleCongruent
        A O B
        B O A :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      A O B).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo A O B)

  unfold Geometry.Geo.AngleCongruent at hAOB_BOA ⊢

  rw [← hAOB_AOD, ← hBOA_BOC]

  exact hAOB_BOA

theorem proposition39_test_circle_outer_outer_angles
    [HilbertCongruence Geo]
    (O A C B D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hOBC : Not (PrimCollinear Geo O B C))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
      C A D
      C B D := by

  --------------------------------------------------------------------
  -- A != D.
  --------------------------------------------------------------------

  have hADO :
      Not (PrimCollinear Geo A D O) := by

    intro h

    have hDOA :
        PrimCollinear Geo D O A :=
      PrimCollinearCycle
        Geo A D O h

    have hOAD' :
        PrimCollinear Geo O A D :=
      PrimCollinearCycle
        Geo D O A hDOA

    exact hOAD hOAD'

  have hAD :
      A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D O hADO

  --------------------------------------------------------------------
  -- B != C.
  --------------------------------------------------------------------

  have hBCO :
      Not (PrimCollinear Geo B C O) := by

    intro h

    have hCOB :
        PrimCollinear Geo C O B :=
      PrimCollinearCycle
        Geo B C O h

    have hOBC' :
        PrimCollinear Geo O B C :=
      PrimCollinearCycle
        Geo C O B hCOB

    exact hOBC hOBC'

  have hBC :
      B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C O hBCO

  --------------------------------------------------------------------
  -- Since O-A-C, angle DAC is supplementary to OAD.
  --------------------------------------------------------------------

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSuppA :
      BookZeroSupplement Geo
        O A D
        D C :=
    ⟨hRayADD, hOAC⟩

  --------------------------------------------------------------------
  -- Since O-B-D, angle CBD is supplementary to OBC.
  --------------------------------------------------------------------

  have hRayBCC :
      HilbertSameRay Geo B C C :=
    hilbert_sameRay_refl
      Geo B C hBC.symm

  have hSuppB :
      BookZeroSupplement Geo
        O B C
        C D :=
    ⟨hRayBCC, hOBD⟩

  --------------------------------------------------------------------
  -- Supplements of congruent angles are congruent.
  --------------------------------------------------------------------

  have hDAC_CBD :
      Geo.AngleCongruent
        D A C
        C B D :=
    bookZero_43_supplements
      Geo
      O A D
      D C
      O B C
      C D
      hAngle
      hSuppA
      hSuppB
      hOAD
      hOBC

  --------------------------------------------------------------------
  -- Reverse the first angle: DAC = CAD.
  --------------------------------------------------------------------

  exact
    (Geo.angle_congruent_reverse_first
      D A C
      C B D).mp
      hDAC_CBD

theorem proposition39_test_circle_inner_inner_angles
    [HilbertCongruence Geo]
    (O A C B D : Geo.Point)
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
      C A D
      C B D := by

  have hACO :
      Geo.Between A C O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.2.2

  have hBDO :
      Geo.Between B D O :=
    (HilbertOrder.between_incidence
      O D B hODB).2.2.2.2

  have hRayACO :
      HilbertSameRay Geo A C O :=
    hilbert_sameRay_of_between
      Geo A C O hACO

  have hRayAOC :
      HilbertSameRay Geo A O C :=
    hilbert_sameRay_symm
      Geo A C O hRayACO

  have hRayBDO :
      HilbertSameRay Geo B D O :=
    hilbert_sameRay_of_between
      Geo B D O hBDO

  have hRayBOD :
      HilbertSameRay Geo B O D :=
    hilbert_sameRay_symm
      Geo B D O hRayBDO

  have hLeft :
      Geo.Angle O A D =
      Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A O C D hRayAOC

  have hRight :
      Geo.Angle O B C =
      Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B O D C hRayBOD

  have hCAD_DBC :
      Geo.AngleCongruent
        C A D
        D B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hLeft, ← hRight]

    exact hAngle

  exact
    (Geo.angle_congruent_reverse_second
      C A D
      D B C).mp
      hCAD_DBC

theorem proposition39_test_circle_mixed_outer_inner_angle_data
    [HilbertCongruence Geo]
    (O A C B D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    BookZeroSupplement Geo
        O A D
        D C
    ∧
    Geo.AngleCongruent
        O A D
        C B D := by

  have hADO :
      Not (PrimCollinear Geo A D O) := by
    intro h
    exact
      hOAD
        (PrimCollinearRotate
          Geo
          O D A
          (PrimCollinearSymm
            Geo A D O h))

  have hAD :
      A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D O hADO

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSuppA :
      BookZeroSupplement Geo
        O A D
        D C :=
    ⟨hRayADD, hOAC⟩

  have hBDO :
      Geo.Between B D O :=
    (HilbertOrder.between_incidence
      O D B hODB).2.2.2.2

  have hRayBDO :
      HilbertSameRay Geo B D O :=
    hilbert_sameRay_of_between
      Geo B D O hBDO

  have hRayBOD :
      HilbertSameRay Geo B O D :=
    hilbert_sameRay_symm
      Geo B D O hRayBDO

  have hRight :
      Geo.Angle O B C =
      Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B O D C hRayBOD

  have hOAD_DBC :
      Geo.AngleCongruent
        O A D
        D B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hRight]

    exact hAngle

  have hOAD_CBD :
      Geo.AngleCongruent
        O A D
        C B D :=
    (Geo.angle_congruent_reverse_second
      O A D
      D B C).mp
      hOAD_DBC

  exact
    ⟨hSuppA, hOAD_CBD⟩

theorem proposition39_test_circle_mixed_inner_outer_angle_data
    [HilbertCongruence Geo]
    (O A C B D : Geo.Point)
    (hOBC : Not (PrimCollinear Geo O B C))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
        C A D
        O B C
    ∧
    BookZeroSupplement Geo
        O B C
        C D := by

  --------------------------------------------------------------------
  -- Transport OAD to CAD, since O-C-A.
  --------------------------------------------------------------------

  have hACO :
      Geo.Between A C O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.2.2

  have hRayACO :
      HilbertSameRay Geo A C O :=
    hilbert_sameRay_of_between
      Geo A C O hACO

  have hRayAOC :
      HilbertSameRay Geo A O C :=
    hilbert_sameRay_symm
      Geo A C O hRayACO

  have hLeft :
      Geo.Angle O A D =
      Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A O C D hRayAOC

  have hCAD_OBC :
      Geo.AngleCongruent
        C A D
        O B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hLeft]

    exact hAngle

  --------------------------------------------------------------------
  -- Since O-B-D, CBD is supplementary to OBC.
  --------------------------------------------------------------------

  have hBCO :
      Not (PrimCollinear Geo B C O) := by
    intro h

    have hCOB :
        PrimCollinear Geo C O B :=
      PrimCollinearCycle
        Geo B C O h

    have hOBC' :
        PrimCollinear Geo O B C :=
      PrimCollinearCycle
        Geo C O B hCOB

    exact hOBC hOBC'

  have hBC :
      B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C O hBCO

  have hRayBCC :
      HilbertSameRay Geo B C C :=
    hilbert_sameRay_refl
      Geo B C hBC.symm

  have hSuppB :
      BookZeroSupplement Geo
        O B C
        C D :=
    ⟨hRayBCC, hOBD⟩

  exact
    ⟨hCAD_OBC, hSuppB⟩

theorem proposition39_test_equal_angles_same_secant_unique
    [HilbertCongruence Geo]
    (O B B' C : Geo.Point)
    (hOBC : Not (PrimCollinear Geo O B C))
    (hRay :
      HilbertSameRay Geo O B B')
    (hAngle :
      Geo.AngleCongruent
        O B C
        O B' C) :
    B = B' := by

  rcases
      hilbert_sameRay_cases
        Geo O B B' hRay
    with
    hEq | hOBB' | hOB'B

  --------------------------------------------------------------------
  -- B = B'.
  --------------------------------------------------------------------

  · exact hEq

  --------------------------------------------------------------------
  -- O-B-B'.
  --
  -- Then O is on the extension of B'B beyond B.
  -- Thus CBO is an exterior angle of triangle B B' C,
  -- while BB'C is the remote interior angle.
  --------------------------------------------------------------------

  · have hOBB'Data :=
      HilbertOrder.between_incidence
        O B B' hOBB'

    have hBB' :
        B ≠ B' :=
      hOBB'Data.2.1

    have hOBB'col :
        PrimCollinear Geo O B B' :=
      hOBB'Data.2.2.2.1

    have hBB'C :
        Not (PrimCollinear Geo B B' C) := by

      intro hBB'C

      have hOBC' :
          PrimCollinear Geo O B C :=
        hilbert_primCollinear_trans
          Geo
          O B B' C
          hBB'
          hOBB'col
          hBB'C

      exact hOBC hOBC'

    have hB'BO :
        Geo.Between B' B O :=
      hOBB'Data.2.2.2.2

    have hRayB'BO :
        HilbertSameRay Geo B' B O :=
      hilbert_sameRay_of_between
        Geo B' B O hB'BO

    have hAtB' :
        Geo.Angle B B' C =
        Geo.Angle O B' C :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        B' B O C
        hRayB'BO

    have hCBO_OB'C :
        Geo.AngleCongruent
          C B O
          O B' C :=
      (Geo.angle_congruent_reverse_first
        O B C
        O B' C).mp
        hAngle

    have hExterior :
        Geo.AngleCongruent
          C B O
          B B' C := by

      unfold Geometry.Geo.AngleCongruent
        at hCBO_OB'C ⊢

      rw [hAtB']

      exact hCBO_OB'C

    exact
      False.elim
        ((hilbert_exterior_angle_not_congruent_other
            Geo
            B B' C O
            hBB'C
            hB'BO)
          hExterior)

  --------------------------------------------------------------------
  -- O-B'-B.
  --
  -- Symmetric situation.
  --------------------------------------------------------------------

  · have hOB'BData :=
      HilbertOrder.between_incidence
        O B' B hOB'B

    have hB'B :
        B' ≠ B :=
      hOB'BData.2.1

    have hOB'Bcol :
        PrimCollinear Geo O B' B :=
      hOB'BData.2.2.2.1

    have hB'BC :
        Not (PrimCollinear Geo B' B C) := by

      intro hB'BC

      have hOBB'col :
          PrimCollinear Geo O B B' :=
        PrimCollinearRotate
          Geo O B' B hOB'Bcol

      have hBB'C :
          PrimCollinear Geo B B' C :=
        PrimCollinearSwap
          Geo B' B C hB'BC

      have hOBC' :
          PrimCollinear Geo O B C :=
        hilbert_primCollinear_trans
          Geo
          O B B' C
          hB'B.symm
          hOBB'col
          hBB'C

      exact hOBC hOBC'

    have hBB'O :
        Geo.Between B B' O :=
      hOB'BData.2.2.2.2

    have hRayBB'O :
        HilbertSameRay Geo B B' O :=
      hilbert_sameRay_of_between
        Geo B B' O hBB'O

    have hAtB :
        Geo.Angle B' B C =
        Geo.Angle O B C :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        B B' O C
        hRayBB'O

    have hSym :
        Geo.AngleCongruent
          O B' C
          O B C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        O B C
        O B' C
        hAngle

    have hCB'O_OBC :
        Geo.AngleCongruent
          C B' O
          O B C :=
      (Geo.angle_congruent_reverse_first
        O B' C
        O B C).mp
        hSym

    have hExterior :
        Geo.AngleCongruent
          C B' O
          B' B C := by

      unfold Geometry.Geo.AngleCongruent
        at hCB'O_OBC ⊢

      rw [hAtB]

      exact hCB'O_OBC

    exact
      False.elim
        ((hilbert_exterior_angle_not_congruent_other
            Geo
            B' B C O
            hB'BC
            hBB'O)
          hExterior)

theorem proposition39_test_circle_nondegenerate_circumcircle
    [HilbertEuclideanPlane Geo]
    (O A C D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D := by

  have hOAC :
      PrimCollinear Geo O A C :=
    hRayAC.2.2.1

  have hACD :
      Not (PrimCollinear Geo A C D) := by

    intro hACD

    have hOAD' :
        PrimCollinear Geo O A D :=
      hilbert_primCollinear_trans
        Geo
        O A C D
        hAC
        hOAC
        hACD

    exact hOAD hOAD'

  exact
    proposition39_test_circumcircle_exists
      Geo
      A C D
      hACD

theorem proposition39_test_circle_acd_circumcircle
    [HilbertEuclideanPlane Geo]
    (O A C D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D := by

  have hAOD :
      Not (PrimCollinear Geo A O D) := by
    intro h
    exact
      hOAD
        (PrimCollinearSwap
          Geo A O D h)

  have hACD :
      Not (PrimCollinear Geo A C D) :=
    proposition39_test_first_secant_noncollinear
      Geo
      O A C D
      hAOD
      hRayAC
      hAC

  exact
    proposition39_test_circumcircle_exists
      Geo
      A C D
      hACD

theorem proposition39_test_circle_nondegenerate_angle_classification
    [HilbertEuclideanPlane Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    (
      Geo.AngleCongruent
        C A D
        C B D
    )
    ∨
    (
      BookZeroSupplement Geo
        O A D
        D C
      ∧
      Geo.AngleCongruent
        O A D
        C B D
    )
    ∨
    (
      Geo.AngleCongruent
        C A D
        O B C
      ∧
      BookZeroSupplement Geo
        O B C
        C D
    ) := by

  rcases
      proposition39_test_circle_crossing_chords_nondegenerate_data
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- O-A-C
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-A-C and O-B-D
    --------------------------------------------------------------

    · left

      exact
        proposition39_test_circle_outer_outer_angles
          Geo
          O A C B D
          hOAD
          hOBC
          hOAC
          hOBD
          hAngle

    --------------------------------------------------------------
    -- O-A-C and O-D-B
    --------------------------------------------------------------

    · right
      left

      exact
        proposition39_test_circle_mixed_outer_inner_angle_data
          Geo
          O A C B D
          hOAD
          hOAC
          hODB
          hAngle

  --------------------------------------------------------------------
  -- O-C-A
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-C-A and O-B-D
    --------------------------------------------------------------

    · right
      right

      exact
        proposition39_test_circle_mixed_inner_outer_angle_data
          Geo
          O A C B D
          hOBC
          hOCA
          hOBD
          hAngle

    --------------------------------------------------------------
    -- O-C-A and O-D-B
    --------------------------------------------------------------

    · left

      exact
        proposition39_test_circle_inner_inner_angles
          Geo
          O A C B D
          hOCA
          hODB
          hAngle

theorem proposition39_test_circle_outer_outer_sameSide_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine D chord ∧
      HilbertSameSide Geo A B chord := by

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_of_between
      Geo O A C hOAC

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_of_between
      Geo O B D hOBD

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hOCD :
      Not (PrimCollinear Geo O C D) := by
    intro h
    apply hCOD
    exact
      PrimCollinearRotate
        Geo C D O
        (PrimCollinearCycle
          Geo O C D h)

  have hODC :
      Not (PrimCollinear Geo O D C) := by
    intro h
    exact
      hOCD
        (PrimCollinearRotate
          Geo O D C h)

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    apply hOCD
    exact
      PrimCollinearCycle
        Geo D O C
        (PrimCollinearCycle
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  --------------------------------------------------------------------
  -- O and A are on the same side of CD.
  --------------------------------------------------------------------

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O A D C
        hOAC
        hOCD
    with
    ⟨chord₁, hDchord₁, hCchord₁, hOA⟩

  --------------------------------------------------------------------
  -- O and B are on the same side of CD.
  --------------------------------------------------------------------

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O B C D
        hOBD
        hODC
    with
    ⟨chord₂, hCchord₂, hDchord₂, hOB⟩

  --------------------------------------------------------------------
  -- Both carrier lines are the unique line CD.
  --------------------------------------------------------------------

  have hChordEq :
      chord₁ = chord₂ :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      chord₁ chord₂
      hCchord₁
      hDchord₁
      hCchord₂
      hDchord₂

  rw [← hChordEq] at hOB

  --------------------------------------------------------------------
  -- A -- O -- B in the same side component of CD.
  --------------------------------------------------------------------

  have hAO :
      HilbertSameSide Geo A O chord₁ :=
    hilbert_sameSide_symm
      Geo O A chord₁ hOA

  have hAB :
      HilbertSameSide Geo A B chord₁ :=
    hilbert_sameSide_trans
      Geo A O B chord₁
      hAO
      hOB

  exact
    ⟨chord₁,
      hCchord₁,
      hDchord₁,
      hAB⟩


/--
Circle theorem used in Hilbert sec. 14.

Let A,C lie on one ray from O and B,D on another ray from O.
If

    angle OAD ~= angle OBC,

then A,C,D,B are concyclic.

This is the converse circle theorem for the crossing-chord
configuration.  It is a test assumption representing the circle
theory of sec. 7 and is to be derived from Groups III-IV.
-/
axiom proposition39_test_circle_crossing_chords_concyclic
    [HilbertEuclideanPlane Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    HilbertConcyclic4 Geo A C D B

theorem proposition39_test_pascal_equal_angles_concyclic
    [HilbertEuclideanPlane Geo]
    (O A C A' B' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hAngle :
      Geo.AngleCongruent
        O A D'
        O B' C) :
    HilbertConcyclic4 Geo A C D' B' := by

  have hAO :
      A ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A O A' hAOA'

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hAO

  have hAOB' :
      Not (PrimCollinear Geo A O B') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      A B'
      hAOA'
      hRayAA
      hRayA'B'

  have hRayB'D' :
      HilbertSameRay Geo O B' D' :=
    hilbert_sameRay_common_reference
      Geo
      O A' B' D'
      hRayA'B'
      hRayA'D'

  exact
    proposition39_test_circle_crossing_chords_concyclic
      Geo
      O A C B' D'
      hAOB'
      hRayAC
      hRayB'D'
      hAngle


------------------------------------------------------------------------
-- Temporary inscribed-quadrilateral angle theorem
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Hilbert sec. 7
-- Circle theorem: inscribed angles in the crossing-chord configuration
------------------------------------------------------------------------

/--
Circle theorem used in Hilbert sec. 14.

If A,C lie on one ray from O, B,D lie on another ray from O,
and A,C,D,B are concyclic, then the two inscribed angles determined
by the chord CB are congruent.

This is a test assumption representing the circle theorem of sec. 7.
It is to be derived from Groups III-IV.
-/
axiom proposition39_test_circle_crossing_chords_angle
    [HilbertEuclideanPlane Geo]
    (O A C B D : Geo.Point)
    (hAOC : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hCyclic : HilbertConcyclic4 Geo A C D B) :
    Geo.AngleCongruent
      O D C
      O A B

theorem proposition39_test_pascal_concyclic_angle
    [HilbertEuclideanPlane Geo]
    (O A C A' B' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hCyclic : HilbertConcyclic4 Geo A C D' B') :
    Geo.AngleCongruent
      O D' C
      O A B' := by

  have hRayB'D' :
      HilbertSameRay Geo O B' D' :=
    hilbert_sameRay_common_reference
      Geo
      O A' B' D'
      hRayA'B'
      hRayA'D'

  have hAO :
      A ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A O A' hAOA'

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hAO

  have hAOB' :
      Not (PrimCollinear Geo A O B') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      A B'
      hAOA'
      hRayAA
      hRayA'B'

  exact
    proposition39_test_circle_crossing_chords_angle
      Geo
      O A C B' D'
      hAOB'
      hRayAC
      hRayB'D'
      hCyclic

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (3t)
------------------------------------------------------------------------

/--
Hilbert's relation (3t) in the special Pascal configuration.

From

    angle OAD' ~= angle OB'C

the four points A,C,D',B' are concyclic.  The inscribed-quadrilateral
angle theorem then gives

    angle OD'C ~= angle OAB'.
-/
theorem proposition39_test_pascal_third_angle
    [HilbertEuclideanPlane Geo]
    (O A C A' B' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hAngle :
      Geo.AngleCongruent
        O A D'
        O B' C) :
    Geo.AngleCongruent
      O D' C
      O A B' := by

  have hCyclic :
      HilbertConcyclic4 Geo A C D' B' :=
    proposition39_test_pascal_equal_angles_concyclic
      Geo
      O A C A' B' D'
      hAOA'
      hRayAC
      hRayA'B'
      hRayA'D'
      hAngle

  exact
    proposition39_test_pascal_concyclic_angle
      Geo
      O A C A' B' D'
      hAOA'
      hRayAC
      hRayA'B'
      hRayA'D'
      hCyclic

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: combine (3t) and (4t)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (4t)
------------------------------------------------------------------------

/--
Hilbert's relation (4t).

The triangles OD'C and OBA' are congruent by SAS:
OD' ~= OB, OC ~= OA', and their included angles at O coincide.
-/
theorem proposition39_test_pascal_second_triangles
    [HilbertCongruence Geo]
    (O A B C A' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hOC_OA' : Geo.Congruent O C O A')
    (hOB_OD' : Geo.Congruent O B O D') :
    Geo.AngleCongruent O D' C O B A' := by

  have hA'OA :
      Not (PrimCollinear Geo A' O A) := by
    intro h
    exact
      hAOA'
        (PrimCollinearSymm
          Geo A' O A h)

  have hD'OC :
      Not (PrimCollinear Geo D' O C) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A' O A
      D' C
      hA'OA
      hRayA'D'
      hRayAC

  have hOD'C :
      Not (PrimCollinear Geo O D' C) := by
    intro h
    exact
      hD'OC
        (PrimCollinearSwap
          Geo O D' C h)

  have hA'O :
      A' ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A' O A hA'OA

  have hRayA'A' :
      HilbertSameRay Geo O A' A' :=
    hilbert_sameRay_refl
      Geo O A' hA'O

  have hBOA' :
      Not (PrimCollinear Geo B O A') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      B A'
      hAOA'
      hRayAB
      hRayA'A'

  have hOBA' :
      Not (PrimCollinear Geo O B A') := by
    intro h
    exact
      hBOA'
        (PrimCollinearSwap
          Geo O B A' h)

  have hLeftFirst :
      Geo.Angle A' O C =
      Geo.Angle D' O C :=
    hilbert_angle_eq_of_sameRay_first
      Geo O A' D' C hRayA'D'

  have hLeftSecond :
      Geo.Angle A' O A =
      Geo.Angle A' O C :=
    hilbert_angle_eq_of_sameRay_second
      Geo O A' A C hRayAC

  have hLeft :
      Geo.Angle D' O C =
      Geo.Angle A' O A := by
    calc
      Geo.Angle D' O C =
          Geo.Angle A' O C :=
        hLeftFirst.symm
      _ = Geo.Angle A' O A :=
        hLeftSecond.symm

  have hRightFirst :
      Geo.Angle A O A' =
      Geo.Angle B O A' :=
    hilbert_angle_eq_of_sameRay_first
      Geo O A B A' hRayAB

  have hRight :
      Geo.Angle B O A' =
      Geo.Angle A' O A := by
    calc
      Geo.Angle B O A' =
          Geo.Angle A O A' :=
        hRightFirst.symm
      _ = Geo.Angle A' O A :=
        (Geo.angle_swap A' O A).symm

  have hRefl :
      Geo.AngleCongruent
        A' O A
        A' O A :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A' O A
      hA'OA

  have hAngleO :
      Geo.AngleCongruent
        D' O C
        B O A' := by
    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢
    rw [hLeft, hRight]
    exact hRefl

  have hOD'_OB :
      Geo.Congruent O D' O B :=
    hilbert_congruent_symmetry
      Geo O B O D' hOB_OD'

  exact
    (hilbert_sas_remaining_angles
      Geo
      O D' C
      O B A'
      hOD'C
      hOBA'
      hOD'_OB
      hOC_OA'
      hAngleO).1

/--
In the special Pascal configuration, the circle argument gives (3t),

    angle OD'C ~= angle OAB',

while the congruent triangles OD'C and OBA' give (4t),

    angle OD'C ~= angle OBA'.

Hence

    angle OAB' ~= angle OBA'.
-/
theorem proposition39_test_pascal_after_circle
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hOC_OA' : Geo.Congruent O C O A')
    (hOB_OD' : Geo.Congruent O B O D')
    (hAngle :
      Geo.AngleCongruent
        O A D'
        O B' C) :
    Geo.AngleCongruent
      O A B'
      O B A' := by

  --------------------------------------------------------------------
  -- Hilbert (3t): the cyclic quadrilateral A C D' B'.
  --------------------------------------------------------------------

  have h3 :
      Geo.AngleCongruent
        O D' C
        O A B' :=
    proposition39_test_pascal_third_angle
      Geo
      O A C A' B' D'
      hAOA'
      hRayAC
      hRayA'B'
      hRayA'D'
      hAngle

  --------------------------------------------------------------------
  -- Hilbert (4t): triangles OD'C and OBA' are congruent.
  --------------------------------------------------------------------

  have h4 :
      Geo.AngleCongruent
        O D' C
        O B A' :=
      proposition39_test_pascal_second_triangles
      Geo
      O A B C A' D'
      hAOA'
      hRayAB
      hRayAC
      hRayA'D'
      hOC_OA'
      hOB_OD'

  --------------------------------------------------------------------
  -- (3t) + (4t).
  --------------------------------------------------------------------

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O A B'
      O D' C
      O B A'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        O D' C
        O A B'
        h3)
      h4

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relations (1t)--(4t)
------------------------------------------------------------------------

/--
Hilbert's four angle relations in the special Pascal configuration.

From

  (1t)  angle OC'B ~= angle OAD'
  (2t)  angle OC'B ~= angle OB'C

we obtain angle OAD' ~= angle OB'C.

The circle argument then gives (3t), and SAS gives (4t), hence

        angle OAB' ~= angle OBA'.
-/
theorem proposition39_test_pascal_angle_chain
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hOC_OA' : Geo.Congruent O C O A')
    (hOB_OD' : Geo.Congruent O B O D')
    (h1 :
      Geo.AngleCongruent
        O C' B
        O A D')
    (h2 :
      Geo.AngleCongruent
        O C' B
        O B' C) :
    Geo.AngleCongruent
      O A B'
      O B A' := by

  have h1symm :
      Geo.AngleCongruent
        O A D'
        O C' B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O C' B
      O A D'
      h1

  have hAngle :
      Geo.AngleCongruent
        O A D'
        O B' C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O A D'
      O C' B
      O B' C
      h1symm
      h2

  exact
    proposition39_test_pascal_after_circle
      Geo
      O A B C A' B' D'
      hAOA'
      hRayAB
      hRayAC
      hRayA'B'
      hRayA'D'
      hOC_OA'
      hOB_OD'
      hAngle

------------------------------------------------------------------------
-- Order on two distinct points of one Hilbert ray
------------------------------------------------------------------------

/--
Two distinct points on the same ray from O are linearly ordered:
one lies between O and the other.

The third possible ordering, with O between them, is excluded by
the definition of HilbertSameRay.
-/
theorem proposition39_test_sameRay_order
    [HilbertOrder Geo]
    (O A B : Geo.Point)
    (hRay : HilbertSameRay Geo O A B)
    (hAB : A ≠ B) :
    Geo.Between O A B ∨
    Geo.Between O B A := by

  have hOA :
      O ≠ A :=
    hRay.1.symm

  have hAB' :
      A ≠ B :=
    hAB

  have hOB :
      O ≠ B :=
    hRay.2.1.symm

  have hOAB :
      PrimCollinear Geo O A B :=
    hRay.2.2.1

  rcases
      hilbert_between_trichotomy
        Geo
        O A B
        hOA
        hAB'
        hOB
        hOAB
    with
    hOABet | hAOB | hOBA

  · exact Or.inl hOABet

  · exact False.elim (hRay.2.2.2 hAOB)

  · exact Or.inr hOBA

------------------------------------------------------------------------
-- Corresponding-angle criterion in the order O-A-B
------------------------------------------------------------------------

/--
Assume O-A-B and A',B' lie on the same ray from O.

If

    angle OAB' ~= angle OBA',

then AB' is parallel to BA'.

The proof replaces the corresponding-angle configuration by an
alternate-angle configuration: extend B'A through A to X.  The angle
BAX is vertical to OAB', while X and A' lie on opposite sides of the
transversal AB.
-/
theorem proposition39_test_corresponding_parallel_case_OAB
    [HilbertCongruence Geo]
    (O A B A' B' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hOAB : Geo.Between O A B)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hAngle :
      Geo.AngleCongruent
        O A B'
        O B A') :
    Geo.Parallel A B' B A' := by

  --------------------------------------------------------------------
  -- The transversal OA = OB.
  --------------------------------------------------------------------

  have hOA :
      Ne O A :=
    (HilbertOrder.between_incidence
      O A B hOAB).1

  rcases
      HilbertPlaneIncidence.line_through
        O A hOA
    with
    ⟨trans, hOtrans, hAtrans⟩

  have hOABcol :
      PrimCollinear Geo O A B :=
    (HilbertOrder.between_incidence
      O A B hOAB).2.2.2.1

  have hBtrans :
      HilbertIncidence.OnLine B trans :=
    hilbert_collinear_on_line
      Geo
      O A B
      trans
      hOA
      hOtrans
      hAtrans
      hOABcol

  --------------------------------------------------------------------
  -- The line of the ray OA'.
  --------------------------------------------------------------------

  have hOA' :
      Ne O A' :=
    hRayA'B'.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O A' hOA'
    with
    ⟨rayLine, hOray, hA'ray⟩

  have hAoffRay :
      Not (HilbertIncidence.OnLine A rayLine) := by
    intro hAray
    exact
      hAOA'
        ⟨rayLine,
          hAray,
          hOray,
          hA'ray⟩

  have hRayA'A' :
      HilbertSameRay Geo O A' A' :=
    hilbert_sameRay_refl
      Geo O A' hRayA'B'.1

  have hSameB'A' :
      HilbertSameSide Geo B' A' trans :=
    hilbert_sameRay_points_sameSide
      Geo
      O A'
      B' A'
      A
      rayLine trans
      hOray
      hA'ray
      hOtrans
      hAtrans
      hAoffRay
      hRayA'B'
      hRayA'A'

  --------------------------------------------------------------------
  -- Extend B'A through A to X.
  --------------------------------------------------------------------

  have hB'A :
      Ne B' A := by
    intro hEq
    subst B'
    exact hSameB'A'.1 hAtrans

  rcases
      HilbertOrder.between_extension
        B' A hB'A
    with
    ⟨X, hB'AX⟩

  have hB'AXData :=
    HilbertOrder.between_incidence
      B' A X hB'AX

  have hAX :
      Ne A X :=
    hB'AXData.2.1

  rcases hB'AXData.2.2.2.1 with
    ⟨lineAX, hB'line, hAline, hXline⟩

  have hXoff :
      Not (HilbertIncidence.OnLine X trans) := by
    intro hXtrans

    have hEq :
        lineAX = trans :=
      HilbertPlaneIncidence.line_unique
        A X hAX
        lineAX trans
        hAline hXline
        hAtrans hXtrans

    have hB'trans :
        HilbertIncidence.OnLine B' trans := by
      rw [← hEq]
      exact hB'line

    exact hSameB'A'.1 hB'trans

  --------------------------------------------------------------------
  -- X and A' are on opposite sides of the transversal.
  --------------------------------------------------------------------

  have hOppB'X :
      HilbertOppositeSide Geo B' X trans :=
    ⟨hSameB'A'.1,
      hXoff,
      ⟨A, hB'AX, hAtrans⟩⟩

  have hOppXB' :
      HilbertOppositeSide Geo X B' trans :=
    hilbert_oppositeSide_symm
      Geo B' X trans hOppB'X

  have hOppXA' :
      HilbertOppositeSide Geo X A' trans :=
    hilbert_oppositeSide_transport_right
      Geo
      X B' A'
      trans
      hOppXB'
      hSameB'A'

  --------------------------------------------------------------------
  -- angle OAB' ~= angle BAX by vertical angles.
  --------------------------------------------------------------------

  have hOAB' :
      Not (PrimCollinear Geo O A B') :=
    hilbert_not_collinear_of_off_line
      Geo
      O A B'
      trans
      hOA
      hOtrans
      hAtrans
      hSameB'A'.1

  have hVertical :
      Geo.AngleCongruent
        O A B'
        B A X :=
    hilbert_vertical_angles
      Geo
      O A B'
      B X
      hOAB
      hB'AX
      hOAB'

  have hBAX_OBA' :
      Geo.AngleCongruent
        B A X
        O B A' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A X
      O A B'
      O B A'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        O A B'
        B A X
        hVertical)
      hAngle

  --------------------------------------------------------------------
  -- Choose T between A and B and rewrite to alternate angles.
  --------------------------------------------------------------------

  have hAB :
      Ne A B :=
    (HilbertOrder.between_incidence
      O A B hOAB).2.1

  rcases
      hilbert_between_exists
        Geo A B hAB
    with
    ⟨T, hATB⟩

  have hBTA :
      Geo.Between B T A :=
    (HilbertOrder.between_incidence
      A T B hATB).2.2.2.2

  have hBAO :
      Geo.Between B A O :=
    (HilbertOrder.between_incidence
      O A B hOAB).2.2.2.2

  have hRayATB :
      HilbertSameRay Geo A T B :=
    hilbert_sameRay_of_between
      Geo A T B hATB

  have hRayBTA :
      HilbertSameRay Geo B T A :=
    hilbert_sameRay_of_between
      Geo B T A hBTA

  have hRayBAT :
      HilbertSameRay Geo B A T :=
    hilbert_sameRay_symm
      Geo B T A hRayBTA

  have hRayBAO :
      HilbertSameRay Geo B A O :=
    hilbert_sameRay_of_between
      Geo B A O hBAO

  have hRayBTO :
      HilbertSameRay Geo B T O :=
    hilbert_sameRay_common_reference
      Geo
      B A T O
      hRayBAT
      hRayBAO

  have hAtA :
      Geo.Angle T A X =
      Geo.Angle B A X :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      A T B X
      hRayATB

  have hAtB :
      Geo.Angle T B A' =
      Geo.Angle O B A' :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      B T O A'
      hRayBTO

  have hAlternate :
      Geo.AngleCongruent
        T A X
        T B A' := by
    unfold Geometry.Geo.AngleCongruent
      at hBAX_OBA' ⊢
    rw [hAtA, hAtB]
    exact hBAX_OBA'

  --------------------------------------------------------------------
  -- Equal alternate angles give AX || BA'.
  --------------------------------------------------------------------

  have hParallelAX :
      Geo.Parallel A X B A' :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      A X
      B T A'
      trans
      hATB
      hAtrans
      hBtrans
      hOppXA'
      hAlternate

  --------------------------------------------------------------------
  -- AX and AB' are the same point-line.
  --------------------------------------------------------------------

  have hAB' :
      Ne A B' :=
    hB'A.symm

  have hPointLine :
      Geo.PointLine A X =
      Geo.PointLine A B' :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      A X
      A B'
      lineAX
      hAX
      hAB'
      hAline
      hXline
      hAline
      hB'line

  exact
    ⟨hAB',
      hParallelAX.2.1,
      hPointLine ▸ hParallelAX.2.2⟩

------------------------------------------------------------------------
-- Corresponding-angle criterion in the order O-B-A
------------------------------------------------------------------------

/--
The second possible order of A and B on the same ray from O.

After exchanging A with B and A' with B', this is exactly the
previous O-A-B case.
-/
theorem proposition39_test_corresponding_parallel_case_OBA
    [HilbertCongruence Geo]
    (O A B A' B' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hOBA : Geo.Between O B A)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hAngle :
      Geo.AngleCongruent
        O A B'
        O B A') :
    Geo.Parallel A B' B A' := by

  --------------------------------------------------------------------
  -- B lies on the same ray OA.
  --------------------------------------------------------------------

  have hRayBA :
      HilbertSameRay Geo O B A :=
    hilbert_sameRay_of_between
      Geo O B A hOBA

  have hRayAB :
      HilbertSameRay Geo O A B :=
    hilbert_sameRay_symm
      Geo O B A hRayBA

  --------------------------------------------------------------------
  -- Hence B,O,B' is also noncollinear.
  --------------------------------------------------------------------

  have hBOB' :
      Not (PrimCollinear Geo B O B') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      B B'
      hAOA'
      hRayAB
      hRayA'B'

  --------------------------------------------------------------------
  -- Reverse the second ray and the angle congruence.
  --------------------------------------------------------------------

  have hRayB'A' :
      HilbertSameRay Geo O B' A' :=
    hilbert_sameRay_symm
      Geo O A' B' hRayA'B'

  have hAngle' :
      Geo.AngleCongruent
        O B A'
        O A B' :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O A B'
      O B A'
      hAngle

  --------------------------------------------------------------------
  -- Apply the already proved O-B-A' / O-A-B' instance.
  --------------------------------------------------------------------

  have hParallel :
      Geo.Parallel B A' A B' :=
    proposition39_test_corresponding_parallel_case_OAB
      Geo
      O
      B A
      B' A'
      hBOB'
      hOBA
      hRayB'A'
      hAngle'

  --------------------------------------------------------------------
  -- Parallelism is symmetric in the two lines.
  --------------------------------------------------------------------

  exact
    ⟨hParallel.2.1,
      hParallel.1,
      hParallel.2.2.symm⟩

------------------------------------------------------------------------
-- Corresponding-angle criterion on two rays
------------------------------------------------------------------------

/--
Let A,B lie on one ray from O and A',B' on another ray from O.
If A and B are distinct and

    angle OAB' ~= angle OBA',

then

    AB' || BA'.

The proof is by the two possible orders of A and B on their common ray.
-/
theorem proposition39_test_corresponding_parallel
    [HilbertCongruence Geo]
    (O A B A' B' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hAB : A ≠ B)
    (hAngle :
      Geo.AngleCongruent
        O A B'
        O B A') :
    Geo.Parallel A B' B A' := by

  rcases
      proposition39_test_sameRay_order
        Geo O A B hRayAB hAB
    with hOAB | hOBA

  · exact
      proposition39_test_corresponding_parallel_case_OAB
        Geo
        O A B A' B'
        hAOA'
        hOAB
        hRayA'B'
        hAngle

  · exact
      proposition39_test_corresponding_parallel_case_OBA
        Geo
        O A B A' B'
        hAOA'
        hOBA
        hRayA'B'
        hAngle

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: angle chain gives the final parallel
------------------------------------------------------------------------

/--
The four angle relations of Hilbert's special Pascal argument imply

    AB' || BA'.

The relations (1t)--(4t) first yield

    angle OAB' ~= angle OBA',

and the corresponding-angle criterion on the two rays then gives
the required parallelism.
-/
theorem proposition39_test_pascal_parallel_from_angle_chain
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hAB : A ≠ B)
    (hOC_OA' : Geo.Congruent O C O A')
    (hOB_OD' : Geo.Congruent O B O D')
    (h1 :
      Geo.AngleCongruent
        O C' B
        O A D')
    (h2 :
      Geo.AngleCongruent
        O C' B
        O B' C) :
    Geo.Parallel A B' B A' := by

  have hAngle :
      Geo.AngleCongruent
        O A B'
        O B A' :=
    proposition39_test_pascal_angle_chain
      Geo
      O A B C A' B' C' D'
      hAOA'
      hRayAB
      hRayAC
      hRayA'B'
      hRayA'D'
      hOC_OA'
      hOB_OD'
      h1
      h2

  exact
    proposition39_test_corresponding_parallel
      Geo
      O A B A' B'
      hAOA'
      hRayAB
      hRayA'B'
      hAB
      hAngle

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: construction of D'
------------------------------------------------------------------------

/--
Lay off OB on the ray OA'.

The constructed point D' lies on ray OA' and satisfies

    OB ~= OD'.
-/
theorem proposition39_test_pascal_construct_D'
    [HilbertCongruence Geo]
    (O B A' : Geo.Point)
    (hOA' : O ≠ A') :
    ∃ D' : Geo.Point,
      HilbertSameRay Geo O A' D' ∧
      Geo.Congruent O B O D' := by

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O B
        O A'
        hOA'
    with
    ⟨D', hRayA'D', hOD'_OB⟩

  have hOB_OD' :
      Geo.Congruent O B O D' :=
    hilbert_congruent_symmetry
      Geo
      O D'
      O B
      hOD'_OB

  exact
    ⟨D', hRayA'D', hOB_OD'⟩

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (1t)
------------------------------------------------------------------------

/--
The first metric step in Hilbert's special Pascal argument.

If A,B lie on one ray from O, while C',D' lie on the ray OA', and

    OC' ~= OA
    OB  ~= OD',

then SAS for triangles OC'B and OAD' gives

    angle OC'B ~= angle OAD'.
-/
theorem proposition39_test_pascal_first_triangles
    [HilbertCongruence Geo]
    (O A B A' C' D' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hRayA'D' : HilbertSameRay Geo O A' D')
    (hOC'_OA : Geo.Congruent O C' O A)
    (hOB_OD' : Geo.Congruent O B O D') :
    Geo.AngleCongruent O C' B O A D' := by

  --------------------------------------------------------------------
  -- Triangle OC'B is noncollinear.
  --------------------------------------------------------------------

  have hA'OA :
      Not (PrimCollinear Geo A' O A) := by
    intro h
    exact
      hAOA'
        (PrimCollinearSymm
          Geo A' O A h)

  have hC'OB :
      Not (PrimCollinear Geo C' O B) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A' O A
      C' B
      hA'OA
      hRayA'C'
      hRayAB

  have hOC'B :
      Not (PrimCollinear Geo O C' B) := by
    intro h
    exact
      hC'OB
        (PrimCollinearSwap
          Geo O C' B h)

  --------------------------------------------------------------------
  -- Triangle OAD' is noncollinear.
  --------------------------------------------------------------------

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAB.1

  have hAOD' :
      Not (PrimCollinear Geo A O D') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      A D'
      hAOA'
      hRayAA
      hRayA'D'

  have hOAD' :
      Not (PrimCollinear Geo O A D') := by
    intro h
    exact
      hAOD'
        (PrimCollinearSwap
          Geo O A D' h)

  --------------------------------------------------------------------
  -- The included angles at O are the same angle.
  --------------------------------------------------------------------

  have hRayC'A' :
      HilbertSameRay Geo O C' A' :=
    hilbert_sameRay_symm
      Geo O A' C' hRayA'C'

  have hRayBA :
      HilbertSameRay Geo O B A :=
    hilbert_sameRay_symm
      Geo O A B hRayAB

  have hAngleEq :
      Geo.Angle C' O B =
      Geo.Angle A O D' := by
    calc
      Geo.Angle C' O B =
          Geo.Angle A' O B :=
        hilbert_angle_eq_of_sameRay_first
          Geo O C' A' B hRayC'A'

      _ = Geo.Angle A' O A :=
        hilbert_angle_eq_of_sameRay_second
          Geo O A' B A hRayBA

      _ = Geo.Angle A O A' :=
        Geo.angle_swap A' O A

      _ = Geo.Angle A O D' :=
        hilbert_angle_eq_of_sameRay_second
          Geo O A A' D' hRayA'D'

  have hAngleRefl :
      Geo.AngleCongruent
        A O D'
        A O D' :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O D'
      hAOD'

  have hAngle :
      Geo.AngleCongruent
        C' O B
        A O D' := by
    unfold Geometry.Geo.AngleCongruent
      at hAngleRefl ⊢
    rw [hAngleEq]
    exact hAngleRefl

  --------------------------------------------------------------------
  -- SAS: triangles OC'B and OAD'.
  --------------------------------------------------------------------

  exact
    (hilbert_sas_remaining_angles
      Geo
      O C' B
      O A D'
      hOC'B
      hOAD'
      hOC'_OA
      hOB_OD'
      hAngle).1

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (2t)
-- Order case O-C'-B'
------------------------------------------------------------------------

/--
Hilbert's relation (2t) in the order case

    O - C' - B'.

Assume B and C lie on the same side of the transversal C'B'. From

    C'B || B'C

we obtain

    angle OC'B ~= angle OB'C.

The proof uses Hilbert Theorem 30 for alternate angles and
Theorem 14 for the resulting adjacent linear pairs.
-/
theorem proposition39_test_pascal_parallel_angle_case_OC'B'
    [HilbertEuclideanPlane Geo]
    (O B C B' C' : Geo.Point)
    (trans : Geo.Line)
    (hOC'B' : Geo.Between O C' B')
    (hC'trans : HilbertIncidence.OnLine C' trans)
    (hB'trans : HilbertIncidence.OnLine B' trans)
    (hSameBC : HilbertSameSide Geo B C trans)
    (hParallel : Geo.Parallel C' B B' C) :
    Geo.AngleCongruent O C' B O B' C := by

  --------------------------------------------------------------------
  -- Basic data from O-C'-B'.
  --------------------------------------------------------------------

  have hOC'B'data :=
    HilbertOrder.between_incidence
      O C' B' hOC'B'

  have hC'B' : C' ≠ B' :=
    hOC'B'data.2.1

  --------------------------------------------------------------------
  -- Choose M strictly between C' and B'.
  --------------------------------------------------------------------

  rcases
      hilbert_between_exists
        Geo C' B' hC'B'
    with
    ⟨M, hC'MB'⟩

  have hC'MB'data :=
    HilbertOrder.between_incidence
      C' M B' hC'MB'

  have hMtrans :
      HilbertIncidence.OnLine M trans :=
    hilbert_between_on_line
      Geo
      C' M B'
      trans
      hC'trans
      hB'trans
      hC'MB'

  --------------------------------------------------------------------
  -- Extend CB' through B' to F:
  --
  --     C - B' - F.
  --------------------------------------------------------------------

  have hCB' : C ≠ B' :=
    hParallel.2.1.symm

  rcases
      HilbertOrder.between_extension
        C B' hCB'
    with
    ⟨F, hCB'F⟩

  have hCB'Fdata :=
    HilbertOrder.between_incidence
      C B' F hCB'F

  have hB'F : B' ≠ F :=
    hCB'Fdata.2.1

  --------------------------------------------------------------------
  -- F lies off the transversal.
  --------------------------------------------------------------------

  have hBoff :
      Not (HilbertIncidence.OnLine B trans) :=
    hSameBC.1

  have hCoff :
      Not (HilbertIncidence.OnLine C trans) :=
    hSameBC.2.1

  have hFoff :
      Not (HilbertIncidence.OnLine F trans) := by

    intro hFtrans

    have hB'FC :
        PrimCollinear Geo B' F C :=
      PrimCollinearCycle
        Geo C B' F
        hCB'Fdata.2.2.2.1

    have hCtrans :
        HilbertIncidence.OnLine C trans :=
      hilbert_collinear_on_line
        Geo
        B' F C
        trans
        hB'F
        hB'trans
        hFtrans
        hB'FC

    exact hCoff hCtrans

  --------------------------------------------------------------------
  -- C and F are opposite across the transversal.
  --------------------------------------------------------------------

  have hOppCF :
      HilbertOppositeSide Geo C F trans :=
    ⟨hCoff,
     hFoff,
     ⟨B', hCB'F, hB'trans⟩⟩

  --------------------------------------------------------------------
  -- Transport the opposite-side relation from C to B.
  --------------------------------------------------------------------

  have hOppFC :
      HilbertOppositeSide Geo F C trans :=
    hilbert_oppositeSide_symm
      Geo C F trans hOppCF

  have hSameCB :
      HilbertSameSide Geo C B trans :=
    hilbert_sameSide_symm
      Geo B C trans hSameBC

  have hOppFB :
      HilbertOppositeSide Geo F B trans :=
    hilbert_oppositeSide_transport_right
      Geo
      F C B
      trans
      hOppFC
      hSameCB

  have hOppBF :
      HilbertOppositeSide Geo B F trans :=
    hilbert_oppositeSide_symm
      Geo F B trans hOppFB

  --------------------------------------------------------------------
  -- Since C,B',F are collinear,
  --
  --     PointLine B'C = PointLine B'F.
  --------------------------------------------------------------------

  rcases hCB'Fdata.2.2.2.1 with
    ⟨lineBC, hClineBC, hB'lineBC, hFlineBC⟩

  have hPointLine :
      Geo.PointLine B' C =
      Geo.PointLine B' F :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      B' C
      B' F
      lineBC
      hParallel.2.1
      hB'F
      hB'lineBC
      hClineBC
      hB'lineBC
      hFlineBC

  have hParallelF :
      Geo.Parallel C' B B' F := by

    refine
      ⟨hParallel.1,
       hB'F,
       ?_⟩

    rw [← hPointLine]

    exact hParallel.2.2

  --------------------------------------------------------------------
  -- Hilbert Theorem 30:
  --
  --     angle MC'B ~= angle MB'F.
  --------------------------------------------------------------------

  have hAlternate :
      Geo.AngleCongruent M C' B M B' F :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo
      C' B
      B' M F
      trans
      hC'MB'
      hC'trans
      hB'trans
      hOppBF
      hParallelF

  --------------------------------------------------------------------
  -- Recover the two linear pairs.
  --------------------------------------------------------------------

  have hB'MC' :
      Geo.Between B' M C' :=
    hC'MB'data.2.2.2.2

  have hB'C'O :
      Geo.Between B' C' O :=
    hOC'B'data.2.2.2.2

  have hInner :=
    hilbert_between_inner_trans
      Geo
      B' M C' O
      hB'MC'
      hB'C'O

  have hMC'O :
      Geo.Between M C' O :=
    hInner.1

  have hB'MO :
      Geo.Between B' M O :=
    hInner.2

  have hFB'C :
      Geo.Between F B' C :=
    hCB'Fdata.2.2.2.2

  --------------------------------------------------------------------
  -- Noncollinearity required by Theorem 14.
  --------------------------------------------------------------------

  have hMC' : M ≠ C' :=
    hC'MB'data.1.symm

  have hMC'B :
      Not (PrimCollinear Geo M C' B) :=
    hilbert_not_collinear_of_off_line
      Geo
      M C' B
      trans
      hMC'
      hMtrans
      hC'trans
      hBoff

  have hB'M : B' ≠ M :=
    hC'MB'data.2.1.symm

  have hB'MF :
      Not (PrimCollinear Geo B' M F) :=
    hilbert_not_collinear_of_off_line
      Geo
      B' M F
      trans
      hB'M
      hB'trans
      hMtrans
      hFoff

  have hFB'M :
      Not (PrimCollinear Geo F B' M) := by

    intro h

    exact
      hB'MF
        (PrimCollinearCycle
          Geo F B' M h)

  --------------------------------------------------------------------
  -- Reverse the second angle:
  --
  --     angle MC'B ~= angle MB'F
  --
  -- becomes
  --
  --     angle MC'B ~= angle FB'M.
  --------------------------------------------------------------------

  have hAlternate' :
      Geo.AngleCongruent M C' B F B' M :=
    (Geo.angle_congruent_reverse_second
      M C' B
      M B' F).mp hAlternate

  --------------------------------------------------------------------
  -- Hilbert Theorem 14 applied to
  --
  --     M - C' - O
  --     F - B' - C
  --
  -- gives
  --
  --     angle BC'O ~= angle MB'C.
  --------------------------------------------------------------------

  have hAdjacent :
      Geo.AngleCongruent B C' O M B' C :=
    hilbert_adjacent_angles_congruent
      Geo
      M C' B O
      F B' M C
      hMC'O
      hFB'C
      hMC'B
      hFB'M
      hAlternate'

  --------------------------------------------------------------------
  -- At B', M and O determine the same ray.
  --------------------------------------------------------------------

  have hRayB'MO :
      HilbertSameRay Geo B' M O :=
    hilbert_sameRay_of_between
      Geo B' M O hB'MO

  have hRight :
      Geo.Angle M B' C =
      Geo.Angle O B' C :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      B' M O C
      hRayB'MO

  --------------------------------------------------------------------
  -- angle BC'O is the same unoriented angle as angle OC'B.
  --------------------------------------------------------------------

  unfold Geometry.Geo.AngleCongruent
    at hAdjacent ⊢

  rw [Geo.angle_swap O C' B, ← hRight]

  exact hAdjacent

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: transversal data for (2t)
------------------------------------------------------------------------

/--
In the special Pascal configuration, C' and B' lie on the second
ray from O, hence on its supporting line.  Since B and C lie on the
first ray and the two rays are noncollinear, B and C lie on the same
side of that supporting line.

This supplies the transversal data needed for relation (2t).
-/
theorem proposition39_test_pascal_transversal_data
    [HilbertOrder Geo]
    (O A B C A' B' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'C' : HilbertSameRay Geo O A' C') :
    ∃ trans : Geo.Line,
      HilbertIncidence.OnLine C' trans ∧
      HilbertIncidence.OnLine B' trans ∧
      HilbertSameSide Geo B C trans := by

  --------------------------------------------------------------------
  -- Supporting line of the first ray OA.
  --------------------------------------------------------------------

  have hAO :
      A ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A O A' hAOA'

  have hOA :
      O ≠ A :=
    hAO.symm

  rcases
      HilbertPlaneIncidence.line_through
        O A hOA
    with
    ⟨base, hObase, hAbase⟩

  --------------------------------------------------------------------
  -- Supporting line of the second ray OA'.
  --------------------------------------------------------------------

  have hA'OA :
      Not (PrimCollinear Geo A' O A) := by
    intro h
    exact
      hAOA'
        (PrimCollinearSymm
          Geo A' O A h)

  have hA'O :
      A' ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A' O A hA'OA

  have hOA' :
      O ≠ A' :=
    hA'O.symm

  rcases
      HilbertPlaneIncidence.line_through
        O A' hOA'
    with
    ⟨trans, hOtrans, hA'trans⟩

  --------------------------------------------------------------------
  -- A' is off the first supporting line.
  --------------------------------------------------------------------

  have hA'offBase :
      Not (HilbertIncidence.OnLine A' base) := by
    intro hA'base
    exact
      hAOA'
        ⟨base,
          hAbase,
          hObase,
          hA'base⟩

  --------------------------------------------------------------------
  -- C' and B' lie on the second supporting line.
  --------------------------------------------------------------------

  have hC'trans :
      HilbertIncidence.OnLine C' trans :=
    hilbert_collinear_on_line
      Geo
      O A' C'
      trans
      hOA'
      hOtrans
      hA'trans
      hRayA'C'.2.2.1

  have hB'trans :
      HilbertIncidence.OnLine B' trans :=
    hilbert_collinear_on_line
      Geo
      O A' B'
      trans
      hOA'
      hOtrans
      hA'trans
      hRayA'B'.2.2.1

  --------------------------------------------------------------------
  -- B and C are on the same side of the second supporting line.
  --------------------------------------------------------------------

  have hSameBC :
      HilbertSameSide Geo B C trans :=
    hilbert_sameRay_points_sameSide
      Geo
      O A
      B C
      A'
      base trans
      hObase
      hAbase
      hOtrans
      hA'trans
      hA'offBase
      hRayAB
      hRayAC

  exact
    ⟨trans,
      hC'trans,
      hB'trans,
      hSameBC⟩

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (2t), intrinsic form
-- Order case O-C'-B'
------------------------------------------------------------------------

/--
Hilbert's relation (2t) in the special Pascal configuration,
for the order

    O - C' - B'.

The supporting line of the ray OA' supplies the transversal.
Points B and C lie on the same side of it because they belong
to the common ray OA.
-/
theorem proposition39_test_pascal_second_angle_case_OC'B'
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hOC'B' : Geo.Between O C' B')
    (hParallel : Geo.Parallel C' B B' C) :
    Geo.AngleCongruent O C' B O B' C := by

  rcases
      proposition39_test_pascal_transversal_data
        Geo
        O A B C A' B' C'
        hAOA'
        hRayAB
        hRayAC
        hRayA'B'
        hRayA'C'
    with
    ⟨trans,
      hC'trans,
      hB'trans,
      hSameBC⟩

  exact
    proposition39_test_pascal_parallel_angle_case_OC'B'
      Geo
      O B C B' C'
      trans
      hOC'B'
      hC'trans
      hB'trans
      hSameBC
      hParallel

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (2t)
-- Order case O-B'-C'
------------------------------------------------------------------------

/--
The second order case for Hilbert's relation (2t):

    O - B' - C'.

After simultaneously exchanging B with C and B' with C',
the configuration is the already proved O-C'-B' case.
-/
theorem proposition39_test_pascal_second_angle_case_OB'C'
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hOB'C' : Geo.Between O B' C')
    (hParallel : Geo.Parallel C' B B' C) :
    Geo.AngleCongruent O C' B O B' C := by

  --------------------------------------------------------------------
  -- Reverse the two parallel lines.
  --------------------------------------------------------------------

  have hParallel' :
      Geo.Parallel B' C C' B :=
    ⟨hParallel.2.1,
      hParallel.1,
      hParallel.2.2.symm⟩

  --------------------------------------------------------------------
  -- Apply the previous order case to
  --
  --     B  <-> C
  --     B' <-> C'.
  --------------------------------------------------------------------

  have hAngle' :
      Geo.AngleCongruent
        O B' C
        O C' B :=
    proposition39_test_pascal_second_angle_case_OC'B'
      Geo
      O A
      C B
      A' C' B'
      hAOA'
      hRayAC
      hRayAB
      hRayA'C'
      hRayA'B'
      hOB'C'
      hParallel'

  exact
    Geometry.Geo.angle_congruent_symmetry
      Geo
      O B' C
      O C' B
      hAngle'

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: relation (2t), general order
------------------------------------------------------------------------

/--
Hilbert's relation (2t) without fixing the order of B' and C'
on their common ray from O.

If

    C'B || B'C,

then

    angle OC'B ~= angle OB'C.
-/
theorem proposition39_test_pascal_second_angle
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hB'C' : B' ≠ C')
    (hParallel : Geo.Parallel C' B B' C) :
    Geo.AngleCongruent O C' B O B' C := by

  --------------------------------------------------------------------
  -- B' and C' lie on the same ray from O.
  --------------------------------------------------------------------

  have hRayB'C' :
      HilbertSameRay Geo O B' C' :=
    hilbert_sameRay_common_reference
      Geo
      O A' B' C'
      hRayA'B'
      hRayA'C'

  --------------------------------------------------------------------
  -- Therefore exactly one of the two relevant orders occurs.
  --------------------------------------------------------------------

  rcases
      proposition39_test_sameRay_order
        Geo
        O B' C'
        hRayB'C'
        hB'C'
    with hOB'C' | hOC'B'

  · exact
      proposition39_test_pascal_second_angle_case_OB'C'
        Geo
        O A B C A' B' C'
        hAOA'
        hRayAB
        hRayAC
        hRayA'B'
        hRayA'C'
        hOB'C'
        hParallel

  · exact
      proposition39_test_pascal_second_angle_case_OC'B'
        Geo
        O A B C A' B' C'
        hAOA'
        hRayAB
        hRayAC
        hRayA'B'
        hRayA'C'
        hOC'B'
        hParallel

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: assembled core
------------------------------------------------------------------------

/--
Hilbert's special Pascal argument, with the two radial congruences
stated explicitly.

The construction of D' gives

    OB ~= OD'.

SAS yields (1t), parallelism C'B || B'C yields (2t), and the
already established circle/angle chain gives the final conclusion

    AB' || BA'.
-/
theorem proposition39_test_special_pascal_core
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hAB : A ≠ B)
    (hB'C' : B' ≠ C')
    (hOC_OA' : Geo.Congruent O C O A')
    (hOC'_OA : Geo.Congruent O C' O A)
    (hParallel : Geo.Parallel C' B B' C) :
    Geo.Parallel A B' B A' := by

  --------------------------------------------------------------------
  -- A' is a genuine point of the second ray.
  --------------------------------------------------------------------

  have hA'OA :
      Not (PrimCollinear Geo A' O A) := by
    intro h
    exact
      hAOA'
        (PrimCollinearSymm
          Geo A' O A h)

  have hA'O :
      A' ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A' O A hA'OA

  have hOA' :
      O ≠ A' :=
    hA'O.symm

  --------------------------------------------------------------------
  -- Construct D' on ray OA' with OB ~= OD'.
  --------------------------------------------------------------------

  rcases
      proposition39_test_pascal_construct_D'
        Geo O B A' hOA'
    with
    ⟨D', hRayA'D', hOB_OD'⟩

  --------------------------------------------------------------------
  -- Relation (1t):
  --
  --     angle OC'B ~= angle OAD'.
  --------------------------------------------------------------------

  have h1 :
      Geo.AngleCongruent
        O C' B
        O A D' :=
    proposition39_test_pascal_first_triangles
      Geo
      O A B A' C' D'
      hAOA'
      hRayAB
      hRayA'C'
      hRayA'D'
      hOC'_OA
      hOB_OD'

  --------------------------------------------------------------------
  -- Relation (2t):
  --
  --     angle OC'B ~= angle OB'C.
  --------------------------------------------------------------------

  have h2 :
      Geo.AngleCongruent
        O C' B
        O B' C :=
    proposition39_test_pascal_second_angle
      Geo
      O A B C A' B' C'
      hAOA'
      hRayAB
      hRayAC
      hRayA'B'
      hRayA'C'
      hB'C'
      hParallel

  --------------------------------------------------------------------
  -- Relations (1t)--(4t) give the final parallel.
  --------------------------------------------------------------------

  exact
    proposition39_test_pascal_parallel_from_angle_chain
      Geo
      O A B C A' B' C' D'
      hAOA'
      hRayAB
      hRayAC
      hRayA'B'
      hRayA'D'
      hAB
      hOC_OA'
      hOB_OD'
      h1
      h2

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: transfer of the radial congruence
------------------------------------------------------------------------

/--
In Hilbert's special Pascal configuration,

    OC ~= OA'
    CA' || AC'

imply

    OC' ~= OA.

The proof uses the equal base angles of triangle OCA', transports
them across the parallel CA' || AC', and applies Hilbert Theorem 25
to triangle OAC' with its reversed copy.
-/
theorem proposition39_test_pascal_radial_transfer
    [HilbertEuclideanPlane Geo]
    (O A C A' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hAC : A ≠ C)
    (hA'C' : A' ≠ C')
    (hOC_OA' : Geo.Congruent O C O A')
    (hParallel : Geo.Parallel C A' A C') :
    Geo.Congruent O C' O A := by

  --------------------------------------------------------------------
  -- Reference rays and noncollinearity.
  --------------------------------------------------------------------

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAC.1

  have hRayA'A' :
      HilbertSameRay Geo O A' A' :=
    hilbert_sameRay_refl
      Geo O A' hRayA'C'.1

  have hA'OA :
      Not (PrimCollinear Geo A' O A) := by
    intro h
    exact
      hAOA'
        (PrimCollinearSymm
          Geo A' O A h)

  have hCOA' :
      Not (PrimCollinear Geo C O A') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      C A'
      hAOA'
      hRayAC
      hRayA'A'

  have hOCA' :
      Not (PrimCollinear Geo O C A') := by
    intro h
    exact
      hCOA'
        (PrimCollinearSwap
          Geo O C A' h)

  have hOA'C :
      Not (PrimCollinear Geo O A' C) := by
    intro h
    exact
      hOCA'
        (PrimCollinearRotate
          Geo O A' C h)

  --------------------------------------------------------------------
  -- Triangle OCA' is isosceles:
  --
  --     angle OCA' ~= angle OA'C.
  --------------------------------------------------------------------

  have hOA'_OC :
      Geo.Congruent O A' O C :=
    hilbert_congruent_symmetry
      Geo O C O A' hOC_OA'

  have hAngleRefl :
      Geo.AngleCongruent
        C O A'
        C O A' :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      C O A'
      hCOA'

  have hAngleO :
      Geo.AngleCongruent
        C O A'
        A' O C :=
    (Geo.angle_congruent_reverse_second
      C O A'
      C O A').mp hAngleRefl

  have hLargeBase :
      Geo.AngleCongruent
        O C A'
        O A' C :=
    (hilbert_sas_remaining_angles
      Geo
      O C A'
      O A' C
      hOCA'
      hOA'C
      hOC_OA'
      hOA'_OC
      hAngleO).1

  --------------------------------------------------------------------
  -- First corresponding-angle transport across CA' || AC':
  --
  --     angle OCA' ~= angle OAC'.
  --
  -- Use the already proved general form of relation (2t), with the
  -- two rays exchanged.
  --------------------------------------------------------------------

  have hAtC :
      Geo.AngleCongruent
        O C A'
        O A C' :=
    proposition39_test_pascal_second_angle
      Geo
      O
      A' A' C'
      A A C
      hA'OA
      hRayA'A'
      hRayA'C'
      hRayAA
      hRayAC
      hAC
      hParallel

  --------------------------------------------------------------------
  -- Reverse both parallel lines:
  --
  --     CA' || AC'  ->  A'C || C'A.
  --------------------------------------------------------------------

  have hParallelFirst :
      Geo.Parallel A' C A C' :=
    (Geo.parallel_swap_first
      C A' A C').mp hParallel

  have hParallelRev :
      Geo.Parallel A' C C' A :=
    (Geo.parallel_swap_second
      A' C A C').mp hParallelFirst

  --------------------------------------------------------------------
  -- Second corresponding-angle transport:
  --
  --     angle OA'C ~= angle OC'A.
  --------------------------------------------------------------------

  have hAtA' :
      Geo.AngleCongruent
        O A' C
        O C' A :=
    proposition39_test_pascal_second_angle
      Geo
      O
      A C A
      A' C' A'
      hAOA'
      hRayAC
      hRayAA
      hRayA'C'
      hRayA'A'
      hA'C'.symm
      hParallelRev

  --------------------------------------------------------------------
  -- Therefore triangle OAC' has equal base angles:
  --
  --     angle OAC' ~= angle OC'A.
  --------------------------------------------------------------------

  have hSmallToLarge :
      Geo.AngleCongruent
        O A C'
        O A' C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O A C'
      O C A'
      O A' C
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        O C A'
        O A C'
        hAtC)
      hLargeBase

  have hSmallBase :
      Geo.AngleCongruent
        O A C'
        O C' A :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O A C'
      O A' C
      O C' A
      hSmallToLarge
      hAtA'

  --------------------------------------------------------------------
  -- Apply Theorem 25 to triangle AC'O and its reversed copy C'AO.
  --------------------------------------------------------------------

  have hAOC' :
      Not (PrimCollinear Geo A O C') :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O A'
      A C'
      hAOA'
      hRayAA
      hRayA'C'

  have hAC'O :
      Not (PrimCollinear Geo A C' O) := by
    intro h
    exact
      hAOC'
        (PrimCollinearRotate
          Geo A C' O h)

  have hC'AO :
      Not (PrimCollinear Geo C' A O) := by
    intro h
    exact
      hAC'O
        (PrimCollinearSwap
          Geo C' A O h)

  have hBaseAAS :
      Geo.AngleCongruent
        C' A O
        A C' O :=
    (Geo.angle_congruent_reverse_second
      C' A O
      O C' A).mp
      ((Geo.angle_congruent_reverse_first
        O A C'
        O C' A).mp hSmallBase)

  have hApexRefl :
      Geo.AngleCongruent
        A O C'
        A O C' :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O C'
      hAOC'

  have hApex :
      Geo.AngleCongruent
        A O C'
        C' O A :=
    (Geo.angle_congruent_reverse_second
      A O C'
      A O C').mp hApexRefl

  have hAC'_refl :
      Geo.Congruent A C' A C' :=
    hilbert_congruent_reflexive
      Geo A C'

  have hShared :
      Geo.Congruent A C' C' A :=
    (Geo.congruent_reverse_second
      A C' A C').mp hAC'_refl

  have hSides :=
    hilbert_aas_sides
      Geo
      A C' O
      C' A O
      hAC'O
      hC'AO
      hShared
      hBaseAAS
      hApex

  --------------------------------------------------------------------
  -- hSides.1 is AO ~= C'O.  Reorient the two segments.
  --------------------------------------------------------------------

  have hC'O_AO :
      Geo.Congruent C' O A O :=
    hilbert_congruent_symmetry
      Geo A O C' O hSides.1

  have hOC'_AO :
      Geo.Congruent O C' A O :=
    (Geo.congruent_reverse_first
      C' O A O).mp hC'O_AO

  exact
    (Geo.congruent_reverse_second
      O C' A O).mp hOC'_AO

------------------------------------------------------------------------
-- Hilbert sec. 14
-- Special Pascal: radial congruence derived from the hypotheses
------------------------------------------------------------------------

/--
Hilbert's special Pascal theorem in the form matching the geometric
hypotheses.

Assume

    OC ~= OA'
    CA' || AC'
    C'B || B'C,

with A,B,C on one ray from O and A',B',C' on the other.
Then

    AB' || BA'.

The auxiliary congruence OC' ~= OA used in relation (1t) is derived
from OC ~= OA' and CA' || AC'.
-/
theorem proposition39_test_special_pascal
    [HilbertEuclideanPlane Geo]
    (O A B C A' B' C' : Geo.Point)
    (hAOA' : Not (PrimCollinear Geo A O A'))
    (hRayAB : HilbertSameRay Geo O A B)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayA'B' : HilbertSameRay Geo O A' B')
    (hRayA'C' : HilbertSameRay Geo O A' C')
    (hAB : A ≠ B)
    (hAC : A ≠ C)
    (hA'C' : A' ≠ C')
    (hB'C' : B' ≠ C')
    (hOC_OA' : Geo.Congruent O C O A')
    (hParallelCA' : Geo.Parallel C A' A C')
    (hParallelCB' : Geo.Parallel C' B B' C) :
    Geo.Parallel A B' B A' := by

  have hOC'_OA :
      Geo.Congruent O C' O A :=
    proposition39_test_pascal_radial_transfer
      Geo
      O A C A' C'
      hAOA'
      hRayAC
      hRayA'C'
      hAC
      hA'C'
      hOC_OA'
      hParallelCA'

  exact
    proposition39_test_special_pascal_core
      Geo
      O A B C A' B' C'
      hAOA'
      hRayAB
      hRayAC
      hRayA'B'
      hRayA'C'
      hAB
      hB'C'
      hOC_OA'
      hOC'_OA
      hParallelCB'

end Geometry

import CGJteamLab.HilbertGrundlagen
import CGJteamLab.HilbertBookZero
import CGJteamLab.Proposition12
import CGJteamLab.Proposition32

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


theorem proposition39_test_circle_sameRay_order
    [HilbertOrder Geo]
    (O A B : Geo.Point)
    (hRay : HilbertSameRay Geo O A B)
    (hAB : A ≠ B) :
    Geo.Between O A B ∨
    Geo.Between O B A := by

  have hOA :
      O ≠ A :=
    hRay.1.symm

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
        hAB
        hOB
        hOAB
    with hOABet | hAOB | hOBA

  · exact Or.inl hOABet

  · exact False.elim
      (hRay.2.2.2 hAOB)

  · exact Or.inr hOBA



theorem proposition39_test_circle_ray_order_cases
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D) :
    (Geo.Between O A C ∧ Geo.Between O B D) ∨
    (Geo.Between O A C ∧ Geo.Between O D B) ∨
    (Geo.Between O C A ∧ Geo.Between O B D) ∨
    (Geo.Between O C A ∧ Geo.Between O D B) := by

  rcases
      proposition39_test_circle_sameRay_order
        Geo O A C hRayAC hAC
    with hOAC | hOCA

  · rcases
        proposition39_test_circle_sameRay_order
          Geo O B D hRayBD hBD
      with hOBD | hODB

    · exact Or.inl ⟨hOAC, hOBD⟩

    · exact
        Or.inr
          (Or.inl ⟨hOAC, hODB⟩)

  · rcases
        proposition39_test_circle_sameRay_order
          Geo O B D hRayBD hBD
      with hOBD | hODB

    · exact
        Or.inr
          (Or.inr
            (Or.inl ⟨hOCA, hOBD⟩))

    · exact
        Or.inr
          (Or.inr
            (Or.inr ⟨hOCA, hODB⟩))


theorem proposition39_test_circle_inner_inner_sameSide_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine D chord ∧
      HilbertSameSide Geo A B chord := by

  have hRayCA :
      HilbertSameRay Geo O C A :=
    hilbert_sameRay_of_between
      Geo O C A hOCA

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_symm
      Geo O C A hRayCA

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨chord, hCchord, hDchord⟩

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hSame :
      HilbertSameSide Geo A B chord :=
    hilbert_third_side_endpoints_sameSide
      Geo
      O A B
      C D
      chord
      hOAB
      hOCA
      hODB
      hCchord
      hDchord

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hSame⟩

theorem proposition39_test_circle_mixed_outer_inner_oppositeSide_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine D chord ∧
      HilbertOppositeSide Geo A B chord := by

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_of_between
      Geo O A C hOAC

  have hRayDB :
    HilbertSameRay Geo O D B :=
  hilbert_sameRay_of_between
    Geo O D B hODB

  have hRayBD :
    HilbertSameRay Geo O B D :=
  hilbert_sameRay_symm
    Geo O D B hRayDB

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
    exact
      hCOD
        (PrimCollinearSwap
          Geo O C D h)

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨chord, hCchord, hDchord⟩

  --------------------------------------------------------------------
  -- O and A lie on the same side of CD, because O-A-C.
  --------------------------------------------------------------------

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O A D C
        hOAC
        hOCD
    with
    ⟨chord₁, hDchord₁, hCchord₁, hOA₁⟩

  have hChordEq :
      chord₁ = chord :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      chord₁ chord
      hCchord₁
      hDchord₁
      hCchord
      hDchord

  have hOA :
      HilbertSameSide Geo O A chord := by
    rw [← hChordEq]
    exact hOA₁

  --------------------------------------------------------------------
  -- O and B lie on opposite sides of CD, because O-D-B.
  --------------------------------------------------------------------

  have hOppOB :
      HilbertOppositeSide Geo O B chord :=
    ⟨hOA.1,
      by
        intro hBchord

        have hODBData :=
          HilbertOrder.between_incidence
            O D B hODB

        have hDB :
            D ≠ B :=
          hODBData.2.1

        have hODBcol :
            PrimCollinear Geo O D B :=
          hODBData.2.2.2.1

        have hDBO :
            PrimCollinear Geo D B O :=
          PrimCollinearCycle
            Geo O D B hODBcol

        have hOchord :
            HilbertIncidence.OnLine O chord :=
          hilbert_collinear_on_line
            Geo
            D B O
            chord
            hDB
            hDchord
            hBchord
            hDBO

        exact hOA.1 hOchord,
      ⟨D, hODB, hDchord⟩⟩

  --------------------------------------------------------------------
  -- Replace O by A inside the same half-plane.
  --------------------------------------------------------------------

  have hOppBO :
      HilbertOppositeSide Geo B O chord :=
    hilbert_oppositeSide_symm
      Geo O B chord hOppOB

  have hOppBA :
      HilbertOppositeSide Geo B A chord :=
    hilbert_oppositeSide_transport_right
      Geo
      B O A
      chord
      hOppBO
      hOA

  have hOppAB :
      HilbertOppositeSide Geo A B chord :=
    hilbert_oppositeSide_symm
      Geo B A chord hOppBA

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hOppAB⟩

theorem proposition39_test_circle_mixed_inner_outer_oppositeSide_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine D chord ∧
      HilbertOppositeSide Geo A B chord := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  rcases
      proposition39_test_circle_mixed_outer_inner_oppositeSide_chord
        Geo
        O B D A C
        hBOA
        hOBD
        hOCA
    with
    ⟨chord,
      hDchord,
      hCchord,
      hOppBA⟩

  have hOppAB :
      HilbertOppositeSide Geo A B chord :=
    hilbert_oppositeSide_symm
      Geo B A chord hOppBA

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hOppAB⟩

theorem proposition39_test_opposite_equal_extension
    [HilbertCongruence Geo]
    (D H : Geo.Point)
    (hDH : D ≠ H) :
    ∃ E : Geo.Point,
      Geo.Between D H E ∧
      Geo.Congruent H E H D := by

  rcases
      HilbertOrder.between_extension
        D H hDH
    with
    ⟨S, hDHS⟩

  have hHS :
      H ≠ S :=
    (HilbertOrder.between_incidence
      D H S hDHS).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        H D
        H S
        hHS
    with
    ⟨E, hRaySE, hHE_HD⟩

  have hRayHDD :
      HilbertSameRay Geo H D D :=
    hilbert_sameRay_refl
      Geo H D hDH

  have hDHE :
      Geo.Between D H E :=
    hilbert_between_transport_sameRays
      Geo
      D H S
      D E
      hDHS
      hRayHDD
      hRaySE

  exact
    ⟨E,
      hDHE,
      hHE_HD⟩

theorem proposition39_test_reflection_distance_sas
    [HilbertCongruence Geo]
    (K D H E : Geo.Point)
    (hHKD : Not (PrimCollinear Geo H K D))
    (hHKE : Not (PrimCollinear Geo H K E))
    (hHE_HD : Geo.Congruent H E H D)
    (hAngle :
      Geo.AngleCongruent K H D K H E) :
    Geo.Congruent K D K E := by

  have hHK_HK :
      Geo.Congruent H K H K :=
    hilbert_congruent_reflexive
      Geo H K

  have hHD_HE :
      Geo.Congruent H D H E :=
    hilbert_congruent_symmetry
      Geo H E H D hHE_HD

  have hSAS :=
    SAS
      Geo
      H K D
      H K E
      hHKD
      hHKE
      hHK_HK
      hAngle
      hHD_HE

  exact hSAS.sideBC

theorem proposition39_test_right_angle_opposite_extension
    [HilbertCongruence Geo]
    (D H E K : Geo.Point)
    (hDHE : Geo.Between D H E)
    (hDHK : Not (PrimCollinear Geo D H K))
    (hRight : HilbertRightAngle Geo D H K) :
    Geo.AngleCongruent K H D K H E := by

  rcases hRight with
    ⟨T, hDHT, hDHK_KHT⟩

  have hRefl :
      Geo.AngleCongruent D H K D H K :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      D H K
      hDHK

  have hKHT_KHE :
      Geo.AngleCongruent K H T K H E :=
    hilbert_adjacent_angles_congruent
      Geo
      D H K T
      D H K E
      hDHT
      hDHE
      hDHK
      hDHK
      hRefl

  have hKHD_KHT :
      Geo.AngleCongruent K H D K H T :=
    (Geo.angle_congruent_reverse_first
      D H K
      K H T).mp hDHK_KHT

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K H D
      K H T
      K H E
      hKHD_KHT
      hKHT_KHE

theorem proposition39_test_reflection_preserves_distance
    [HilbertCongruence Geo]
    (K D H E : Geo.Point)
    (hDHE : Geo.Between D H E)
    (hHE_HD : Geo.Congruent H E H D)
    (hDHK : Not (PrimCollinear Geo D H K))
    (hRight : HilbertRightAngle Geo D H K) :
    Geo.Congruent K D K E := by

  have hHKD :
      Not (PrimCollinear Geo H K D) := by
    intro h
    exact
      hDHK
        (PrimCollinearCycle
          Geo K D H
          (PrimCollinearCycle
            Geo H K D h))

  have hHE :
      H ≠ E :=
    (HilbertOrder.between_incidence
      D H E hDHE).2.1

  have hDHEcol :
      PrimCollinear Geo D H E :=
    (HilbertOrder.between_incidence
      D H E hDHE).2.2.2.1

  have hHKE :
      Not (PrimCollinear Geo H K E) := by
    intro hHKEcol

    have hHEK :
        PrimCollinear Geo H E K :=
      PrimCollinearRotate
        Geo H K E hHKEcol

    have hDHK' :
        PrimCollinear Geo D H K :=
      hilbert_primCollinear_trans
        Geo
        D H E K
        hHE
        hDHEcol
        hHEK

    exact hDHK hDHK'

  have hAngle :
      Geo.AngleCongruent K H D K H E :=
    proposition39_test_right_angle_opposite_extension
      Geo
      D H E K
      hDHE
      hDHK
      hRight

  exact
    proposition39_test_reflection_distance_sas
      Geo
      K D H E
      hHKD
      hHKE
      hHE_HD
      hAngle

theorem proposition39_test_reflected_circle_point
    [HilbertCongruence Geo]
    (K D H : Geo.Point)
    (hDH : D ≠ H)
    (hDHK : Not (PrimCollinear Geo D H K))
    (hRight : HilbertRightAngle Geo D H K) :
    ∃ E : Geo.Point,
      Geo.Between D H E ∧
      Geo.Congruent H E H D ∧
      Geo.Congruent K D K E := by

  rcases
      proposition39_test_opposite_equal_extension
        Geo
        D H
        hDH
    with
    ⟨E, hDHE, hHE_HD⟩

  have hKD_KE :
      Geo.Congruent K D K E :=
    proposition39_test_reflection_preserves_distance
      Geo
      K D H E
      hDHE
      hHE_HD
      hDHK
      hRight

  exact
    ⟨E,
      hDHE,
      hHE_HD,
      hKD_KE⟩

theorem proposition39_test_right_angle_collinear_first
    [HilbertCongruence Geo]
    (D R H K : Geo.Point)
    (hHD : H ≠ D)
    (hHR : H ≠ R)
    (hHDR : PrimCollinear Geo H D R)
    (hDHK : Not (PrimCollinear Geo D H K))
    (hRHK : Not (PrimCollinear Geo R H K))
    (hRightR : HilbertRightAngle Geo R H K) :
    HilbertRightAngle Geo D H K := by

  have hKHR :
      Not (PrimCollinear Geo K H R) := by
    intro h

    exact
      hRHK
        (PrimCollinearSymm
          Geo K H R h)

  have hRightKHR :
      HilbertRightAngle Geo K H R :=
    proposition39_test_right_angle_swap
      Geo
      R H K
      hRHK
      hRightR

  have hRightKHD :
      HilbertRightAngle Geo K H D :=
    proposition39_test_right_angle_collinear_second
      Geo
      K H D R
      hHD
      hHR
      hHDR
      hKHR
      hRightKHR

  have hKHD :
      Not (PrimCollinear Geo K H D) := by
    intro h

    exact
      hDHK
        (PrimCollinearSymm
          Geo K H D h)

  exact
    proposition39_test_right_angle_swap
      Geo
      K H D
      hKHD
      hRightKHD

theorem proposition39_test_reflected_circle_point_from_perpendicular
    [HilbertCongruence Geo]
    (K D H R : Geo.Point)
    (base : Geo.Line)
    (hDbase : HilbertIncidence.OnLine D base)
    (hHbase : HilbertIncidence.OnLine H base)
    (hRbase : HilbertIncidence.OnLine R base)
    (hKbase : Not (HilbertIncidence.OnLine K base))
    (hDH : D ≠ H)
    (hRightR : HilbertRightAngle Geo R H K) :
    ∃ E : Geo.Point,
      Geo.Between D H E ∧
      Geo.Congruent H E H D ∧
      Geo.Congruent K D K E := by

  rcases hRightR with
    ⟨T, hRHT, hRightEq⟩

  have hRH :
      R ≠ H :=
    (HilbertOrder.between_incidence
      R H T hRHT).1

  have hRightR' :
      HilbertRightAngle Geo R H K :=
    ⟨T, hRHT, hRightEq⟩

  have hDHK :
      Not (PrimCollinear Geo D H K) :=
    hilbert_not_collinear_of_off_line
      Geo
      D H K
      base
      hDH
      hDbase
      hHbase
      hKbase

  have hRHK :
      Not (PrimCollinear Geo R H K) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H K
      base
      hRH
      hRbase
      hHbase
      hKbase

  have hHDR :
      PrimCollinear Geo H D R :=
    ⟨base,
      hHbase,
      hDbase,
      hRbase⟩

  have hRightD :
      HilbertRightAngle Geo D H K :=
    proposition39_test_right_angle_collinear_first
      Geo
      D R H K
      hDH.symm
      hRH.symm
      hHDR
      hDHK
      hRHK
      hRightR'

  exact
    proposition39_test_reflected_circle_point
      Geo
      K D H
      hDH
      hDHK
      hRightD

theorem proposition39_test_circle_line_second_point_or_tangent
    [HilbertCongruence Geo]
    (K O D : Geo.Point)
    (base : Geo.Line)
    (hOD : O ≠ D)
    (hObase : HilbertIncidence.OnLine O base)
    (hDbase : HilbertIncidence.OnLine D base)
    (hKbase : Not (HilbertIncidence.OnLine K base)) :
    ∃ H R : Geo.Point,
      HilbertIncidence.OnLine H base ∧
      HilbertIncidence.OnLine R base ∧
      HilbertRightAngle Geo R H K ∧
      (
        H = D
        ∨
        ∃ E : Geo.Point,
          Geo.Between D H E ∧
          Geo.Congruent H E H D ∧
          Geo.Congruent K D K E
      ) := by

  rcases
      hilbert_perpendicular_from_point_exists
        Geo
        O D K
        base
        hOD
        hObase
        hDbase
        hKbase
    with
    ⟨H, R, hHbase, hRbase, hRightR⟩

  refine
    ⟨H,
      R,
      hHbase,
      hRbase,
      hRightR,
      ?_⟩

  by_cases hHD : H = D

  · exact Or.inl hHD

  · have hDH :
        D ≠ H :=
      Ne.symm hHD

    have hSecond :=
      proposition39_test_reflected_circle_point_from_perpendicular
        Geo
        K D H R
        base
        hDbase
        hHbase
        hRbase
        hKbase
        hDH
        hRightR

    exact Or.inr hSecond

theorem proposition39_test_circle_chord_midpoint_perpendicular
    [HilbertCongruence Geo]
    (A M C K : Geo.Point)
    (hAMC : Geo.Between A M C)
    (hAM_MC : Geo.Congruent A M M C)
    (hKA_KC : Geo.Congruent K A K C)
    (hAMK : Not (PrimCollinear Geo A M K)) :
    HilbertRightAngle Geo A M K := by

  have hMAK :
      Not (PrimCollinear Geo M A K) := by
    intro h

    exact
      hAMK
        (PrimCollinearSwap
          Geo M A K h)

  have hMA_MC :
      Geo.Congruent M A M C :=
    (Geo.congruent_reverse_first
      A M
      M C).mp hAM_MC

  have hAK_KC :
      Geo.Congruent A K K C :=
    (Geo.congruent_reverse_first
      K A
      K C).mp hKA_KC

  have hAK_CK :
      Geo.Congruent A K C K :=
    (Geo.congruent_reverse_second
      A K
      K C).mp hAK_KC

  have hMK_MK :
      Geo.Congruent M K M K :=
    hilbert_congruent_reflexive
      Geo M K

  have hSSS :=
    HilbertSSS
      Geo
      M A K
      M C K
      hMAK
      hMA_MC
      hAK_CK
      hMK_MK

  have hAMK_CMK :
      Geo.AngleCongruent A M K C M K :=
    hSSS.2.angleA

  have hAMK_KMC :
      Geo.AngleCongruent A M K K M C :=
    (Geo.angle_congruent_reverse_second
      A M K
      C M K).mp hAMK_CMK

  exact
    ⟨C,
      hAMC,
      hAMK_KMC⟩


theorem proposition39_test_circle_chord_midpoint
    [HilbertCongruence Geo]
    (K R A C : Geo.Point)
    (hA : HilbertCircle Geo K R A)
    (hC : HilbertCircle Geo K R C)
    (hACK : Not (PrimCollinear Geo A C K)) :
    ∃ M : Geo.Point,
      Geo.Between A M C ∧
      Geo.Congruent A M M C ∧
      HilbertRightAngle Geo A M K := by

  have hAC :
      A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C K hACK

  rcases
      hilbert_midpoint_exists
        Geo A C hAC
    with
    ⟨M, hAMC, hAM_MC⟩

  have hAMCcol :
      PrimCollinear Geo A M C :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.1

  have hAM :
      A ≠ M :=
    (HilbertOrder.between_incidence
      A M C hAMC).1

  have hAMK :
      Not (PrimCollinear Geo A M K) := by
    intro hAMKcol

    rcases hAMKcol with
      ⟨line, hAline, hMline, hKline⟩

    have hCline :
        HilbertIncidence.OnLine C line :=
      hilbert_collinear_on_line
        Geo
        A M C
        line
        hAM
        hAline
        hMline
        hAMCcol

    exact
      hACK
        ⟨line,
          hAline,
          hCline,
          hKline⟩

  unfold HilbertCircle at hA hC

  have hKR_KC :
      Geo.Congruent K R K C :=
    hilbert_congruent_symmetry
      Geo
      K C
      K R
      hC

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_congruent_transitivity
      Geo
      K A
      K R
      K C
      hA
      hKR_KC

  have hRight :
      HilbertRightAngle Geo A M K :=
    proposition39_test_circle_chord_midpoint_perpendicular
      Geo
      A M C K
      hAMC
      hAM_MC
      hKA_KC
      hAMK

  exact
    ⟨M,
      hAMC,
      hAM_MC,
      hRight⟩

theorem proposition39_test_circle_chord_perpendicular_bisector
    [HilbertCongruence Geo]
    (K R A C : Geo.Point)
    (hA : HilbertCircle Geo K R A)
    (hC : HilbertCircle Geo K R C)
    (hACK : Not (PrimCollinear Geo A C K)) :
    ∃ M : Geo.Point,
    ∃ perp : Geo.Line,
      Geo.Between A M C ∧
      Geo.Congruent A M M C ∧
      HilbertIncidence.OnLine M perp ∧
      HilbertIncidence.OnLine K perp ∧
      HilbertRightAngle Geo A M K := by

  rcases
      proposition39_test_circle_chord_midpoint
        Geo
        K R A C
        hA
        hC
        hACK
    with
    ⟨M, hAMC, hAM_MC, hRight⟩

  have hAMCcol :
      PrimCollinear Geo A M C :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.1

  have hMK :
      M ≠ K := by
    intro hEq

    subst K

    rcases hAMCcol with
      ⟨line, hAline, hMline, hCline⟩

    exact
      hACK
        ⟨line,
          hAline,
          hCline,
          hMline⟩

  rcases
      HilbertPlaneIncidence.line_through
        M K hMK
    with
    ⟨perp, hMperp, hKperp⟩

  exact
    ⟨M,
      perp,
      hAMC,
      hAM_MC,
      hMperp,
      hKperp,
      hRight⟩

theorem proposition39_test_circle_chord_axis
    [HilbertCongruence Geo]
    (K R A C : Geo.Point)
    (hA : HilbertCircle Geo K R A)
    (hC : HilbertCircle Geo K R C)
    (hACK : Not (PrimCollinear Geo A C K)) :
    ∃ M : Geo.Point,
    ∃ perp : Geo.Line,
      Geo.Between A M C ∧
      Geo.Congruent A M M C ∧
      HilbertIncidence.OnLine M perp ∧
      HilbertIncidence.OnLine K perp ∧
      HilbertRightAngle Geo A M K ∧
      ∀ P : Geo.Point,
        HilbertIncidence.OnLine P perp →
        Geo.Congruent A P C P := by

  rcases
      proposition39_test_circle_chord_perpendicular_bisector
        Geo
        K R A C
        hA
        hC
        hACK
    with
    ⟨M,
      perp,
      hAMC,
      hAM_MC,
      hMperp,
      hKperp,
      hRight⟩

  have hAMCcol :
      PrimCollinear Geo A M C :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.1

  have hAM :
      A ≠ M :=
    (HilbertOrder.between_incidence
      A M C hAMC).1

  have hAMK :
      Not (PrimCollinear Geo A M K) := by

    intro hAMKcol

    rcases hAMKcol with
      ⟨line, hAline, hMline, hKline⟩

    have hCline :
        HilbertIncidence.OnLine C line :=
      hilbert_collinear_on_line
        Geo
        A M C
        line
        hAM
        hAline
        hMline
        hAMCcol

    exact
      hACK
        ⟨line,
          hAline,
          hCline,
          hKline⟩

  refine
    ⟨M,
      perp,
      hAMC,
      hAM_MC,
      hMperp,
      hKperp,
      hRight,
      ?_⟩

  intro P hPperp

  exact
    proposition39_test_perpendicular_bisector_equidistant
      Geo
      A M C K P
      perp
      hAMC
      hAM_MC
      hMperp
      hKperp
      hPperp
      hAMK
      hRight

theorem proposition39_test_circle_radii_base_angles
    [HilbertCongruence Geo]
    (K R A C : Geo.Point)
    (hA : HilbertCircle Geo K R A)
    (hC : HilbertCircle Geo K R C)
    (hKAC : Not (PrimCollinear Geo K A C)) :
    Geo.AngleCongruent K A C K C A := by

  unfold HilbertCircle at hA hC

  have hKR_KC :
      Geo.Congruent K R K C :=
    hilbert_congruent_symmetry
      Geo
      K C
      K R
      hC

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_congruent_transitivity
      Geo
      K A
      K R
      K C
      hA
      hKR_KC

  have hAK_CK :
      Geo.Congruent A K C K :=
    (Geo.congruent_reverse_first
      K A
      C K).mp
      ((Geo.congruent_reverse_second
        K A
        K C).mp hKA_KC)

  have hKC_KA :
      Geo.Congruent K C K A :=
    hilbert_congruent_symmetry
      Geo
      K A
      K C
      hKA_KC

  have hAC_CA :
      Geo.Congruent A C C A :=
    (Geo.congruent_reverse_second
      A C
      A C).mp
      (hilbert_congruent_reflexive
        Geo A C)

  have hAKC :
      Not (PrimCollinear Geo A K C) := by
    intro h
    exact
      hKAC
        (PrimCollinearSwap
          Geo A K C h)

  have hSSS :=
    HilbertSSS
      Geo
      A K C
      C K A
      hAKC
      hAK_CK
      hKC_KA
      hAC_CA

  exact hSSS.2.angleA

theorem proposition39_test_concyclic4_center_circle
    [HilbertCongruence Geo]
    (A C D B : Geo.Point)
    (hCyclic : HilbertConcyclic4 Geo A C D B) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D ∧
      HilbertCircle Geo K A B := by

  rcases hCyclic with
    ⟨K,
      hKA_KC,
      hKA_KD,
      hKA_KB⟩

  have hKA_KA :
      Geo.Congruent K A K A :=
    hilbert_congruent_reflexive
      Geo K A

  have hKC_KA :
      Geo.Congruent K C K A :=
    hilbert_congruent_symmetry
      Geo
      K A
      K C
      hKA_KC

  have hKD_KA :
      Geo.Congruent K D K A :=
    hilbert_congruent_symmetry
      Geo
      K A
      K D
      hKA_KD

  have hKB_KA :
      Geo.Congruent K B K A :=
    hilbert_congruent_symmetry
      Geo
      K A
      K B
      hKA_KB

  unfold HilbertCircle

  exact
    ⟨K,
      hKA_KA,
      hKC_KA,
      hKD_KA,
      hKB_KA⟩

theorem proposition39_test_concyclic4_radius_data
    [HilbertCongruence Geo]
    (A C D B : Geo.Point)
    (hCyclic : HilbertConcyclic4 Geo A C D B) :
    ∃ K : Geo.Point,
      Geo.Congruent K A K C ∧
      Geo.Congruent K A K D ∧
      Geo.Congruent K A K B ∧
      Geo.Congruent K C K D ∧
      Geo.Congruent K C K B ∧
      Geo.Congruent K D K B := by

  rcases
      proposition39_test_concyclic4_center_circle
        Geo
        A C D B
        hCyclic
    with
    ⟨K, hA, hC, hD, hB⟩

  unfold HilbertCircle at hA hC hD hB

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_congruent_symmetry
      Geo
      K C
      K A
      hC

  have hKA_KD :
      Geo.Congruent K A K D :=
    hilbert_congruent_symmetry
      Geo
      K D
      K A
      hD

  have hKA_KB :
      Geo.Congruent K A K B :=
    hilbert_congruent_symmetry
      Geo
      K B
      K A
      hB

  have hKC_KD :
      Geo.Congruent K C K D :=
    hilbert_congruent_transitivity
      Geo
      K C
      K A
      K D
      hC
      hKA_KD

  have hKC_KB :
      Geo.Congruent K C K B :=
    hilbert_congruent_transitivity
      Geo
      K C
      K A
      K B
      hC
      hKA_KB

  have hKD_KB :
      Geo.Congruent K D K B :=
    hilbert_congruent_transitivity
      Geo
      K D
      K A
      K B
      hD
      hKA_KB

  exact
    ⟨K,
      hKA_KC,
      hKA_KD,
      hKA_KB,
      hKC_KD,
      hKC_KB,
      hKD_KB⟩

theorem proposition39_test_concyclic4_base_angle_data
    [HilbertCongruence Geo]
    (A C D B : Geo.Point)
    (hCyclic : HilbertConcyclic4 Geo A C D B) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D ∧
      HilbertCircle Geo K A B ∧
      (
        Not (PrimCollinear Geo K C B) →
        Geo.AngleCongruent K C B K B C
      ) ∧
      (
        Not (PrimCollinear Geo K C D) →
        Geo.AngleCongruent K C D K D C
      ) := by

  rcases
      proposition39_test_concyclic4_center_circle
        Geo
        A C D B
        hCyclic
    with
    ⟨K, hA, hC, hD, hB⟩

  have hBaseCB :
      Not (PrimCollinear Geo K C B) →
      Geo.AngleCongruent K C B K B C := by

    intro hKCB

    exact
      proposition39_test_circle_radii_base_angles
        Geo
        K A C B
        hC
        hB
        hKCB

  have hBaseCD :
      Not (PrimCollinear Geo K C D) →
      Geo.AngleCongruent K C D K D C := by

    intro hKCD

    exact
      proposition39_test_circle_radii_base_angles
        Geo
        K A C D
        hC
        hD
        hKCD

  exact
    ⟨K,
      hC,
      hD,
      hB,
      hBaseCB,
      hBaseCD⟩

theorem proposition39_test_concyclic4_all_base_angles
    [HilbertCongruence Geo]
    (A C D B : Geo.Point)
    (hCyclic : HilbertConcyclic4 Geo A C D B) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D ∧
      HilbertCircle Geo K A B ∧
      (
        Not (PrimCollinear Geo K C B) →
        Geo.AngleCongruent K C B K B C
      ) ∧
      (
        Not (PrimCollinear Geo K D B) →
        Geo.AngleCongruent K D B K B D
      ) ∧
      (
        Not (PrimCollinear Geo K A C) →
        Geo.AngleCongruent K A C K C A
      ) ∧
      (
        Not (PrimCollinear Geo K A B) →
        Geo.AngleCongruent K A B K B A
      ) := by

  rcases
      proposition39_test_concyclic4_center_circle
        Geo
        A C D B
        hCyclic
    with
    ⟨K, hA, hC, hD, hB⟩

  have hBaseCB :
      Not (PrimCollinear Geo K C B) →
      Geo.AngleCongruent K C B K B C := by
    intro hKCB

    exact
      proposition39_test_circle_radii_base_angles
        Geo
        K A C B
        hC
        hB
        hKCB

  have hBaseDB :
      Not (PrimCollinear Geo K D B) →
      Geo.AngleCongruent K D B K B D := by
    intro hKDB

    exact
      proposition39_test_circle_radii_base_angles
        Geo
        K A D B
        hD
        hB
        hKDB

  have hBaseAC :
      Not (PrimCollinear Geo K A C) →
      Geo.AngleCongruent K A C K C A := by
    intro hKAC

    exact
      proposition39_test_circle_radii_base_angles
        Geo
        K A A C
        hA
        hC
        hKAC

  have hBaseAB :
      Not (PrimCollinear Geo K A B) →
      Geo.AngleCongruent K A B K B A := by
    intro hKAB

    exact
      proposition39_test_circle_radii_base_angles
        Geo
        K A A B
        hA
        hB
        hKAB

  exact
    ⟨K,
      hA,
      hC,
      hD,
      hB,
      hBaseCB,
      hBaseDB,
      hBaseAC,
      hBaseAB⟩

theorem proposition39_test_isosceles_exterior_bisected
    [HilbertEuclideanPlane Geo]
    (C D K E : Geo.Point)
    (hCDK : Not (PrimCollinear Geo C D K))
    (hDKE : Geo.Between D K E)
    (hBase :
      Geo.AngleCongruent
        D C K
        C D K) :
    ∃ R : Geo.Point,
      Geo.Between C R E ∧
      Geo.AngleCongruent D C K C K R ∧
      Geo.AngleCongruent C D K R K E ∧
      Geo.AngleCongruent C K R R K E := by

  have hExterior :=
    euclid_proposition_32_exterior
      C D K E
      hCDK
      hDKE

  rcases hExterior with
    ⟨R,
      hCRE,
      hDCK_CKR,
      hCDK_RKE⟩

  have hCKR_DCK :
      Geo.AngleCongruent
        C K R
        D C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D C K
      C K R
      hDCK_CKR

  have hCKR_CDK :
      Geo.AngleCongruent
        C K R
        C D K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C K R
      D C K
      C D K
      hCKR_DCK
      hBase

  have hCKR_RKE :
      Geo.AngleCongruent
        C K R
        R K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C K R
      C D K
      R K E
      hCKR_CDK
      hCDK_RKE

  exact
    ⟨R,
      hCRE,
      hDCK_CKR,
      hCDK_RKE,
      hCKR_RKE⟩

theorem proposition39_test_circle_central_exterior_bisected
    [HilbertEuclideanPlane Geo]
    (K A C D E : Geo.Point)
    (hC : HilbertCircle Geo K A C)
    (hD : HilbertCircle Geo K A D)
    (hCDK : Not (PrimCollinear Geo C D K))
    (hDKE : Geo.Between D K E) :
    ∃ R : Geo.Point,
      Geo.Between C R E ∧
      Geo.AngleCongruent D C K C K R ∧
      Geo.AngleCongruent C D K R K E ∧
      Geo.AngleCongruent C K R R K E := by

  have hKCD :
      Not (PrimCollinear Geo K C D) := by
    intro h
    exact
      hCDK
        (PrimCollinearCycle
          Geo K C D h)

  have hBaseRaw :
      Geo.AngleCongruent
        K C D
        K D C :=
    proposition39_test_circle_radii_base_angles
      Geo
      K A C D
      hC
      hD
      hKCD

  have hBase1 :
      Geo.AngleCongruent
        D C K
        K D C :=
    (Geo.angle_congruent_reverse_first
      K C D
      K D C).mp hBaseRaw

  have hBase :
      Geo.AngleCongruent
        D C K
        C D K :=
    (Geo.angle_congruent_reverse_second
      D C K
      K D C).mp hBase1

  exact
    proposition39_test_isosceles_exterior_bisected
      Geo
      C D K E
      hCDK
      hDKE
      hBase

theorem proposition39_test_circle_two_central_exterior_bisectors
    [HilbertEuclideanPlane Geo]
    (K A C D B E : Geo.Point)
    (hC : HilbertCircle Geo K A C)
    (hD : HilbertCircle Geo K A D)
    (hB : HilbertCircle Geo K A B)
    (hCBK : Not (PrimCollinear Geo C B K))
    (hDBK : Not (PrimCollinear Geo D B K))
    (hBKE : Geo.Between B K E) :
    ∃ R S : Geo.Point,
      Geo.Between C R E ∧
      Geo.Between D S E ∧
      Geo.AngleCongruent B C K C K R ∧
      Geo.AngleCongruent C B K R K E ∧
      Geo.AngleCongruent C K R R K E ∧
      Geo.AngleCongruent B D K D K S ∧
      Geo.AngleCongruent D B K S K E ∧
      Geo.AngleCongruent D K S S K E := by

  rcases
      proposition39_test_circle_central_exterior_bisected
        Geo
        K A C B E
        hC
        hB
        hCBK
        hBKE
    with
    ⟨R,
      hCRE,
      hBCK_CKR,
      hCBK_RKE,
      hCKR_RKE⟩

  rcases
      proposition39_test_circle_central_exterior_bisected
        Geo
        K A D B E
        hD
        hB
        hDBK
        hBKE
    with
    ⟨S,
      hDSE,
      hBDK_DKS,
      hDBK_SKE,
      hDKS_SKE⟩

  exact
    ⟨R,
      S,
      hCRE,
      hDSE,
      hBCK_CKR,
      hCBK_RKE,
      hCKR_RKE,
      hBDK_DKS,
      hDBK_SKE,
      hDKS_SKE⟩

theorem proposition39_test_circle_inscribed_angle_components
    [HilbertEuclideanPlane Geo]
    (K A C D B E : Geo.Point)
    (hC : HilbertCircle Geo K A C)
    (hD : HilbertCircle Geo K A D)
    (hB : HilbertCircle Geo K A B)
    (hCBK : Not (PrimCollinear Geo C B K))
    (hDBK : Not (PrimCollinear Geo D B K))
    (hBKE : Geo.Between B K E) :
    ∃ R S : Geo.Point,
      Geo.Between C R E ∧
      Geo.Between D S E ∧
      Geo.AngleCongruent C B K R K E ∧
      Geo.AngleCongruent K B D S K E ∧
      Geo.AngleCongruent C K R R K E ∧
      Geo.AngleCongruent D K S S K E := by

  rcases
      proposition39_test_circle_two_central_exterior_bisectors
        Geo
        K A C D B E
        hC
        hD
        hB
        hCBK
        hDBK
        hBKE
    with
    ⟨R,
      S,
      hCRE,
      hDSE,
      hBCK_CKR,
      hCBK_RKE,
      hCKR_RKE,
      hBDK_DKS,
      hDBK_SKE,
      hDKS_SKE⟩

  have hKBD_SKE :
      Geo.AngleCongruent
        K B D
        S K E :=
    (Geo.angle_congruent_reverse_first
      D B K
      S K E).mp hDBK_SKE

  exact
    ⟨R,
      S,
      hCRE,
      hDSE,
      hCBK_RKE,
      hKBD_SKE,
      hCKR_RKE,
      hDKS_SKE⟩

theorem proposition39_test_circle_inscribed_components_to_central_halves
    [HilbertEuclideanPlane Geo]
    (K A C D B E : Geo.Point)
    (hC : HilbertCircle Geo K A C)
    (hD : HilbertCircle Geo K A D)
    (hB : HilbertCircle Geo K A B)
    (hCBK : Not (PrimCollinear Geo C B K))
    (hDBK : Not (PrimCollinear Geo D B K))
    (hBKE : Geo.Between B K E) :
    ∃ R S : Geo.Point,
      Geo.Between C R E ∧
      Geo.Between D S E ∧
      Geo.AngleCongruent C B K C K R ∧
      Geo.AngleCongruent K B D D K S := by

  rcases
      proposition39_test_circle_inscribed_angle_components
        Geo
        K A C D B E
        hC
        hD
        hB
        hCBK
        hDBK
        hBKE
    with
    ⟨R,
      S,
      hCRE,
      hDSE,
      hCBK_RKE,
      hKBD_SKE,
      hCKR_RKE,
      hDKS_SKE⟩

  have hRKE_CKR :
      Geo.AngleCongruent
        R K E
        C K R :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C K R
      R K E
      hCKR_RKE

  have hCBK_CKR :
      Geo.AngleCongruent
        C B K
        C K R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C B K
      R K E
      C K R
      hCBK_RKE
      hRKE_CKR

  have hSKE_DKS :
      Geo.AngleCongruent
        S K E
        D K S :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D K S
      S K E
      hDKS_SKE

  have hKBD_DKS :
      Geo.AngleCongruent
        K B D
        D K S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K B D
      S K E
      D K S
      hKBD_SKE
      hSKE_DKS

  exact
    ⟨R,
      S,
      hCRE,
      hDSE,
      hCBK_CKR,
      hKBD_DKS⟩

theorem proposition39_test_circle_central_exterior_double
    [HilbertEuclideanPlane Geo]
    (K A C B E : Geo.Point)
    (hC : HilbertCircle Geo K A C)
    (hB : HilbertCircle Geo K A B)
    (hCBK : Not (PrimCollinear Geo C B K))
    (hBKE : Geo.Between B K E) :
    ∃ R : Geo.Point,
      Geo.Between C R E ∧
      Geo.AngleCongruent C K R C B K ∧
      Geo.AngleCongruent R K E C B K := by

  rcases
      proposition39_test_circle_central_exterior_bisected
        Geo
        K A C B E
        hC
        hB
        hCBK
        hBKE
    with
    ⟨R,
      hCRE,
      _hBCK_CKR,
      hCBK_RKE,
      hCKR_RKE⟩

  have hRKE_CBK :
      Geo.AngleCongruent
        R K E
        C B K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C B K
      R K E
      hCBK_RKE

  have hCKR_CBK :
      Geo.AngleCongruent
        C K R
        C B K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C K R
      R K E
      C B K
      hCKR_RKE
      hRKE_CBK

  exact
    ⟨R,
      hCRE,
      hCKR_CBK,
      hRKE_CBK⟩

theorem proposition39_test_circle_outer_outer_oppositeSide_other_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine B chord ∧
      HilbertOppositeSide Geo A D chord := by

  have hAO :
      A ≠ O :=
    (HilbertOrder.between_incidence
      O A C hOAC).1.symm

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hAO

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_of_between
      Geo O B D hOBD

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  exact
    proposition39_test_circle_mixed_outer_inner_oppositeSide_chord
      Geo
      O A C D B
      hAOD
      hOAC
      hOBD

theorem proposition39_test_circle_inner_inner_oppositeSide_other_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine B chord ∧
      HilbertOppositeSide Geo A D chord := by

  have hAO :
      A ≠ O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.1.symm

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hAO

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  exact
    proposition39_test_circle_mixed_inner_outer_oppositeSide_chord
      Geo
      O A C D B
      hAOD
      hOCA
      hODB

theorem proposition39_test_circle_mixed_outer_inner_sameSide_other_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine B chord ∧
      HilbertSameSide Geo A D chord := by

  have hAO :
      A ≠ O :=
    (HilbertOrder.between_incidence
      O A C hOAC).1.symm

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hAO

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  exact
    proposition39_test_circle_outer_outer_sameSide_chord
      Geo
      O A C D B
      hAOD
      hOAC
      hODB

theorem proposition39_test_circle_mixed_inner_outer_sameSide_other_chord
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      HilbertIncidence.OnLine C chord ∧
      HilbertIncidence.OnLine B chord ∧
      HilbertSameSide Geo A D chord := by

  have hAO :
      A ≠ O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.1.symm

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hAO

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_of_between
      Geo O B D hOBD

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  exact
    proposition39_test_circle_inner_inner_sameSide_chord
      Geo
      O A C D B
      hAOD
      hOCA
      hOBD

theorem proposition39_test_circle_other_chord_side_classification
    [HilbertOrder Geo]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D) :
    (
      ∃ chord : Geo.Line,
        HilbertIncidence.OnLine C chord ∧
        HilbertIncidence.OnLine B chord ∧
        HilbertOppositeSide Geo A D chord
    )
    ∨
    (
      ∃ chord : Geo.Line,
        HilbertIncidence.OnLine C chord ∧
        HilbertIncidence.OnLine B chord ∧
        HilbertSameSide Geo A D chord
    ) := by

  rcases
      proposition39_test_circle_ray_order_cases
        Geo
        O A C B D
        hRayAC
        hRayBD
        hAC
        hBD
    with
    hOO | hRest

  ----------------------------------------------------------------------
  -- O-A-C, O-B-D
  ----------------------------------------------------------------------

  · rcases hOO with ⟨hOAC, hOBD⟩

    left

    exact
      proposition39_test_circle_outer_outer_oppositeSide_other_chord
        Geo
        O A C B D
        hAOB
        hOAC
        hOBD

  · rcases hRest with
      hOI | hRest

    --------------------------------------------------------------------
    -- O-A-C, O-D-B
    --------------------------------------------------------------------

    · rcases hOI with ⟨hOAC, hODB⟩

      right

      exact
        proposition39_test_circle_mixed_outer_inner_sameSide_other_chord
          Geo
          O A C B D
          hAOB
          hOAC
          hODB

    · rcases hRest with
        hIO | hII

      ------------------------------------------------------------------
      -- O-C-A, O-B-D
      ------------------------------------------------------------------

      · rcases hIO with ⟨hOCA, hOBD⟩

        right

        exact
          proposition39_test_circle_mixed_inner_outer_sameSide_other_chord
            Geo
            O A C B D
            hAOB
            hOCA
            hOBD

      ------------------------------------------------------------------
      -- O-C-A, O-D-B
      ------------------------------------------------------------------

      · rcases hII with ⟨hOCA, hODB⟩

        left

        exact
          proposition39_test_circle_inner_inner_oppositeSide_other_chord
            Geo
            O A C B D
            hAOB
            hOCA
            hODB

theorem proposition39_test_angle_unique_same_side_ray
    [HilbertCongruence Geo]
    (O L H K : Geo.Point)
    (line : Geo.Line)
    (hOL : O ≠ L)
    (hOline : HilbertIncidence.OnLine O line)
    (hLline : HilbertIncidence.OnLine L line)
    (hHoff : Not (HilbertIncidence.OnLine H line))
    (hSameHK : HilbertSameSide Geo H K line)
    (hAngle :
      Geo.AngleCongruent
        O L H
        O L K) :
    HilbertSameRay Geo L H K := by

  rcases
      hilbert_angle_unique_common_ray
        Geo
        O L H K
        line
        hOL
        hOline
        hLline
        hHoff
        hSameHK
        hAngle
    with
    ⟨X, hRayXH, hRayXK⟩

  exact
    hilbert_sameRay_of_common
      Geo
      L X H K
      hRayXH
      hRayXK

theorem proposition39_test_circle_inscribed_vertex_radius_angles
    [HilbertCongruence Geo]
    (K R C A B : Geo.Point)
    (hC : HilbertCircle Geo K R C)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hKCA : Not (PrimCollinear Geo K C A))
    (hKAB : Not (PrimCollinear Geo K A B)) :
    Geo.AngleCongruent
        C A K
        A C K
    ∧
    Geo.AngleCongruent
        K A B
        A B K := by

  ----------------------------------------------------------------------
  -- Triangle K-C-A is isosceles.
  ----------------------------------------------------------------------

  have hBaseCA :
      Geo.AngleCongruent
        K C A
        K A C :=
    proposition39_test_circle_radii_base_angles
      Geo
      K R C A
      hC
      hA
      hKCA

  have hACK_KAC :
      Geo.AngleCongruent
        A C K
        K A C :=
    (Geo.angle_congruent_reverse_first
      K C A
      K A C).mp hBaseCA

  have hACK_CAK :
      Geo.AngleCongruent
        A C K
        C A K :=
    (Geo.angle_congruent_reverse_second
      A C K
      K A C).mp hACK_KAC

  have hCAK_ACK :
      Geo.AngleCongruent
        C A K
        A C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A C K
      C A K
      hACK_CAK

  ----------------------------------------------------------------------
  -- Triangle K-A-B is isosceles.
  ----------------------------------------------------------------------

  have hBaseAB :
      Geo.AngleCongruent
        K A B
        K B A :=
    proposition39_test_circle_radii_base_angles
      Geo
      K R A B
      hA
      hB
      hKAB

  have hKAB_ABK :
      Geo.AngleCongruent
        K A B
        A B K :=
    (Geo.angle_congruent_reverse_second
      K A B
      K B A).mp hBaseAB

  exact
    ⟨hCAK_ACK,
      hKAB_ABK⟩

theorem proposition39_test_circle_antipode
    [HilbertCongruence Geo]
    (K R A : Geo.Point)
    (hA : HilbertCircle Geo K R A)
    (hKA : K ≠ A) :
    ∃ E : Geo.Point,
      Geo.Between A K E ∧
      HilbertCircle Geo K R E := by

  rcases
      proposition39_test_opposite_equal_extension
        Geo
        A K
        hKA.symm
    with
    ⟨E, hAKE, hKE_KA⟩

  unfold HilbertCircle at hA ⊢

  have hKE_KR :
      Geo.Congruent K E K R :=
    hilbert_congruent_transitivity
      Geo
      K E
      K A
      K R
      hKE_KA
      hA

  exact
    ⟨E,
      hAKE,
      hKE_KR⟩

theorem proposition39_test_circle_inscribed_vertex_central_halves
    [HilbertEuclideanPlane Geo]
    (K R C A B : Geo.Point)
    (hC : HilbertCircle Geo K R C)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hKCA : Not (PrimCollinear Geo K C A))
    (hKAB : Not (PrimCollinear Geo K A B)) :
    ∃ E P Q : Geo.Point,
      Geo.Between A K E ∧
      HilbertCircle Geo K R E ∧
      Geo.Between C P E ∧
      Geo.Between B Q E ∧
      Geo.AngleCongruent C A K P K E ∧
      Geo.AngleCongruent K A B Q K E ∧
      Geo.AngleCongruent C K P P K E ∧
      Geo.AngleCongruent B K Q Q K E := by

  have hKA :
      K ≠ A :=
    hilbert_noncollinear_ne_first
      Geo K A B hKAB

  have hCAK :
      Not (PrimCollinear Geo C A K) := by
    intro h
    have hAKC :
        PrimCollinear Geo A K C :=
      PrimCollinearCycle
        Geo C A K h
    have hKCA' :
        PrimCollinear Geo K C A :=
      PrimCollinearCycle
        Geo A K C hAKC
    exact hKCA hKCA'

  have hBAK :
      Not (PrimCollinear Geo B A K) := by
    intro h
    have hABK :
        PrimCollinear Geo A B K :=
      PrimCollinearSwap
        Geo B A K h
    have hBKA :
        PrimCollinear Geo B K A :=
      PrimCollinearCycle
        Geo A B K hABK
    have hKAB' :
        PrimCollinear Geo K A B :=
      PrimCollinearCycle
        Geo B K A hBKA
    exact hKAB hKAB'

  rcases
      proposition39_test_circle_antipode
        Geo
        K R A
        hA
        hKA
    with
    ⟨E, hAKE, hE⟩

  rcases
      proposition39_test_circle_central_exterior_bisected
        Geo
        K R C A E
        hC
        hA
        hCAK
        hAKE
    with
    ⟨P,
      hCPE,
      _hACK_CKP,
      hCAK_PKE,
      hCKP_PKE⟩

  rcases
      proposition39_test_circle_central_exterior_bisected
        Geo
        K R B A E
        hB
        hA
        hBAK
        hAKE
    with
    ⟨Q,
      hBQE,
      _hABK_BKQ,
      hBAK_QKE,
      hBKQ_QKE⟩

  have hKAB_QKE :
      Geo.AngleCongruent
        K A B
        Q K E :=
    (Geo.angle_congruent_reverse_first
      B A K
      Q K E).mp
      hBAK_QKE

  exact
    ⟨E,
      P,
      Q,
      hAKE,
      hE,
      hCPE,
      hBQE,
      hCAK_PKE,
      hKAB_QKE,
      hCKP_PKE,
      hBKQ_QKE⟩

theorem proposition39_test_circle_inscribed_components_equal_central_halves
    [HilbertEuclideanPlane Geo]
    (K R C A B : Geo.Point)
    (hC : HilbertCircle Geo K R C)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hKCA : Not (PrimCollinear Geo K C A))
    (hKAB : Not (PrimCollinear Geo K A B)) :
    ∃ E P Q : Geo.Point,
      Geo.Between A K E ∧
      HilbertCircle Geo K R E ∧
      Geo.Between C P E ∧
      Geo.Between B Q E ∧
      Geo.AngleCongruent C A K C K P ∧
      Geo.AngleCongruent K A B B K Q := by

  rcases
      proposition39_test_circle_inscribed_vertex_central_halves
        Geo
        K R C A B
        hC
        hA
        hB
        hKCA
        hKAB
    with
    ⟨E,
      P,
      Q,
      hAKE,
      hE,
      hCPE,
      hBQE,
      hCAK_PKE,
      hKAB_QKE,
      hCKP_PKE,
      hBKQ_QKE⟩

  have hPKE_CKP :
      Geo.AngleCongruent
        P K E
        C K P :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C K P
      P K E
      hCKP_PKE

  have hCAK_CKP :
      Geo.AngleCongruent
        C A K
        C K P :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C A K
      P K E
      C K P
      hCAK_PKE
      hPKE_CKP

  have hQKE_BKQ :
      Geo.AngleCongruent
        Q K E
        B K Q :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K Q
      Q K E
      hBKQ_QKE

  have hKAB_BKQ :
      Geo.AngleCongruent
        K A B
        B K Q :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K A B
      Q K E
      B K Q
      hKAB_QKE
      hQKE_BKQ

  exact
    ⟨E,
      P,
      Q,
      hAKE,
      hE,
      hCPE,
      hBQE,
      hCAK_CKP,
      hKAB_BKQ⟩

/--
Reversing the endpoints of the crossed segment does not change the
fact that a ray meets its interior.
-/
theorem proposition39_test_ray_meets_segment_reverse
    [HilbertOrder Geo]
    (O D X C : Geo.Point)
    (hInside :
      HilbertRayMeetsSegment Geo O D X C) :
    HilbertRayMeetsSegment Geo O D C X := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hCHX :
      Geo.Between C H X :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.2.2.2

  exact
    ⟨H, hCHX, hRayODH⟩


/--
An interior ray of angle XOC lies on the same side of the line OC
as the first boundary ray OX.

The supplied line `base` is the carrier OC.
-/
theorem proposition39_test_interior_ray_sameSide_first
    [HilbertOrder Geo]
    (O D X C : Geo.Point)
    (base : Geo.Line)
    (hObase :
      HilbertIncidence.OnLine O base)
    (hCbase :
      HilbertIncidence.OnLine C base)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C) :
    HilbertSameSide Geo D X base := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hOC :
      O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo
      O C X
      (by
        intro h
        exact
          hXOC
            (PrimCollinearRotate
              Geo X C O
              (PrimCollinearSymm
                Geo O C X h)))

  have hXCO :
      Not (PrimCollinear Geo X C O) := by
    intro h
    exact
      hXOC
        (PrimCollinearRotate
          Geo X C O h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        X H O C
        hXHC
        hXCO
    with
    ⟨l,
      hOl,
      hCl,
      hXHsame_l⟩

  have hlbase :
      l = base :=
    HilbertPlaneIncidence.line_unique
      O C hOC
      l base
      hOl hCl
      hObase hCbase

  have hXHsame :
      HilbertSameSide Geo X H base := by
    rw [← hlbase]
    exact hXHsame_l

  rcases hRayODH.2.2.1 with
    ⟨rayLine,
      hOray,
      hDray,
      hHray⟩

  have hHC :
      H ≠ C :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.1

  have hCoff :
      Not (HilbertIncidence.OnLine C rayLine) := by

    intro hCray

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hHCX :
        PrimCollinear Geo H C X :=
      PrimCollinearCycle
        Geo X H C hXHCcol

    have hXray :
        HilbertIncidence.OnLine X rayLine :=
      hilbert_collinear_on_line
        Geo
        H C X
        rayLine
        hHC
        hHray
        hCray
        hHCX

    exact
      hXOC
        ⟨rayLine,
          hXray,
          hOray,
          hCray⟩

  have hDD :
      HilbertSameRay Geo O D D :=
    hilbert_sameRay_refl
      Geo O D hRayODH.1

  have hDHsame :
      HilbertSameSide Geo D H base :=
    hilbert_sameRay_points_sameSide
      Geo
      O D
      D H
      C
      rayLine base
      hOray
      hDray
      hObase
      hCbase
      hCoff
      hDD
      hRayODH

  have hHXsame :
      HilbertSameSide Geo H X base :=
    hilbert_sameSide_symm
      Geo X H base hXHsame

  exact
    hilbert_sameSide_trans
      Geo
      D H X
      base
      hDHsame
      hHXsame


/--
Two proper component angles of one decomposition cannot both be
strictly smaller than the corresponding component angles of another
decomposition of the same angle.

D and E are interior rays of angle XOC.

If

    angle XOD < angle XOE

and simultaneously

    angle COD < angle COE,

then the ray OD would cross both sides XE and CE.  Together with
the original crossing of XC this contradicts plane separation/Pasch.
-/
theorem proposition39_test_two_component_less_impossible
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hLessFirst :
      HilbertAngleLess Geo
        X O D
        X O E)
    (hLessSecond :
      HilbertAngleLess Geo
        C O D
        C O E) :
    False := by

  --------------------------------------------------------------------
  -- The reversed angle COX.
  --------------------------------------------------------------------

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  --------------------------------------------------------------------
  -- Supporting line OX.
  --------------------------------------------------------------------

  have hOXC :
      Not (PrimCollinear Geo O X C) := by
    intro h
    exact
      hXOC
        (PrimCollinearSwap
          Geo O X C h)

  have hOX :
      O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo O X C hOXC

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX
    with
    ⟨lineOX,
      hOlineOX,
      hXlineOX⟩

  have hDCSameOX :
      HilbertSameSide Geo D C lineOX :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O D C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideDrev

  have hECSameOX :
      HilbertSameSide Geo E C lineOX :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O E C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideErev

  have hCESameOX :
      HilbertSameSide Geo C E lineOX :=
    hilbert_sameSide_symm
      Geo
      E C
      lineOX
      hECSameOX

  have hDESameOX :
      HilbertSameSide Geo D E lineOX :=
    hilbert_sameSide_trans
      Geo
      D C E
      lineOX
      hDCSameOX
      hCESameOX

  --------------------------------------------------------------------
  -- Supporting line OC.
  --------------------------------------------------------------------

  have hOCX :
      Not (PrimCollinear Geo O C X) := by
    intro h
    exact
      hXOC
        (PrimCollinearRotate
          Geo
          X C O
          (PrimCollinearSymm
            Geo O C X h))

  have hOC :
      O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo O C X hOCX

  rcases
      HilbertPlaneIncidence.line_through
        O C hOC
    with
    ⟨lineOC,
      hOlineOC,
      hClineOC⟩

  have hDXSameOC :
      HilbertSameSide Geo D X lineOC :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O D X C
      lineOC
      hOlineOC
      hClineOC
      hXOC
      hInsideD

  have hEXSameOC :
      HilbertSameSide Geo E X lineOC :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O E X C
      lineOC
      hOlineOC
      hClineOC
      hXOC
      hInsideE

  have hXESameOC :
      HilbertSameSide Geo X E lineOC :=
    hilbert_sameSide_symm
      Geo
      E X
      lineOC
      hEXSameOC

  have hDESameOC :
      HilbertSameSide Geo D E lineOC :=
    hilbert_sameSide_trans
      Geo
      D X E
      lineOC
      hDXSameOC
      hXESameOC

  --------------------------------------------------------------------
  -- Strict inequalities place OD inside both XOE and COE.
  --------------------------------------------------------------------

  have hInsideFirst :
      HilbertRayMeetsSegment Geo O D X E :=
    proposition39_test_angle_less_ray_inside
      Geo
      D E O X
      lineOX
      hOlineOX
      hXlineOX
      hOX
      hDESameOX
      hLessFirst

  have hInsideSecond :
      HilbertRayMeetsSegment Geo O D C E :=
    proposition39_test_angle_less_ray_inside
      Geo
      D E O C
      lineOC
      hOlineOC
      hClineOC
      hOC
      hDESameOC
      hLessSecond

  --------------------------------------------------------------------
  -- Carrier OD and its original crossing of XC.
  --------------------------------------------------------------------

  rcases hInsideD with
    ⟨H₀,
      hXH₀C,
      hRayODH₀⟩

  have hOD :
      O ≠ D :=
    hRayODH₀.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O D hOD
    with
    ⟨lineOD,
      hOlineOD,
      hDlineOD⟩

  have hH₀lineOD :
      HilbertIncidence.OnLine H₀ lineOD :=
    hilbert_collinear_on_line
      Geo
      O D H₀
      lineOD
      hOD
      hOlineOD
      hDlineOD
      hRayODH₀.2.2.1

  --------------------------------------------------------------------
  -- Split according to whether E happens to lie on XC.
  --------------------------------------------------------------------

  by_cases hEXC :
      PrimCollinear Geo E X C

  --------------------------------------------------------------------
  -- Degenerate representative: E lies on XC.
  --------------------------------------------------------------------

  ·
    rcases hInsideE with
      ⟨H,
        hXHC,
        hRayOEH⟩

    have hXC :
        X ≠ C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.1

    rcases
        HilbertPlaneIncidence.line_through
          X C hXC
      with
      ⟨lineXC,
        hXlineXC,
        hClineXC⟩

    have hHlineXC :
        HilbertIncidence.OnLine H lineXC :=
      hilbert_between_on_line
        Geo
        X H C
        lineXC
        hXlineXC
        hClineXC
        hXHC

    have hXCE :
        PrimCollinear Geo X C E :=
      PrimCollinearCycle
        Geo E X C hEXC

    have hElineXC :
        HilbertIncidence.OnLine E lineXC :=
      hilbert_collinear_on_line
        Geo
        X C E
        lineXC
        hXC
        hXlineXC
        hClineXC
        hXCE

    have hOE :
        O ≠ E :=
      hRayOEH.1.symm

    rcases
        HilbertPlaneIncidence.line_through
          O E hOE
      with
      ⟨lineOE,
        hOlineOE,
        hElineOE⟩

    have hHlineOE :
        HilbertIncidence.OnLine H lineOE :=
      hilbert_collinear_on_line
        Geo
        O E H
        lineOE
        hOE
        hOlineOE
        hElineOE
        hRayOEH.2.2.1

    have hLinesXCOE :
        lineXC ≠ lineOE := by

      intro hEq

      have hOlineXC :
          HilbertIncidence.OnLine O lineXC := by
        rw [hEq]
        exact hOlineOE

      exact
        hXOC
          ⟨lineXC,
            hXlineXC,
            hOlineXC,
            hClineXC⟩

    have hHE :
        H = E := by

      by_contra hHE

      have hEq :
          lineXC = lineOE :=
        HilbertPlaneIncidence.line_unique
          E H
          (Ne.symm hHE)
          lineXC lineOE
          hElineXC hHlineXC
          hElineOE hHlineOE

      exact hLinesXCOE hEq

    have hXEC :
        Geo.Between X E C := by
      simpa [hHE] using hXHC

    rcases hInsideFirst with
      ⟨H₁,
        hXH₁E,
        hRayODH₁⟩

    rcases hInsideSecond with
      ⟨H₂,
        hCH₂E,
        hRayODH₂⟩

    have hH₁lineOD :
        HilbertIncidence.OnLine H₁ lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H₁
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH₁.2.2.1

    have hH₂lineOD :
        HilbertIncidence.OnLine H₂ lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H₂
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH₂.2.2.1

    have hH₁lineXC :
        HilbertIncidence.OnLine H₁ lineXC :=
      hilbert_between_on_line
        Geo
        X H₁ E
        lineXC
        hXlineXC
        hElineXC
        hXH₁E

    have hH₂lineXC :
        HilbertIncidence.OnLine H₂ lineXC :=
      hilbert_between_on_line
        Geo
        C H₂ E
        lineXC
        hClineXC
        hElineXC
        hCH₂E

    have hOoffXC :
        Not (HilbertIncidence.OnLine O lineXC) := by
      intro hOline
      exact
        hXOC
          ⟨lineXC,
            hXlineXC,
            hOline,
            hClineXC⟩

    have hLinesODXC :
        lineOD ≠ lineXC := by
      intro hEq
      apply hOoffXC
      rw [← hEq]
      exact hOlineOD

    have hH₁H₂ :
        H₁ = H₂ := by

      by_contra hH₁H₂

      have hEq :
          lineOD = lineXC :=
        HilbertPlaneIncidence.line_unique
          H₁ H₂
          hH₁H₂
          lineOD lineXC
          hH₁lineOD hH₂lineOD
          hH₁lineXC hH₂lineXC

      exact hLinesODXC hEq

    have hCH₁E :
        Geo.Between C H₁ E := by
      simpa [hH₁H₂] using hCH₂E

    have hEH₁C :
        Geo.Between E H₁ C :=
      (HilbertOrder.between_incidence
        C H₁ E hCH₁E).2.2.2.2

    have hInner :=
      hilbert_between_inner_trans
        Geo
        X H₁ E C
        hXH₁E
        hXEC

    have hH₁EC :
        Geo.Between H₁ E C :=
      hInner.1

    have hH₁ECcol :
        PrimCollinear Geo H₁ E C :=
      (HilbertOrder.between_incidence
        H₁ E C hH₁EC).2.2.2.1

    have hNotEH₁C :
        Not (Geo.Between E H₁ C) :=
      (HilbertOrder.between_unique
        (Geo := Geo)
        H₁ E C
        hH₁ECcol
        hH₁EC).1

    exact hNotEH₁C hEH₁C

  ·
    rcases hInsideFirst with
      ⟨H₁,
        hXH₁E,
        hRayODH₁⟩

    rcases hInsideSecond with
      ⟨H₂,
        hCH₂E,
        hRayODH₂⟩

    have hH₁lineOD :
        HilbertIncidence.OnLine H₁ lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H₁
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH₁.2.2.1

    have hH₂lineOD :
        HilbertIncidence.OnLine H₂ lineOD :=
      hilbert_collinear_on_line
        Geo
        O D H₂
        lineOD
        hOD
        hOlineOD
        hDlineOD
        hRayODH₂.2.2.1

    have hEH₁X :
        Geo.Between E H₁ X :=
      (HilbertOrder.between_incidence
        X H₁ E hXH₁E).2.2.2.2

    have hEH₂C :
        Geo.Between E H₂ C :=
      (HilbertOrder.between_incidence
        C H₂ E hCH₂E).2.2.2.2

    have hSameXC :
        HilbertSameSide Geo X C lineOD :=
      hilbert_third_side_endpoints_sameSide
        Geo
        E X C
        H₁ H₂
        lineOD
        hEXC
        hEH₁X
        hEH₂C
        hH₁lineOD
        hH₂lineOD

    have hOppXC :
        HilbertOppositeSide Geo X C lineOD :=
      ⟨hSameXC.1,
        hSameXC.2.1,
        ⟨H₀,
          hXH₀C,
          hH₀lineOD⟩⟩

    exact
      hilbert_oppositeSide_not_sameSide
        Geo
        X C
        lineOD
        hOppXC
        hSameXC




/--
Uniqueness of the half of an angle.

If OD and OE are two interior rays of the same nondegenerate angle XOC
and each divides the angle into two congruent component angles, then
the two first halves are congruent.

This is the cancellation principle needed for the synthetic form of
Euclid III.20--III.21.
-/
theorem proposition39_test_angle_half_unique
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hBisectD :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisectE :
      Geo.AngleCongruent
        X O E
        C O E) :
    Geo.AngleCongruent
      X O D
      X O E := by

  have hXOD :
      Not (PrimCollinear Geo X O D) :=
    (hilbert_interior_angle_less
      Geo
      O D X C
      hXOC
      hInsideD).1

  have hXOE :
      Not (PrimCollinear Geo X O E) :=
    (hilbert_interior_angle_less
      Geo
      O E X C
      hXOC
      hInsideE).1

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo
      O D C X
      hCOX
      hInsideDrev).1

  have hCOE :
      Not (PrimCollinear Geo C O E) :=
    (hilbert_interior_angle_less
      Geo
      O E C X
      hCOX
      hInsideErev).1

  rcases
      angle_trichotomy
        Geo
        X O D
        X O E
        hXOD
        hXOE
    with
    hEqual | hLess | hGreater

  --------------------------------------------------------------------
  -- Equal halves.
  --------------------------------------------------------------------

  · exact hEqual

  --------------------------------------------------------------------
  -- XOD < XOE.
  --
  -- Since each ray bisects the whole angle, this also gives
  -- COD < COE.  The preceding theorem excludes that configuration.
  --------------------------------------------------------------------

  ·
    have hCOD_XOD :
        Geo.AngleCongruent
          C O D
          X O D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        C O D
        hBisectD

    have hCOD_XOE :
        HilbertAngleLess Geo
          C O D
          X O E :=
      hilbert_angleLess_transport_left
        Geo
        X O D
        C O D
        X O E
        hLess
        hCOD
        hCOD_XOD

    have hCOD_COE :
        HilbertAngleLess Geo
          C O D
          C O E :=
      hilbert_angleLess_transport_right
        Geo
        C O D
        X O E
        C O E
        hCOD_XOE
        hCOE
        hBisectE

    exact
      False.elim
        (proposition39_test_two_component_less_impossible
          Geo
          O X C
          D E
          hXOC
          hInsideD
          hInsideE
          hLess
          hCOD_COE)

  --------------------------------------------------------------------
  -- XOE < XOD.
  --
  -- Symmetrically COE < COD, again impossible.
  --------------------------------------------------------------------

  ·
    have hCOE_XOE :
        Geo.AngleCongruent
          C O E
          X O E :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O E
        C O E
        hBisectE

    have hCOE_XOD :
        HilbertAngleLess Geo
          C O E
          X O D :=
      hilbert_angleLess_transport_left
        Geo
        X O E
        C O E
        X O D
        hGreater
        hCOE
        hCOE_XOE

    have hCOE_COD :
        HilbertAngleLess Geo
          C O E
          C O D :=
      hilbert_angleLess_transport_right
        Geo
        C O E
        X O D
        C O D
        hCOE_XOD
        hCOD
        hBisectD

    exact
      False.elim
        (proposition39_test_two_component_less_impossible
          Geo
          O X C
          E D
          hXOC
          hInsideE
          hInsideD
          hGreater
          hCOE_COD)


theorem proposition39_test_angle_half_unique_both
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hBisectD :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisectE :
      Geo.AngleCongruent
        X O E
        C O E) :
    Geo.AngleCongruent
        X O D
        X O E
    ∧
    Geo.AngleCongruent
        C O D
        C O E := by

  have hFirst :
      Geo.AngleCongruent
        X O D
        X O E :=
    proposition39_test_angle_half_unique
      Geo
      O X C D E
      hXOC
      hInsideD
      hInsideE
      hBisectD
      hBisectE

  have hCOD_XOD :
      Geo.AngleCongruent
        C O D
        X O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X O D
      C O D
      hBisectD

  have hCOD_XOE :
      Geo.AngleCongruent
        C O D
        X O E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C O D
      X O D
      X O E
      hCOD_XOD
      hFirst

  have hSecond :
      Geo.AngleCongruent
        C O D
        C O E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C O D
      X O E
      C O E
      hCOD_XOE
      hBisectE

  exact
    ⟨hFirst, hSecond⟩


theorem proposition39_test_angle_bisector_ray_unique
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D X C)
    (hInsideE :
      HilbertRayMeetsSegment Geo O E X C)
    (hBisectD :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisectE :
      Geo.AngleCongruent
        X O E
        C O E) :
    HilbertSameRay Geo O D E := by

  have hHalves :=
    proposition39_test_angle_half_unique_both
      Geo
      O X C D E
      hXOC
      hInsideD
      hInsideE
      hBisectD
      hBisectE

  have hFirst :
      Geo.AngleCongruent
        X O D
        X O E :=
    hHalves.1

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hXO :
      X ≠ O :=
    hilbert_noncollinear_ne_first
      Geo X O C hXOC

  have hOX :
      O ≠ X :=
    hXO.symm

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX
    with
    ⟨lineOX,
      hOlineOX,
      hXlineOX⟩

  have hDCSame :
      HilbertSameSide Geo D C lineOX :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O D C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideDrev

  have hECSame :
      HilbertSameSide Geo E C lineOX :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O E C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideErev

  have hCESame :
      HilbertSameSide Geo C E lineOX :=
    hilbert_sameSide_symm
      Geo
      E C
      lineOX
      hECSame

  have hDESame :
      HilbertSameSide Geo D E lineOX :=
    hilbert_sameSide_trans
      Geo
      D C E
      lineOX
      hDCSame
      hCESame

  exact
    proposition39_test_angle_unique_same_side_ray
      Geo
      X O D E
      lineOX
      hXO
      hXlineOX
      hOlineOX
      hDCSame.1
      hDESame
      hFirst

theorem proposition39_test_angle_subtraction
    [HilbertCongruence Geo]
    (O X C D A' O' B' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hAOB :
      Not (PrimCollinear Geo A' O' B'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' A' B')
    (hWhole :
      Geo.AngleCongruent
        X O C
        A' O' B')
    (hRight :
      Geo.AngleCongruent
        C O D
        B' O' D') :
    Geo.AngleCongruent
      X O D
      A' O' D' := by

  --------------------------------------------------------------------
  -- Transport D into the second whole angle.
  --------------------------------------------------------------------

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        O X C D
        A' O' B'
        hXOC
        hAOB
        hInside
        hWhole
    with
    ⟨Y,
      hInsideY,
      hBoth⟩

  have hRightY :
      Geo.AngleCongruent
        C O D
        B' O' Y :=
    hBoth.1

  have hLeftY :
      Geo.AngleCongruent
        X O D
        A' O' Y :=
    hBoth.2

  --------------------------------------------------------------------
  -- The right components at Y and D' are congruent.
  --------------------------------------------------------------------

  have hB'Y_B'D' :
      Geo.AngleCongruent
        B' O' Y
        B' O' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B' O' Y
      C O D
      B' O' D'
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        C O D
        B' O' Y
        hRightY)
      hRight

  --------------------------------------------------------------------
  -- Y and D' lie on the same side of the boundary O'B'.
  --------------------------------------------------------------------

  have hO'B'A' :
      Not (PrimCollinear Geo O' B' A') := by
    intro h
    exact
      hAOB
        (PrimCollinearRotate
          Geo
          A' B' O'
          (PrimCollinearSymm
            Geo O' B' A' h))

  have hO'B' :
      O' ≠ B' :=
    hilbert_noncollinear_ne_first
      Geo
      O' B' A'
      hO'B'A'

  rcases
      HilbertPlaneIncidence.line_through
        O' B' hO'B'
    with
    ⟨lineB',
      hO'line,
      hB'line⟩

  have hYASame :
      HilbertSameSide Geo Y A' lineB' :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O' Y A' B'
      lineB'
      hO'line
      hB'line
      hAOB
      hInsideY

  have hD'ASame :
      HilbertSameSide Geo D' A' lineB' :=
    proposition39_test_interior_ray_sameSide_first
      Geo
      O' D' A' B'
      lineB'
      hO'line
      hB'line
      hAOB
      hInside'

  have hAD'Same :
      HilbertSameSide Geo A' D' lineB' :=
    hilbert_sameSide_symm
      Geo
      D' A'
      lineB'
      hD'ASame

  have hYD'Same :
      HilbertSameSide Geo Y D' lineB' :=
    hilbert_sameSide_trans
      Geo
      Y A' D'
      lineB'
      hYASame
      hAD'Same

  --------------------------------------------------------------------
  -- Equal right components on the same side give the same ray.
  --------------------------------------------------------------------

  have hRayYD' :
      HilbertSameRay Geo O' Y D' :=
    proposition39_test_angle_unique_same_side_ray
      Geo
      B' O' Y D'
      lineB'
      hO'B'.symm
      hB'line
      hO'line
      hYASame.1
      hYD'Same
      hB'Y_B'D'

  --------------------------------------------------------------------
  -- Replace Y by D' in the left component.
  --------------------------------------------------------------------

  have hAngleReplace :
      Geo.Angle A' O' Y =
      Geo.Angle A' O' D' :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      O' A' Y D'
      hRayYD'

  unfold Geometry.Geo.AngleCongruent
    at hLeftY ⊢

  rw [← hAngleReplace]

  exact hLeftY

theorem proposition39_test_angle_addition_interior
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hX'O'C' :
      Not (PrimCollinear Geo X' O' C'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' X' C')
    (hLeft :
      Geo.AngleCongruent
        X O D
        X' O' D')
    (hRight :
      Geo.AngleCongruent
        D O C
        D' O' C') :
    Geo.AngleCongruent
      X O C
      X' O' C' := by

  --------------------------------------------------------------------
  -- First interior ray: line OD crosses segment XC.
  --------------------------------------------------------------------

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hOD :
      O ≠ D :=
    hRayODH.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O D hOD
    with
    ⟨lineOD,
      hOlineOD,
      hDlineOD⟩

  have hHlineOD :
      HilbertIncidence.OnLine H lineOD :=
    hilbert_collinear_on_line
      Geo
      O D H
      lineOD
      hOD
      hOlineOD
      hDlineOD
      hRayODH.2.2.1

  have hXHCdata :=
    HilbertOrder.between_incidence
      X H C hXHC

  have hXH :
      X ≠ H :=
    hXHCdata.1

  have hHC :
      H ≠ C :=
    hXHCdata.2.1

  have hXHCcol :
      PrimCollinear Geo X H C :=
    hXHCdata.2.2.2.1

  have hXoff :
      Not (HilbertIncidence.OnLine X lineOD) := by
    intro hXline

    have hCline :
        HilbertIncidence.OnLine C lineOD :=
      hilbert_collinear_on_line
        Geo
        X H C
        lineOD
        hXH
        hXline
        hHlineOD
        hXHCcol

    exact
      hXOC
        ⟨lineOD,
          hXline,
          hOlineOD,
          hCline⟩

  have hCoff :
      Not (HilbertIncidence.OnLine C lineOD) := by
    intro hCline

    have hCHX :
        PrimCollinear Geo C H X :=
      PrimCollinearSymm
        Geo X H C hXHCcol

    have hXline :
        HilbertIncidence.OnLine X lineOD :=
      hilbert_collinear_on_line
        Geo
        C H X
        lineOD
        hHC.symm
        hCline
        hHlineOD
        hCHX

    exact
      hXOC
        ⟨lineOD,
          hXline,
          hOlineOD,
          hCline⟩

  have hOppXC :
      HilbertOppositeSide Geo X C lineOD :=
    ⟨hXoff,
      hCoff,
      ⟨H,
        hXHC,
        hHlineOD⟩⟩

  have hNotSameXC :
      Not (HilbertSameSide Geo X C lineOD) :=
    hilbert_oppositeSide_not_sameSide
      Geo X C lineOD hOppXC


  --------------------------------------------------------------------
  -- Second interior ray: line O'D' crosses segment X'C'.
  --------------------------------------------------------------------

  rcases hInside' with
    ⟨H', hX'H'C', hRayO'D'H'⟩

  have hO'D' :
      O' ≠ D' :=
    hRayO'D'H'.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        O' D' hO'D'
    with
    ⟨lineO'D',
      hO'line,
      hD'line⟩

  have hH'line :
      HilbertIncidence.OnLine H' lineO'D' :=
    hilbert_collinear_on_line
      Geo
      O' D' H'
      lineO'D'
      hO'D'
      hO'line
      hD'line
      hRayO'D'H'.2.2.1

  have hX'H'C'data :=
    HilbertOrder.between_incidence
      X' H' C' hX'H'C'

  have hX'H' :
      X' ≠ H' :=
    hX'H'C'data.1

  have hH'C' :
      H' ≠ C' :=
    hX'H'C'data.2.1

  have hX'H'C'col :
      PrimCollinear Geo X' H' C' :=
    hX'H'C'data.2.2.2.1

  have hX'off :
      Not (HilbertIncidence.OnLine X' lineO'D') := by
    intro hX'line

    have hC'line :
        HilbertIncidence.OnLine C' lineO'D' :=
      hilbert_collinear_on_line
        Geo
        X' H' C'
        lineO'D'
        hX'H'
        hX'line
        hH'line
        hX'H'C'col

    exact
      hX'O'C'
        ⟨lineO'D',
          hX'line,
          hO'line,
          hC'line⟩

  have hC'off :
      Not (HilbertIncidence.OnLine C' lineO'D') := by
    intro hC'line

    have hC'H'X' :
        PrimCollinear Geo C' H' X' :=
      PrimCollinearSymm
        Geo X' H' C' hX'H'C'col

    have hX'line :
        HilbertIncidence.OnLine X' lineO'D' :=
      hilbert_collinear_on_line
        Geo
        C' H' X'
        lineO'D'
        hH'C'.symm
        hC'line
        hH'line
        hC'H'X'

    exact
      hX'O'C'
        ⟨lineO'D',
          hX'line,
          hO'line,
          hC'line⟩

  have hOppX'C' :
      HilbertOppositeSide Geo X' C' lineO'D' :=
    ⟨hX'off,
      hC'off,
      ⟨H',
        hX'H'C',
        hH'line⟩⟩

  have hNotSameX'C' :
      Not (HilbertSameSide Geo X' C' lineO'D') :=
    hilbert_oppositeSide_not_sameSide
      Geo X' C' lineO'D' hOppX'C'


  --------------------------------------------------------------------
  -- The two configurations are both opposite-side configurations.
  --------------------------------------------------------------------

  have hSideConfiguration :
      HilbertSameSide Geo X C lineOD ↔
      HilbertSameSide Geo X' C' lineO'D' := by
    constructor

    · intro hSame
      exact
        False.elim
          (hNotSameXC hSame)

    · intro hSame'
      exact
        False.elim
          (hNotSameX'C' hSame')


  --------------------------------------------------------------------
  -- Hilbert Theorem 15: addition of the two component angles.
  --------------------------------------------------------------------

  exact
    hilbert_angle_addition
      Geo
      X O D C
      X' O' D' C'
      lineOD lineO'D'
      hOD
      hO'D'
      hOlineOD
      hDlineOD
      hO'line
      hD'line
      hXoff
      hCoff
      hX'off
      hC'off
      hSideConfiguration
      hXOC
      hX'O'C'
      hLeft
      hRight

theorem proposition39_test_equal_halves_equal_wholes
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC :
      Not (PrimCollinear Geo X O C))
    (hX'O'C' :
      Not (PrimCollinear Geo X' O' C'))
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hInside' :
      HilbertRayMeetsSegment Geo O' D' X' C')
    (hBisect :
      Geo.AngleCongruent
        X O D
        D O C)
    (hBisect' :
      Geo.AngleCongruent
        X' O' D'
        D' O' C')
    (hHalf :
      Geo.AngleCongruent
        X O D
        X' O' D') :
    Geo.AngleCongruent
      X O C
      X' O' C' := by

  --------------------------------------------------------------------
  -- The second halves are congruent as well.
  --------------------------------------------------------------------

  have hDOC_XOD :
      Geo.AngleCongruent
        D O C
        X O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X O D
      D O C
      hBisect

  have hDOC_X'O'D' :
      Geo.AngleCongruent
        D O C
        X' O' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D O C
      X O D
      X' O' D'
      hDOC_XOD
      hHalf

  have hRight :
      Geo.AngleCongruent
        D O C
        D' O' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D O C
      X' O' D'
      D' O' C'
      hDOC_X'O'D'
      hBisect'

  --------------------------------------------------------------------
  -- Add the two congruent halves.
  --------------------------------------------------------------------

  exact
    proposition39_test_angle_addition_interior
      Geo
      O X C D
      O' X' C' D'
      hXOC
      hX'O'C'
      hInside
      hInside'
      hHalf
      hRight

theorem proposition39_test_circle_inscribed_components_are_central_halves
    [HilbertEuclideanPlane Geo]
    (K R C A B : Geo.Point)
    (hC : HilbertCircle Geo K R C)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hKCA :
      Not (PrimCollinear Geo K C A))
    (hKAB :
      Not (PrimCollinear Geo K A B)) :
    ∃ E P Q : Geo.Point,
      Geo.Between A K E ∧
      HilbertCircle Geo K R E ∧
      Geo.Between C P E ∧
      Geo.Between B Q E ∧
      Geo.AngleCongruent C A K C K P ∧
      Geo.AngleCongruent C K P P K E ∧
      Geo.AngleCongruent K A B B K Q ∧
      Geo.AngleCongruent B K Q Q K E := by

  rcases
      proposition39_test_circle_inscribed_vertex_central_halves
        Geo
        K R C A B
        hC
        hA
        hB
        hKCA
        hKAB
    with
    ⟨E,
      P,
      Q,
      hAKE,
      hE,
      hCPE,
      hBQE,
      hCAK_PKE,
      hKAB_QKE,
      hCKP_PKE,
      hBKQ_QKE⟩

  have hPKE_CKP :
      Geo.AngleCongruent
        P K E
        C K P :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C K P
      P K E
      hCKP_PKE

  have hCAK_CKP :
      Geo.AngleCongruent
        C A K
        C K P :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C A K
      P K E
      C K P
      hCAK_PKE
      hPKE_CKP

  have hQKE_BKQ :
      Geo.AngleCongruent
        Q K E
        B K Q :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B K Q
      Q K E
      hBKQ_QKE

  have hKAB_BKQ :
      Geo.AngleCongruent
        K A B
        B K Q :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K A B
      Q K E
      B K Q
      hKAB_QKE
      hQKE_BKQ

  exact
    ⟨E,
      P,
      Q,
      hAKE,
      hE,
      hCPE,
      hBQE,
      hCAK_CKP,
      hCKP_PKE,
      hKAB_BKQ,
      hBKQ_QKE⟩

theorem proposition39_test_circle_inscribed_additive_assembly
    [HilbertCongruence Geo]
    (A C K B P E Q : Geo.Point)
    (hCAB :
      Not (PrimCollinear Geo C A B))
    (hPKQ :
      Not (PrimCollinear Geo P K Q))
    (hInsideA :
      HilbertRayMeetsSegment Geo A K C B)
    (hInsideK :
      HilbertRayMeetsSegment Geo K E P Q)
    (hCAK_CKP :
      Geo.AngleCongruent
        C A K
        C K P)
    (hCKP_PKE :
      Geo.AngleCongruent
        C K P
        P K E)
    (hKAB_BKQ :
      Geo.AngleCongruent
        K A B
        B K Q)
    (hBKQ_QKE :
      Geo.AngleCongruent
        B K Q
        Q K E) :
    Geo.AngleCongruent
      C A B
      P K Q := by

  have hCAK_PKE :
      Geo.AngleCongruent
        C A K
        P K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C A K
      C K P
      P K E
      hCAK_CKP
      hCKP_PKE

  have hKAB_QKE :
      Geo.AngleCongruent
        K A B
        Q K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K A B
      B K Q
      Q K E
      hKAB_BKQ
      hBKQ_QKE

  have hKAB_EKQ :
      Geo.AngleCongruent
        K A B
        E K Q :=
    (Geo.angle_congruent_reverse_second
      K A B
      Q K E).mp
      hKAB_QKE

  exact
    proposition39_test_angle_addition_interior
      Geo
      A C B K
      K P Q E
      hCAB
      hPKQ
      hInsideA
      hInsideK
      hCAK_PKE
      hKAB_EKQ

theorem proposition39_test_circle_inscribed_subtractive_assembly
    [HilbertCongruence Geo]
    (A C K B P E Q : Geo.Point)
    (hCAK :
      Not (PrimCollinear Geo C A K))
    (hPKE :
      Not (PrimCollinear Geo P K E))
    (hInsideA :
      HilbertRayMeetsSegment Geo A B C K)
    (hInsideK :
      HilbertRayMeetsSegment Geo K Q P E)
    (hCAK_CKP :
      Geo.AngleCongruent
        C A K
        C K P)
    (hCKP_PKE :
      Geo.AngleCongruent
        C K P
        P K E)
    (hKAB_BKQ :
      Geo.AngleCongruent
        K A B
        B K Q)
    (hBKQ_QKE :
      Geo.AngleCongruent
        B K Q
        Q K E) :
    Geo.AngleCongruent
      C A B
      P K Q := by

  --------------------------------------------------------------------
  -- Equal larger angles.
  --------------------------------------------------------------------

  have hCAK_PKE :
      Geo.AngleCongruent
        C A K
        P K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C A K
      C K P
      P K E
      hCAK_CKP
      hCKP_PKE

  --------------------------------------------------------------------
  -- Equal parts to be subtracted.
  --------------------------------------------------------------------

  have hKAB_QKE :
      Geo.AngleCongruent
        K A B
        Q K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K A B
      B K Q
      Q K E
      hKAB_BKQ
      hBKQ_QKE

  have hKAB_EKQ :
      Geo.AngleCongruent
        K A B
        E K Q :=
    (Geo.angle_congruent_reverse_second
      K A B
      Q K E).mp
      hKAB_QKE

  --------------------------------------------------------------------
  -- Subtract equal interior parts from equal whole angles.
  --
  -- CAB = CAK - KAB
  -- PKQ = PKE - EKQ
  --------------------------------------------------------------------

  exact
    proposition39_test_angle_subtraction
      Geo
      A C K B
      P K E Q
      hCAK
      hPKE
      hInsideA
      hInsideK
      hCAK_PKE
      hKAB_EKQ

theorem proposition39_test_circle_inscribed_subtractive_assembly_mirror
    [HilbertCongruence Geo]
    (A C K B P E Q : Geo.Point)
    (hBAK :
      Not (PrimCollinear Geo B A K))
    (hQKE :
      Not (PrimCollinear Geo Q K E))
    (hInsideA :
      HilbertRayMeetsSegment Geo A C B K)
    (hInsideK :
      HilbertRayMeetsSegment Geo K P Q E)
    (hCAK_CKP :
      Geo.AngleCongruent
        C A K
        C K P)
    (hCKP_PKE :
      Geo.AngleCongruent
        C K P
        P K E)
    (hKAB_BKQ :
      Geo.AngleCongruent
        K A B
        B K Q)
    (hBKQ_QKE :
      Geo.AngleCongruent
        B K Q
        Q K E) :
    Geo.AngleCongruent
      C A B
      P K Q := by

  --------------------------------------------------------------------
  -- Equal larger angles.
  --------------------------------------------------------------------

  have hKAB_QKE :
      Geo.AngleCongruent
        K A B
        Q K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K A B
      B K Q
      Q K E
      hKAB_BKQ
      hBKQ_QKE

  have hBAK_QKE :
      Geo.AngleCongruent
        B A K
        Q K E :=
    (Geo.angle_congruent_reverse_first
      K A B
      Q K E).mp
      hKAB_QKE

  --------------------------------------------------------------------
  -- Equal parts to be subtracted.
  --------------------------------------------------------------------

  have hCAK_PKE :
      Geo.AngleCongruent
        C A K
        P K E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C A K
      C K P
      P K E
      hCAK_CKP
      hCKP_PKE

  have hKAC_PKE :
      Geo.AngleCongruent
        K A C
        P K E :=
    (Geo.angle_congruent_reverse_first
      C A K
      P K E).mp
      hCAK_PKE

  have hKAC_EKP :
      Geo.AngleCongruent
        K A C
        E K P :=
    (Geo.angle_congruent_reverse_second
      K A C
      P K E).mp
      hKAC_PKE

  --------------------------------------------------------------------
  -- BAK - KAC = BAC
  -- QKE - EKP = QKP.
  --------------------------------------------------------------------

  have hRaw :
      Geo.AngleCongruent
        B A C
        Q K P :=
    proposition39_test_angle_subtraction
      Geo
      A B K C
      Q K E P
      hBAK
      hQKE
      hInsideA
      hInsideK
      hBAK_QKE
      hKAC_EKP

  --------------------------------------------------------------------
  -- Reverse both resulting angles to the standard orientation.
  --------------------------------------------------------------------

  have hFirst :
      Geo.AngleCongruent
        C A B
        Q K P :=
    (Geo.angle_congruent_reverse_first
      B A C
      Q K P).mp
      hRaw

  exact
    (Geo.angle_congruent_reverse_second
      C A B
      Q K P).mp
      hFirst

theorem proposition39_test_circle_inscribed_three_case_assembly
    [HilbertCongruence Geo]
    (A C K B P E Q : Geo.Point)
    (hCAB :
      Not (PrimCollinear Geo C A B))
    (hCAK :
      Not (PrimCollinear Geo C A K))
    (hBAK :
      Not (PrimCollinear Geo B A K))
    (hPKQ :
      Not (PrimCollinear Geo P K Q))
    (hPKE :
      Not (PrimCollinear Geo P K E))
    (hQKE :
      Not (PrimCollinear Geo Q K E))
    (hCAK_CKP :
      Geo.AngleCongruent
        C A K
        C K P)
    (hCKP_PKE :
      Geo.AngleCongruent
        C K P
        P K E)
    (hKAB_BKQ :
      Geo.AngleCongruent
        K A B
        B K Q)
    (hBKQ_QKE :
      Geo.AngleCongruent
        B K Q
        Q K E)
    (hCases :
      (
        HilbertRayMeetsSegment Geo A K C B
        ∧
        HilbertRayMeetsSegment Geo K E P Q
      )
      ∨
      (
        HilbertRayMeetsSegment Geo A B C K
        ∧
        HilbertRayMeetsSegment Geo K Q P E
      )
      ∨
      (
        HilbertRayMeetsSegment Geo A C B K
        ∧
        HilbertRayMeetsSegment Geo K P Q E
      )) :
    Geo.AngleCongruent
      C A B
      P K Q := by

  rcases hCases with
    hAdd | hSub | hMirror

  --------------------------------------------------------------------
  -- Additive case.
  --------------------------------------------------------------------

  · exact
      proposition39_test_circle_inscribed_additive_assembly
        Geo
        A C K B P E Q
        hCAB
        hPKQ
        hAdd.1
        hAdd.2
        hCAK_CKP
        hCKP_PKE
        hKAB_BKQ
        hBKQ_QKE

  --------------------------------------------------------------------
  -- First subtractive case.
  --------------------------------------------------------------------

  · exact
      proposition39_test_circle_inscribed_subtractive_assembly
        Geo
        A C K B P E Q
        hCAK
        hPKE
        hSub.1
        hSub.2
        hCAK_CKP
        hCKP_PKE
        hKAB_BKQ
        hBKQ_QKE

  --------------------------------------------------------------------
  -- Mirror subtractive case.
  --------------------------------------------------------------------

  · exact
      proposition39_test_circle_inscribed_subtractive_assembly_mirror
        Geo
        A C K B P E Q
        hBAK
        hQKE
        hMirror.1
        hMirror.2
        hCAK_CKP
        hCKP_PKE
        hKAB_BKQ
        hBKQ_QKE

theorem proposition39_test_circle_inscribed_auxiliary_midpoints
    [HilbertEuclideanPlane Geo]
    (K R C A B : Geo.Point)
    (hC : HilbertCircle Geo K R C)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hKCA :
      Not (PrimCollinear Geo K C A))
    (hKAB :
      Not (PrimCollinear Geo K A B)) :
    ∃ E P Q : Geo.Point,
      HilbertIsMidpoint Geo K A E ∧
      HilbertIsMidpoint Geo P C E ∧
      HilbertIsMidpoint Geo Q B E := by

  rcases
      proposition39_test_circle_inscribed_components_are_central_halves
        Geo
        K R C A B
        hC
        hA
        hB
        hKCA
        hKAB
    with
    ⟨E,
      P,
      Q,
      hAKE,
      hE,
      hCPE,
      hBQE,
      _hCAK_CKP,
      hCKP_PKE,
      _hKAB_BKQ,
      hBKQ_QKE⟩

  --------------------------------------------------------------------
  -- K is the midpoint of AE.
  --------------------------------------------------------------------

  have hKR_KE :
      Geo.Congruent K R K E :=
    hilbert_congruent_symmetry
      Geo
      K E
      K R
      hE

  have hKA_KE :
      Geo.Congruent K A K E :=
    hilbert_congruent_transitivity
      Geo
      K A
      K R
      K E
      hA
      hKR_KE

  have hKC_KE :
      Geo.Congruent K C K E :=
    hilbert_congruent_transitivity
      Geo
      K C
      K R
      K E
      hC
      hKR_KE

  have hKB_KE :
      Geo.Congruent K B K E :=
    hilbert_congruent_transitivity
      Geo
      K B
      K R
      K E
      hB
      hKR_KE

  have hAK_KE :
      Geo.Congruent A K K E :=
    (Geo.congruent_reverse_first
      K A
      K E).mp
      hKA_KE

  have hMidK :
      HilbertIsMidpoint Geo K A E :=
    ⟨hAKE, hAK_KE⟩

  --------------------------------------------------------------------
  -- C,K,E is noncollinear.
  --------------------------------------------------------------------

  have hAKEcol :
      PrimCollinear Geo A K E :=
    (HilbertOrder.between_incidence
      A K E hAKE).2.2.2.1

  have hKE :
      K ≠ E :=
    (HilbertOrder.between_incidence
      A K E hAKE).2.1

  have hKEA :
      PrimCollinear Geo K E A :=
    PrimCollinearCycle
      Geo A K E hAKEcol

  have hCKE :
      Not (PrimCollinear Geo C K E) := by
    intro h

    have hCKA :
        PrimCollinear Geo C K A :=
      hilbert_primCollinear_trans
        Geo
        C K E A
        hKE
        h
        hKEA

    exact
      hKCA
        (PrimCollinearSwap
          Geo C K A hCKA)

  --------------------------------------------------------------------
  -- P is inside CE, hence triangles KCP and KEP are nondegenerate.
  --------------------------------------------------------------------

  have hKP :
      K ≠ P := by
    intro h
    subst P

    exact
      hCKE
        ((HilbertOrder.between_incidence
          C K E hCPE).2.2.2.1)

  have hRayKPP :
      HilbertSameRay Geo K P P :=
    hilbert_sameRay_refl
      Geo K P hKP.symm

  have hInsideP :
      HilbertRayMeetsSegment Geo K P C E :=
    ⟨P, hCPE, hRayKPP⟩

  have hCKP :
      Not (PrimCollinear Geo C K P) :=
    (hilbert_interior_angle_less
      Geo
      K P C E
      hCKE
      hInsideP).1

  have hEKC :
      Not (PrimCollinear Geo E K C) := by
    intro h

    exact
      hCKE
        (PrimCollinearSymm
          Geo E K C h)

  have hInsidePrev :
      HilbertRayMeetsSegment Geo K P E C :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      K P C E
      hInsideP

  have hEKP :
      Not (PrimCollinear Geo E K P) :=
    (hilbert_interior_angle_less
      Geo
      K P E C
      hEKC
      hInsidePrev).1

  have hKCP :
      Not (PrimCollinear Geo K C P) := by
    intro h

    exact
      hCKP
        (PrimCollinearSwap
          Geo K C P h)

  have hKEP :
      Not (PrimCollinear Geo K E P) := by
    intro h

    exact
      hEKP
        (PrimCollinearSwap
          Geo K E P h)

  have hCKP_EKP :
      Geo.AngleCongruent
        C K P
        E K P :=
    (Geo.angle_congruent_reverse_second
      C K P
      P K E).mp
      hCKP_PKE

  have hKP_KP :
      Geo.Congruent K P K P :=
    hilbert_congruent_reflexive
      Geo K P

  have hSASP :=
    SAS
      Geo
      K C P
      K E P
      hKCP
      hKEP
      hKC_KE
      hCKP_EKP
      hKP_KP

  have hCP_EP :
      Geo.Congruent C P E P :=
    hSASP.sideBC

  have hCP_PE :
      Geo.Congruent C P P E :=
    (Geo.congruent_reverse_second
      C P
      E P).mp
      hCP_EP

  have hMidP :
      HilbertIsMidpoint Geo P C E :=
    ⟨hCPE, hCP_PE⟩

  --------------------------------------------------------------------
  -- B,K,E is noncollinear.
  --------------------------------------------------------------------

  have hBKE :
      Not (PrimCollinear Geo B K E) := by
    intro h

    have hBKA :
        PrimCollinear Geo B K A :=
      hilbert_primCollinear_trans
        Geo
        B K E A
        hKE
        h
        hKEA

    exact
      hKAB
        (PrimCollinearCycle
          Geo B K A hBKA)

  --------------------------------------------------------------------
  -- Q is inside BE, hence the same SAS argument makes Q its midpoint.
  --------------------------------------------------------------------

  have hKQ :
      K ≠ Q := by
    intro h
    subst Q

    exact
      hBKE
        ((HilbertOrder.between_incidence
          B K E hBQE).2.2.2.1)

  have hRayKQQ :
      HilbertSameRay Geo K Q Q :=
    hilbert_sameRay_refl
      Geo K Q hKQ.symm

  have hInsideQ :
      HilbertRayMeetsSegment Geo K Q B E :=
    ⟨Q, hBQE, hRayKQQ⟩

  have hBKQ :
      Not (PrimCollinear Geo B K Q) :=
    (hilbert_interior_angle_less
      Geo
      K Q B E
      hBKE
      hInsideQ).1

  have hEKB :
      Not (PrimCollinear Geo E K B) := by
    intro h

    exact
      hBKE
        (PrimCollinearSymm
          Geo E K B h)

  have hInsideQrev :
      HilbertRayMeetsSegment Geo K Q E B :=
    proposition39_test_ray_meets_segment_reverse
      Geo
      K Q B E
      hInsideQ

  have hEKQ :
      Not (PrimCollinear Geo E K Q) :=
    (hilbert_interior_angle_less
      Geo
      K Q E B
      hEKB
      hInsideQrev).1

  have hKBQ :
      Not (PrimCollinear Geo K B Q) := by
    intro h

    exact
      hBKQ
        (PrimCollinearSwap
          Geo K B Q h)

  have hKEQ :
      Not (PrimCollinear Geo K E Q) := by
    intro h

    exact
      hEKQ
        (PrimCollinearSwap
          Geo K E Q h)

  have hBKQ_EKQ :
      Geo.AngleCongruent
        B K Q
        E K Q :=
    (Geo.angle_congruent_reverse_second
      B K Q
      Q K E).mp
      hBKQ_QKE

  have hKQ_KQ :
      Geo.Congruent K Q K Q :=
    hilbert_congruent_reflexive
      Geo K Q

  have hSASQ :=
    SAS
      Geo
      K B Q
      K E Q
      hKBQ
      hKEQ
      hKB_KE
      hBKQ_EKQ
      hKQ_KQ

  have hBQ_EQ :
      Geo.Congruent B Q E Q :=
    hSASQ.sideBC

  have hBQ_QE :
      Geo.Congruent B Q Q E :=
    (Geo.congruent_reverse_second
      B Q
      E Q).mp
      hBQ_EQ

  have hMidQ :
      HilbertIsMidpoint Geo Q B E :=
    ⟨hBQE, hBQ_QE⟩

  exact
    ⟨E,
      P,
      Q,
      hMidK,
      hMidP,
      hMidQ⟩


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
      proposition39_test_circle_sameRay_order
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
      proposition39_test_circle_sameRay_order
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

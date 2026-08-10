import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Hilbert representation of the Euclidean statement that two adjacent
angles are together equal to two right angles.

The witness E is the point on the extension of CB through B.
The angle ABD is congruent to the supplementary angle ABE.
-/
def HilbertAnglesEqualTwoRightAngles
    [HilbertIncidence Geo]
    (A B C D : Geo.Point) : Prop :=
  ∃ E : Geo.Point,
    Geo.Between C B E ∧
    Geo.AngleCongruent A B D A B E

/--
Euclid, Book I, Proposition 14.

If two straight lines meeting a straight line at the same point and
on opposite sides of it make adjacent angles together equal to two
right angles, then the two straight lines are in a straight line.
-/
theorem euclid_proposition_14
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hOppCD : HilbertOppositeSide Geo C D base)
    (hTwoRight :
      HilbertAnglesEqualTwoRightAngles Geo A B C D) :
    Geo.Between C B D := by

  rcases hTwoRight with ⟨E, hCBE, hAngleDE⟩

  have hCbase : ¬ HilbertIncidence.OnLine C base :=
    hOppCD.1

  have hCBEData :=
    HilbertOrder.between_incidence C B E hCBE

  have hBEC :
      PrimCollinear Geo B E C :=
    PrimCollinearCycle Geo C B E
      hCBEData.2.2.2.1

  have hEbase : ¬ HilbertIncidence.OnLine E base :=
    fun hEbase =>
      hCbase
        (hilbert_collinear_on_line
          Geo B E C base
          hCBEData.2.1
          hBbase
          hEbase
          hBEC)

  have hOppCE :
      HilbertOppositeSide Geo C E base :=
    ⟨hCbase, hEbase, ⟨B, hCBE, hBbase⟩⟩

  by_cases hCDE : PrimCollinear Geo C D E

  · rcases hCDE with ⟨line, hCline, hDline, hEline⟩
    rcases hOppCD.2.2 with ⟨X, hCXD, hXbase⟩

    have hCE : C ≠ E :=
      hCBEData.2.2.1

    have hCEB :
        PrimCollinear Geo C E B :=
      PrimCollinearRotate Geo C B E
        hCBEData.2.2.2.1

    have hBline :
        HilbertIncidence.OnLine B line :=
      hilbert_collinear_on_line
        Geo C E B line
        hCE
        hCline
        hEline
        hCEB

    have hXline :
        HilbertIncidence.OnLine X line :=
      hilbert_between_on_line
        Geo C X D line
        hCline
        hDline
        hCXD

    have hXB : X = B := by
      by_contra hXB
      have hLineEq : line = base :=
        HilbertPlaneIncidence.line_unique
          X B hXB
          line base
          hXline hBline
          hXbase hBbase
      exact hCbase (hLineEq ▸ hCline)

    subst X
    exact hCXD

  · have hDESame :
        HilbertSameSide Geo D E base := by
      rcases hOppCD.2.2 with ⟨X, hCXD, hXbase⟩
      exact
        hilbert_third_side_endpoints_sameSide
          Geo C D E X B base
          hCDE
          hCXD
          hCBE
          hXbase
          hBbase

    have hABE :
        ¬ PrimCollinear Geo A B E := by
      intro hABE
      have hEbase' : HilbertIncidence.OnLine E base :=
        hilbert_collinear_on_line
          Geo A B E base
          hAB
          hAbase
          hBbase
          hABE
      exact hEbase hEbase'

    have hEDSame :
        HilbertSameSide Geo E D base :=
      hilbert_sameSide_symm
        Geo D E base hDESame

    have hDDSame :
        HilbertSameSide Geo D D base :=
      hilbert_sameSide_refl
        Geo D base hOppCD.2.1

    rcases HilbertCongruence.angle_construction
        (Geo := Geo) A B E A B D
        hABE
        hAB
        base
        hAbase
        hBbase
        hOppCD.2.1 with
      ⟨Z, hZDSame, hAngleZ, hUnique⟩

    have hAngleEE :
        Geo.AngleCongruent A B E A B E :=
      Geo.angle_congruent_reflexive A B E

    have hZESameRay :
        HilbertSameRay Geo B Z E :=
      hUnique E hEDSame hAngleEE

    have hAngleED :
        Geo.AngleCongruent A B E A B D :=
      Geo.angle_congruent_symmetry
        A B D A B E
        hAngleDE

    have hZDSameRay :
        HilbertSameRay Geo B Z D :=
      hUnique D hDDSame hAngleED

    have hEDSameRay :
        HilbertSameRay Geo B E D :=
      bookZero_36_ray3
        Geo B Z E D
        hZESameRay
        hZDSameRay

    have hCCSameRay :
        HilbertSameRay Geo B C C :=
      hilbert_sameRay_refl
        Geo B C hCBEData.1

    have hCBD :
        Geo.Between C B D :=
      hilbert_between_transport_sameRays
        Geo C B E C D
        hCBE
        hCCSameRay
        hEDSameRay

    exact hCBD

end Geometry

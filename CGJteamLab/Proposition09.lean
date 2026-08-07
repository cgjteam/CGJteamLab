import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.9.

Every nondegenerate angle admits a bisecting ray.
-/
theorem euclid_proposition_9
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ Collinear Geo A B C) :
    ∃ M : Geo.Point,
      Geo.AngleCongruent B A M C A M := by

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  ----------------------------------------------------------------------
  -- Lay off AD congruent to AC on ray AB.
  ----------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A C
        A B
        hAB with
    ⟨D, hRayBD, hAD_AC⟩

  have hAD : A ≠ D :=
    hRayBD.2.1.symm

  have hABD :
      Collinear Geo A B D :=
    hRayBD.2.2.1

  ----------------------------------------------------------------------
  -- A, D, C are noncollinear.
  ----------------------------------------------------------------------

  have hADC :
      ¬ Collinear Geo A D C := by

    intro hADC

    have hBAD :
        Collinear Geo B A D :=
      PrimCollinearSwap Geo A B D hABD

    have hBAC :
        Collinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo
        B A D C
        hAD
        hBAD
        hADC

    exact
      hABC
        (PrimCollinearSwap Geo B A C hBAC)

  have hDC : D ≠ C := by
    intro hDC
    subst D
    exact hABC hABD

  ----------------------------------------------------------------------
  -- Let M be the midpoint of DC.
  ----------------------------------------------------------------------

  rcases
      HilbertMidpointExists
        Geo D C hDC with
    ⟨M, hMid⟩

  have hDMC :
      Geo.Between D M C :=
    hMid.1

  have hDM_MC :
      Geo.Congruent D M M C :=
    hMid.2

  have hDM : D ≠ M :=
    (HilbertOrder.between_incidence
      D M C hDMC).1

  have hDMCcol :
      Collinear Geo D M C :=
    (HilbertOrder.between_incidence
      D M C hDMC).2.2.2.1

  ----------------------------------------------------------------------
  -- Triangle ADM is nondegenerate.
  ----------------------------------------------------------------------

  have hADM :
      ¬ Collinear Geo A D M := by

    intro hADM

    have hADC' :
        Collinear Geo A D C :=
      hilbert_primCollinear_trans
        Geo
        A D M C
        hDM
        hADM
        hDMCcol

    exact hADC hADC'

  ----------------------------------------------------------------------
  -- Prepare the three side congruences for SSS.
  ----------------------------------------------------------------------

  have hDM_CM :
      Geo.Congruent D M C M :=
    (Geo.congruent_reverse_second
      D M M C).mp hDM_MC

  have hAM :
      Geo.Congruent A M A M :=
    hilbert_congruent_reflexive
      Geo A M

  ----------------------------------------------------------------------
  -- SSS for triangles ADM and ACM.
  ----------------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      A D M
      A C M
      hADM
      hAD_AC
      hDM_CM
      hAM

  have hAngle :
      Geo.AngleCongruent D A M C A M :=
    hSSS.2.angleA

  ----------------------------------------------------------------------
  -- D lies on the same ray from A as B.
  -- Hence angle DAM is the same angle as BAM.
  ----------------------------------------------------------------------

  have hRayDB :
      HilbertSameRay Geo A D B :=
    hilbert_sameRay_symm
      Geo A B D hRayBD

  have hEq :
      Geo.Angle D A M =
      Geo.Angle B A M :=
    hilbert_angle_eq_of_sameRay_first
      Geo A D B M hRayDB

  ----------------------------------------------------------------------
  -- Therefore AM bisects angle BAC.
  ----------------------------------------------------------------------

  refine ⟨M, ?_⟩

  unfold Geometry.Geo.AngleCongruent at hAngle ⊢
  rw [← hEq]
  exact hAngle

end Geometry

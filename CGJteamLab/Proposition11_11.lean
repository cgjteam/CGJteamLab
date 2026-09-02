import CGJteamLab.Proposition11_8
import CGJteamLab.Proposition12
import CGJteamLab.Proposition31

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid, Book XI, Proposition XI.11.

To draw a straight line perpendicular to a given plane from a given
elevated point.

Given a plane `pi` and a point `A` outside `pi`, there exists a line
through `A` perpendicular to `pi`.

The proof follows Euclid's classical construction:

1. choose a line `bc` in `pi`;
2. in the plane through `A` and `bc`, draw `ad` perpendicular to `bc`;
3. if `ad` is already perpendicular to `pi`, finish;
4. otherwise draw `de` in `pi` perpendicular to `bc`;
5. in the plane through `ad,de`, draw `af` perpendicular to `de`;
6. through `F` draw `gh` parallel to `bc`;
7. XI.4 gives `bc` perpendicular to the plane of `ad,de`;
8. XI.8 gives `gh` perpendicular to the same plane;
9. hence `af` is perpendicular to both `de` and `gh`;
10. XI.4 gives `af` perpendicular to `pi`.
-/
theorem euclid_proposition_11_11
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
    (A : Geo.Point)
    (hApi : Not (S.OnPlane A pi)) :
    exists l F,
      H.OnLine A l /\
      HilbertLinePerpendicularPlaneAt Geo l pi F := by

  ----------------------------------------------------------------------
  -- Choose a nondegenerate line bc in the given plane pi.
  ----------------------------------------------------------------------

  rcases
      hilbert_three_noncollinear_on_plane
        (Geo := Geo) pi
    with
    ⟨B, C, T,
     hBpi, hCpi, _hTpi,
     hBCT⟩

  have hBC : Ne B C :=
    hilbert_noncollinear_ne_first
      Geo B C T hBCT

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        B C hBC
    with
    ⟨bc, hBbc, hCbc⟩

  have hbcpi :
      HilbertLineInPlane Geo bc pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B C hBC
      bc hBbc hCbc
      pi hBpi hCpi

  have hAbc :
      Not (H.OnLine A bc) := by
    intro h
    exact hApi (hbcpi A h)

  ----------------------------------------------------------------------
  -- The line bc together with A determines the auxiliary plane sigma.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        bc A hAbc
    with
    ⟨sigma, hbcsigma, hAsigma, _hSigmaUnique⟩

  have hBsigma : S.OnPlane B sigma :=
    hbcsigma B hBbc

  have hCsigma : S.OnPlane C sigma :=
    hbcsigma C hCbc

  let Bsigma : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Csigma : PlanePoint Geo sigma :=
    ⟨C, hCsigma⟩

  let Asigma : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let bcsigma : PlaneLine Geo sigma :=
    ⟨bc, hbcsigma⟩

  have hBCsigma : Ne Bsigma Csigma := by
    intro h
    apply hBC
    exact congrArg Subtype.val h

  ----------------------------------------------------------------------
  -- First Euclid I.12 in PlaneGeo(sigma):
  -- draw AD perpendicular to BC.
  ----------------------------------------------------------------------

  rcases
      hilbert_perpendicular_from_point_exists
        (PlaneGeo Geo sigma)
        Bsigma Csigma Asigma
        bcsigma
        hBCsigma
        hBbc
        hCbc
        hAbc
    with
    ⟨Dsigma, Rsigma,
     hDbc,
     hRbc,
     hRightRDAPlane⟩

  have hRightRDA :
      HilbertRightAngle Geo Rsigma.1 Dsigma.1 A := by
    apply
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        sigma Rsigma Dsigma Asigma).mp
    exact hRightRDAPlane

  have hDpi : S.OnPlane Dsigma.1 pi :=
    hbcpi Dsigma.1 hDbc

  have hAD : Ne A Dsigma.1 := by
    intro h
    apply hApi
    rw [h]
    exact hDpi

  have hDA : Ne Dsigma.1 A :=
    hAD.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Dsigma.1 A hDA
    with
    ⟨ad, hDad, hAad⟩

  have hadsigma :
      HilbertLineInPlane Geo ad sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Dsigma.1 A hDA
      ad hDad hAad
      sigma Dsigma.2 hAsigma

  ----------------------------------------------------------------------
  -- Package the first I.12 right angle as bc perpendicular ad at D.
  ----------------------------------------------------------------------

  rcases hRightRDA with
    ⟨X, hRDX, hAngleRDA_ADX⟩

  have hRDXData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      Rsigma.1 Dsigma.1 X hRDX

  have hRD : Ne Rsigma.1 Dsigma.1 :=
    hRDXData.1

  have hRightRDA' :
      HilbertRightAngle Geo Rsigma.1 Dsigma.1 A :=
    ⟨X, hRDX, hAngleRDA_ADX⟩

  have hRDA :
      Not (PrimCollinear Geo Rsigma.1 Dsigma.1 A) := by
    intro hCol

    have hAonBC :
        H.OnLine A bc :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hRD
        hRbc
        hDbc
        hCol

    exact hApi (hbcpi A hAonBC)

  have hPerpBCAD :
      HilbertLinesPerpendicularAt Geo bc ad Dsigma.1 := by
    exact
      ⟨hDbc,
       hDad,
       Rsigma.1, A,
       hRD,
       hAD,
       hRbc,
       hAad,
       hRDA,
       hRightRDA'⟩

  ----------------------------------------------------------------------
  -- Euclid's case split.
  ----------------------------------------------------------------------

  by_cases hADpi :
      HilbertLinePerpendicularPlaneAt Geo ad pi Dsigma.1

  · exact
      ⟨ad, Dsigma.1, hAad, hADpi⟩

  · --------------------------------------------------------------------
    -- Nontrivial branch:
    -- construct DE in pi perpendicular to BC at D.
    --------------------------------------------------------------------

    let Bpi : PlanePoint Geo pi :=
      ⟨B, hBpi⟩

    let Cpi : PlanePoint Geo pi :=
      ⟨C, hCpi⟩

    let Dpi : PlanePoint Geo pi :=
      ⟨Dsigma.1, hDpi⟩

    let bcpi : PlaneLine Geo pi :=
      ⟨bc, hbcpi⟩

    rcases
        planeGeo_opposite_points_on_line_congruent_to
          (Geo := Geo)
          pi
          bcpi
          Dpi Bpi Cpi
          hDbc
      with
      ⟨Lpi, Mpi,
       hLbc,
       hMbc,
       hLDM,
       _hDLref,
       _hDMref⟩

    rcases
        hilbert_right_angle_exists_nondegenerate
          (PlaneGeo Geo pi)
          Lpi Dpi Mpi
          hLDM
      with
      ⟨Epi,
       hLDE_noncol,
       hRightLDE⟩

    have hDEL_noncol :
        Not
          (PrimCollinear
            (PlaneGeo Geo pi)
            Dpi Epi Lpi) := by
      intro h
      exact
        hLDE_noncol
          (PrimCollinearCycle
            (PlaneGeo Geo pi)
            Epi Lpi Dpi
            (PrimCollinearCycle
              (PlaneGeo Geo pi)
              Dpi Epi Lpi h))

    have hDEpi : Ne Dpi Epi :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        Dpi Epi Lpi
        hDEL_noncol

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Dpi Epi hDEpi
      with
      ⟨depi, hDde, hEde⟩

    have hLD : Ne Lpi Dpi :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        Lpi Dpi Epi
        hLDE_noncol

    have hED : Ne Epi Dpi :=
      hDEpi.symm

    have hPerpBCDEPlane :
        HilbertLinesPerpendicularAt
          (PlaneGeo Geo pi)
          bcpi depi Dpi := by
      exact
        ⟨hDbc,
         hDde,
         Lpi, Epi,
         hLD,
         hED,
         hLbc,
         hEde,
         hLDE_noncol,
         hRightLDE⟩

    have hPerpBCDE :
        HilbertLinesPerpendicularAt
          Geo bc depi.1 Dsigma.1 :=
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        pi bcpi depi Dpi).mp
        hPerpBCDEPlane

    have hADDE : Ne ad depi.1 := by
      intro hEq

      have hAde :
          H.OnLine A depi.1 := by
        rw [← hEq]
        exact hAad

      exact hApi (depi.2 A hAde)

    --------------------------------------------------------------------
    -- The intersecting lines ad,de determine the auxiliary plane tau.
    --------------------------------------------------------------------

    rcases
        hilbert_plane_through_two_intersecting_lines
          (Geo := Geo)
          ad depi.1
          hADDE
          Dsigma.1
          hDad
          hDde
      with
      ⟨tau,
       hadtau,
       hdetau,
       _hTauUnique⟩

    have hAtau : S.OnPlane A tau :=
      hadtau A hAad

    have hAde :
        Not (H.OnLine A depi.1) := by
      intro h
      exact hApi (depi.2 A h)

    --------------------------------------------------------------------
    -- Second Euclid I.12 in PlaneGeo(tau):
    -- draw AF perpendicular to DE.
    --------------------------------------------------------------------

    rcases
        hilbert_other_point_on_line
          (Geo := Geo)
          depi.1 Dsigma.1
      with
      ⟨E, hEDambient, hEdeAmbient⟩

    have hDEambient : Ne Dsigma.1 E :=
      hEDambient.symm

    have hEtau : S.OnPlane E tau :=
      hdetau E hEdeAmbient

    let Dtau : PlanePoint Geo tau :=
      ⟨Dsigma.1, hdetau Dsigma.1 hDde⟩

    let Etau : PlanePoint Geo tau :=
      ⟨E, hEtau⟩

    let Atau : PlanePoint Geo tau :=
      ⟨A, hAtau⟩

    let detau : PlaneLine Geo tau :=
      ⟨depi.1, hdetau⟩

    have hDEtau : Ne Dtau Etau := by
      intro h
      apply hDEambient
      exact congrArg Subtype.val h

    rcases
        hilbert_perpendicular_from_point_exists
          (PlaneGeo Geo tau)
          Dtau Etau Atau
          detau
          hDEtau
          hDde
          hEdeAmbient
          hAde
      with
      ⟨Ftau, Qtau,
       hFde,
       hQde,
       hRightQFAPlane⟩

    have hRightQFA :
        HilbertRightAngle Geo Qtau.1 Ftau.1 A := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          tau Qtau Ftau Atau).mp
      exact hRightQFAPlane

    have hFpi : S.OnPlane Ftau.1 pi :=
      depi.2 Ftau.1 hFde

    have hAF : Ne A Ftau.1 := by
      intro h
      apply hApi
      rw [h]
      exact hFpi

    have hFA : Ne Ftau.1 A :=
      hAF.symm

    rcases hRightQFA with
      ⟨Y, hQFY, hAngleQFA_AFY⟩

    have hQFYData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        Qtau.1 Ftau.1 Y hQFY

    have hQF : Ne Qtau.1 Ftau.1 :=
      hQFYData.1

    have hRightQFA' :
        HilbertRightAngle Geo Qtau.1 Ftau.1 A :=
      ⟨Y, hQFY, hAngleQFA_AFY⟩

    have hQFA :
        Not (PrimCollinear Geo Qtau.1 Ftau.1 A) := by
      intro hCol

      have hAonDE :
          H.OnLine A depi.1 :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hQF
          hQde
          hFde
          hCol

      exact hAde hAonDE

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          Ftau.1 A hFA
      with
      ⟨af, hFaf, hAaf⟩

    have haftau :
        HilbertLineInPlane Geo af tau :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        Ftau.1 A hFA
        af hFaf hAaf
        tau Ftau.2 hAtau

    have hPerpDEAF :
        HilbertLinesPerpendicularAt Geo depi.1 af Ftau.1 := by
      exact
        ⟨hFde,
         hFaf,
         Qtau.1, A,
         hQF,
         hAF,
         hQde,
         hAaf,
         hQFA,
         hRightQFA'⟩

    --------------------------------------------------------------------
    -- Hidden formal fact: F is not on bc.
    --------------------------------------------------------------------

    have hBCDE :
        Ne bc depi.1 :=
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        bc depi.1 Dsigma.1
        hPerpBCDE

    have hFnotBC :
        Not (H.OnLine Ftau.1 bc) := by

      intro hFbc

      have hFD : Ftau.1 = Dsigma.1 := by
        by_contra hFDne

        have hDF : Ne Dsigma.1 Ftau.1 := by
          intro h
          exact hFDne h.symm

        have hBCeqDE : bc = depi.1 :=
          HilbertPlaneIncidence.line_unique
            (Geo := Geo)
            Dsigma.1 Ftau.1 hDF
            bc depi.1
            hDbc hFbc
            hDde hFde

        exact hBCDE hBCeqDE

      have hDaf :
          H.OnLine Dsigma.1 af := by
        rw [← hFD]
        exact hFaf

      have hADeqAF : ad = af :=
        HilbertPlaneIncidence.line_unique
          (Geo := Geo)
          Dsigma.1 A hDA
          ad af
          hDad hAad
          hDaf hAaf

      have hPerpADBC :
          HilbertLinesPerpendicularAt Geo ad bc Dsigma.1 :=
        hilbert_space_linesPerpendicularAt_symm
          (Geo := Geo)
          bc ad Dsigma.1
          hPerpBCAD

      have hPerpDEAD :
          HilbertLinesPerpendicularAt Geo depi.1 ad Dsigma.1 := by
        rw [hADeqAF]
        rw [← hFD]
        exact hPerpDEAF

      have hPerpADDE :
          HilbertLinesPerpendicularAt Geo ad depi.1 Dsigma.1 :=
        hilbert_space_linesPerpendicularAt_symm
          (Geo := Geo)
          depi.1 ad Dsigma.1
          hPerpDEAD

      let depPi : PlaneLine Geo pi :=
        ⟨depi.1, depi.2⟩

      have hBCDEpi : Ne bcpi depPi := by
        intro h
        apply hBCDE
        exact congrArg Subtype.val h

      have hADpi' :
          HilbertLinePerpendicularPlaneAt
            Geo ad pi Dsigma.1 :=
        euclid_proposition_11_4
          (Geo := Geo)
          (pi := pi)
          (m := bcpi)
          (n := depPi)
          (l := ad)
          (O := Dpi)
          hBCDEpi
          hPerpADBC
          hPerpADDE

      exact hADpi hADpi'

    --------------------------------------------------------------------
    -- Euclid I.31 in PlaneGeo(pi):
    -- through F draw GH parallel to BC.
    --------------------------------------------------------------------

    let Fpi : PlanePoint Geo pi :=
      ⟨Ftau.1, hFpi⟩

    have hFnotBCPlane :
        Not ((PlaneGeo Geo pi).OnLine Fpi bcpi) := by
      exact hFnotBC

    have hBCF :
        Not
          (PrimCollinear
            (PlaneGeo Geo pi)
            Bpi Cpi Fpi) :=
      hilbert_not_collinear_of_off_line
        (PlaneGeo Geo pi)
        Bpi Cpi Fpi
        bcpi
        (by
          intro h
          apply hBC
          exact congrArg Subtype.val h)
        hBbc
        hCbc
        hFnotBCPlane

    rcases
        euclid_proposition_31
          (Geo := PlaneGeo Geo pi)
          Bpi Cpi Fpi
          (by
            intro h
            apply hBC
            exact congrArg Subtype.val h)
          hBCF
      with
      ⟨Gpi, hFG, hParallelPlane⟩

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Fpi Gpi hFG
      with
      ⟨ghpi, hFgh, hGgh⟩

    have hDisjointPlane :
        HilbertLinesDisjoint
          (PlaneGeo Geo pi)
          bcpi ghpi := by

      rintro ⟨Ppi, hPbc, hPgh⟩

      have hPBC :
          Ppi ∈
            (PlaneGeo Geo pi).PointLine Bpi Cpi :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Bpi Cpi Ppi
          bcpi
          hParallelPlane.1
          hBbc hCbc).mpr
          hPbc

      have hPFG :
          Ppi ∈
            (PlaneGeo Geo pi).PointLine Fpi Gpi :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Fpi Gpi Ppi
          ghpi
          hParallelPlane.2.1
          hFgh hGgh).mpr
          hPgh

      exact
        Set.disjoint_left.mp
          hParallelPlane.2.2
          hPBC
          hPFG

    have hDisjointAmbient :
        HilbertLinesDisjoint Geo bc ghpi.1 :=
      (planeGeo_linesDisjoint_iff_ambient
        (Geo := Geo)
        pi bcpi ghpi).mp
        hDisjointPlane

    have hSpaceParallel :
        HilbertSpaceLinesParallel Geo bc ghpi.1 :=
      ⟨pi,
       hbcpi,
       ghpi.2,
       hDisjointAmbient⟩

    --------------------------------------------------------------------
    -- XI.4 in tau:
    -- bc is perpendicular to both ad and de at D.
    --------------------------------------------------------------------

    let adtau : PlaneLine Geo tau :=
      ⟨ad, hadtau⟩

    let depTau : PlaneLine Geo tau :=
      ⟨depi.1, hdetau⟩

    let Dtau' : PlanePoint Geo tau :=
      ⟨Dsigma.1, hdetau Dsigma.1 hDde⟩

    have hADDEtau : Ne adtau depTau := by
      intro h
      apply hADDE
      exact congrArg Subtype.val h

    have hBCtau :
        HilbertLinePerpendicularPlaneAt
          Geo bc tau Dsigma.1 :=
      euclid_proposition_11_4
        (Geo := Geo)
        (pi := tau)
        (m := adtau)
        (n := depTau)
        (l := bc)
        (O := Dtau')
        hADDEtau
        hPerpBCAD
        hPerpBCDE

    --------------------------------------------------------------------
    -- XI.8 transfers perpendicularity to the parallel line gh.
    --------------------------------------------------------------------

    rcases
        euclid_proposition_11_8
          (Geo := Geo)
          bc ghpi.1
          tau
          Dsigma.1
          hSpaceParallel
          hBCtau
      with
      ⟨K, hGHtauK⟩

    --------------------------------------------------------------------
    -- Normalize the XI.8 foot K to the already constructed point F.
    --------------------------------------------------------------------

    have hKInc :=
      hGHtauK.incidence

    have hKgh :
        H.OnLine K ghpi.1 :=
      hKInc.1

    have hKtau :
        S.OnPlane K tau :=
      hKInc.2

    have hKF : K = Ftau.1 := by
      by_contra hKFne

      have hghtau :
          HilbertLineInPlane Geo ghpi.1 tau :=
        HilbertSpaceIncidence.line_in_plane
          (Geo := Geo)
          K Ftau.1 hKFne
          ghpi.1 hKgh hFgh
          tau hKtau Ftau.2

      have hSelfPerp :
          HilbertLinesPerpendicularAt
            Geo ghpi.1 ghpi.1 K :=
        HilbertLinePerpendicularPlaneAt.perpendicular_to_line
          (Geo := Geo)
          hGHtauK
          hghtau
          hKgh

      have hSelfNe :
          Ne ghpi.1 ghpi.1 :=
        hilbert_linesPerpendicularAt_ne
          (Geo := Geo)
          ghpi.1 ghpi.1 K
          hSelfPerp

      exact hSelfNe rfl

    subst K

    have hGHtauF :
        HilbertLinePerpendicularPlaneAt
          Geo ghpi.1 tau Ftau.1 :=
      hGHtauK

    --------------------------------------------------------------------
    -- XI.Def.3 gives gh perpendicular af, hence af perpendicular gh.
    --------------------------------------------------------------------

    have hPerpGHAF :
        HilbertLinesPerpendicularAt
          Geo ghpi.1 af Ftau.1 :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hGHtauF
        haftau
        hFaf

    have hPerpAFGH :
        HilbertLinesPerpendicularAt
          Geo af ghpi.1 Ftau.1 :=
      hilbert_space_linesPerpendicularAt_symm
        (Geo := Geo)
        ghpi.1 af Ftau.1
        hPerpGHAF

    have hPerpAFDE :
        HilbertLinesPerpendicularAt
          Geo af depi.1 Ftau.1 :=
      hilbert_space_linesPerpendicularAt_symm
        (Geo := Geo)
        depi.1 af Ftau.1
        hPerpDEAF

    --------------------------------------------------------------------
    -- de and gh are distinct lines of pi.
    --------------------------------------------------------------------

    have hDEGH :
        Ne depi.1 ghpi.1 := by
      intro hEq

      have hDgh :
          H.OnLine Dsigma.1 ghpi.1 := by
        rw [← hEq]
        exact hDde

      exact
        hDisjointAmbient
          ⟨Dsigma.1, hDbc, hDgh⟩

    let depPiFinal : PlaneLine Geo pi :=
      ⟨depi.1, depi.2⟩

    let ghpFinal : PlaneLine Geo pi :=
      ⟨ghpi.1, ghpi.2⟩

    have hDEGHpi :
        Ne depPiFinal ghpFinal := by
      intro h
      apply hDEGH
      exact congrArg Subtype.val h

    --------------------------------------------------------------------
    -- Final XI.4 in pi.
    --------------------------------------------------------------------

    have hAFpi :
        HilbertLinePerpendicularPlaneAt
          Geo af pi Ftau.1 :=
      euclid_proposition_11_4
        (Geo := Geo)
        (pi := pi)
        (m := depPiFinal)
        (n := ghpFinal)
        (l := af)
        (O := Fpi)
        hDEGHpi
        hPerpAFDE
        hPerpAFGH

    exact
      ⟨af, Ftau.1, hAaf, hAFpi⟩

end Geometry

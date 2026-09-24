import CGJteamLab.Proposition11_25
import CGJteamLab.Wyler.Proposition11_24

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})


/-!
# Euclid XI.25 - Hilbert-Wyler route

Production Hilbert-Wyler reconstruction of Euclid XI.25.

Architecture:

1. The neutral two-slab, cut, quotient-magnitude, proper-part, width,
   and Eudoxus infrastructure is shared with the canonical XI.25 file.
2. The genuinely different route is the XI.24 front end:
   `euclid_proposition_11_24_wyler` supplies the face packages for the
   left slab, right slab, whole slab, and every canonical width slab.
3. Equal-width propagation and equality of adjacent elementary solids
   are rebuilt over that Wyler XI.24 data.
4. Canonical width representatives `widthSolid_wyler` and
   `widthBase_wyler` use the same synthetic section-plane construction,
   but their XI.24 package is obtained through the Wyler carrier route.
5. Strict width comparison is realized by the same actual parallel cut;
   the resulting Wyler representatives form
   `HilbertXI25WidthRealization`.
6. The final Eudoxus argument is shared. No numerical area, volume,
   coordinates, or real-valued ratio is introduced.

The terminal theorem is

  `HilbertXI25SolidCutWitness.eudoxusProportion_from_seed_cut_wyler`.
-/


/--
XI.24 applied to both adjacent XI.25 slabs through the Hilbert-Wyler
carrier route.
-/
theorem hilbert_XI25_twoSlab_XI24_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25TwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2) :
    HilbertXI24Conclusion
        Geo
        A0 B0 C0 D0
        A1 B1 C1 D1
    /\
    HilbertXI24Conclusion
        Geo
        A1 B1 C1 D1
        A2 B2 C2 D2 := by

  have hLeftCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1 :=
    h.leftConfiguration
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2

  have hRightCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A1 B1 C1 D1
        A2 B2 C2 D2 :=
    h.rightConfiguration
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2

  have hLeft :
      HilbertXI24Conclusion
        Geo
        A0 B0 C0 D0
        A1 B1 C1 D1 :=
    euclid_proposition_11_24_wyler
      (Geo := Geo)
      pi0 pi1
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      hLeftCfg

  have hRight :
      HilbertXI24Conclusion
        Geo
        A1 B1 C1 D1
        A2 B2 C2 D2 :=
    euclid_proposition_11_24_wyler
      (Geo := Geo)
      pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A1 B1 C1 D1
      A2 B2 C2 D2
      hRightCfg

  exact And.intro hLeft hRight


/--
XI.24 applied to the whole XI.25 slab through the Hilbert-Wyler
carrier route.
-/
theorem hilbert_XI25_whole_XI24_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25TwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2) :
    HilbertXI24Conclusion
      Geo
      A0 B0 C0 D0
      A2 B2 C2 D2 := by

  have hWholeCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A2 B2 C2 D2 :=
    h.wholeConfiguration
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2

  exact
    euclid_proposition_11_24_wyler
      (Geo := Geo)
      pi0 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A2 B2 C2 D2
      hWholeCfg



theorem hilbert_XI25_equal_width_B_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25OrderedTwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2)
    (hWidthA :
      Geo.Congruent A0 A1 A1 A2) :
    Geo.Congruent B0 B1 B1 B2 := by

  have hXI24 :=
    hilbert_XI25_twoSlab_XI24_wyler
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2
      h.slab

  have hLeft := hXI24.1
  have hRight := hXI24.2

  have hLeftSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      rho0
      A0 B0 B1 A1
      h.slab.A0_on.2.1
      h.slab.B0_on.2.1
      h.slab.B1_on.2.1
      h.slab.A1_on.2.1
      hLeft.face_rho0

  have hRightSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      rho0
      A1 B1 B2 A2
      h.slab.A1_on.2.1
      h.slab.B1_on.2.1
      h.slab.B2_on.2.1
      h.slab.A2_on.2.1
      hRight.face_rho0

  have hB0B1_A0A1 :
      Geo.Congruent B0 B1 A0 A1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B0 B1
      A1 A0).mp
      hLeftSides.2

  have hB1B2_A1A2 :
      Geo.Congruent B1 B2 A1 A2 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B1 B2
      A2 A1).mp
      hRightSides.2

  have hB1B2ne : Ne B1 B2 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      B0 B1 B2 h.between_B).2.1

  have hA1A2_B1B2 :
      Geo.Congruent A1 A2 B1 B2 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      B1 B2
      A1 A2
      hB1B2ne
      hB1B2_A1A2

  have hA0A1ne : Ne A0 A1 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A0 A1 A2 h.between_A).1

  have hA0A1_A1A2 :
      Geo.Congruent A0 A1 A1 A2 :=
    hWidthA

  have hA0A1_B0B1 :
      Geo.Congruent A0 A1 B0 B1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      B0 B1
      A0 A1
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        B0 B1 B2 h.between_B).1
      hB0B1_A0A1

  have hB0B1_A1A2 :
      Geo.Congruent B0 B1 A1 A2 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A0 A1
      B0 B1
      A1 A2
      hA0A1_B0B1
      hA0A1_A1A2

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A1 A2
      B0 B1
      B1 B2
      (hilbert_space_congruent_symmetry
        (Geo := Geo)
        B0 B1
        A1 A2
        (HilbertSpaceOrder.between_incidence
          (Geo := Geo)
          B0 B1 B2 h.between_B).1
        hB0B1_A1A2)
      hA1A2_B1B2

/--
Equality of consecutive widths propagates to the C-edge.
-/
theorem hilbert_XI25_equal_width_C_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25OrderedTwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2)
    (hWidthA :
      Geo.Congruent A0 A1 A1 A2) :
    Geo.Congruent C0 C1 C1 C2 := by

  have hXI24 :=
    hilbert_XI25_twoSlab_XI24_wyler
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2
      h.slab

  have hLeft := hXI24.1
  have hRight := hXI24.2

  have hWidthB :
      Geo.Congruent B0 B1 B1 B2 :=
    hilbert_XI25_equal_width_B_wyler
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2
      h hWidthA

  have hLeftSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      sigma0
      C0 B0 B1 C1
      h.slab.C0_on.2.2
      h.slab.B0_on.2.2
      h.slab.B1_on.2.2
      h.slab.C1_on.2.2
      hLeft.face_sigma0

  have hRightSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      sigma0
      C1 B1 B2 C2
      h.slab.C1_on.2.2
      h.slab.B1_on.2.2
      h.slab.B2_on.2.2
      h.slab.C2_on.2.2
      hRight.face_sigma0

  have hB0B1_C0C1 :
      Geo.Congruent B0 B1 C0 C1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B0 B1
      C1 C0).mp
      hLeftSides.2

  have hB1B2_C1C2 :
      Geo.Congruent B1 B2 C1 C2 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B1 B2
      C2 C1).mp
      hRightSides.2

  have hB0B1ne : Ne B0 B1 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      B0 B1 B2 h.between_B).1

  have hB1B2_B0B1 :
      Geo.Congruent B1 B2 B0 B1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      B0 B1
      B1 B2
      hB0B1ne
      hWidthB

  have hB0B1_C1C2 :
      Geo.Congruent B0 B1 C1 C2 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      B1 B2
      B0 B1
      C1 C2
      hB1B2_B0B1
      hB1B2_C1C2

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      B0 B1
      C0 C1
      C1 C2
      hB0B1_C0C1
      hB0B1_C1C2

/--
Equality of consecutive widths propagates to the D-edge.
-/
theorem hilbert_XI25_equal_width_D_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25OrderedTwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2)
    (hWidthA :
      Geo.Congruent A0 A1 A1 A2) :
    Geo.Congruent D0 D1 D1 D2 := by

  have hXI24 :=
    hilbert_XI25_twoSlab_XI24_wyler
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2
      h.slab

  have hLeft := hXI24.1
  have hRight := hXI24.2

  have hLeftSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      sigma1
      D0 A0 A1 D1
      h.slab.D0_on.2.2
      h.slab.A0_on.2.2
      h.slab.A1_on.2.2
      h.slab.D1_on.2.2
      hLeft.face_sigma1

  have hRightSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      sigma1
      D1 A1 A2 D2
      h.slab.D1_on.2.2
      h.slab.A1_on.2.2
      h.slab.A2_on.2.2
      h.slab.D2_on.2.2
      hRight.face_sigma1

  have hA0A1_D0D1 :
      Geo.Congruent A0 A1 D0 D1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      A0 A1
      D1 D0).mp
      hLeftSides.2

  have hA1A2_D1D2 :
      Geo.Congruent A1 A2 D1 D2 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      A1 A2
      D2 D1).mp
      hRightSides.2

  have hA0A1ne : Ne A0 A1 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A0 A1 A2 h.between_A).1

  have hA1A2_A0A1 :
      Geo.Congruent A1 A2 A0 A1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A0 A1
      A1 A2
      hA0A1ne
      hWidthA

  have hA0A1_D1D2 :
      Geo.Congruent A0 A1 D1 D2 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A1 A2
      A0 A1
      D1 D2
      hA1A2_A0A1
      hA1A2_D1D2

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A0 A1
      D0 D1
      D1 D2
      hA0A1_D0D1
      hA0A1_D1D2

/--
Bundled propagation of equal consecutive widths to all four
longitudinal edges.
-/
theorem hilbert_XI25_equal_width_all_edges_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25OrderedTwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2)
    (hWidthA :
      Geo.Congruent A0 A1 A1 A2) :
    Geo.Congruent B0 B1 B1 B2 /\
    Geo.Congruent C0 C1 C1 C2 /\
    Geo.Congruent D0 D1 D1 D2 := by

  exact
    And.intro
      (hilbert_XI25_equal_width_B_wyler
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2
        h hWidthA)
      (And.intro
        (hilbert_XI25_equal_width_C_wyler
          (Geo := Geo)
          pi0 pi1 pi2
          rho0 rho1
          sigma0 sigma1
          A0 B0 C0 D0
          A1 B1 C1 D1
          A2 B2 C2 D2
          h hWidthA)
        (hilbert_XI25_equal_width_D_wyler
          (Geo := Geo)
          pi0 pi1 pi2
          rho0 rho1
          sigma0 sigma1
          A0 B0 C0 D0
          A1 B1 C1 D1
          A2 B2 C2 D2
          h hWidthA))


theorem hilbert_XI25_adjacent_elementary_solids_equal_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point)
    (h :
      HilbertXI25OrderedTwoSlabConfiguration
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2)
    (hWidthA :
      Geo.Congruent A0 A1 A1 A2) :
    let hXI24 :=
      hilbert_XI25_twoSlab_XI24_wyler
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2
        h.slab
    let hLeft := hXI24.1
    let hRight := hXI24.2
    HilbertXI10EqualSimilarParallelepiped
      (HilbertParallelogramFaceEqual Geo)
      (hilbertXI24ParallelepipedFaces
        (Geo := Geo)
        A0 B0 C0 D0
        A1 B1 C1 D1
        hLeft)
      (hilbertXI24ParallelepipedFaces
        (Geo := Geo)
        A1 B1 C1 D1
        A2 B2 C2 D2
        hRight) := by

  dsimp

  have hXI24 :=
    hilbert_XI25_twoSlab_XI24_wyler
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2
      h.slab

  have hLeft := hXI24.1
  have hRight := hXI24.2

  let SL :=
    hilbertXI24ParallelepipedFaces
      (Geo := Geo)
      A0 B0 C0 D0
      A1 B1 C1 D1
      hLeft

  let SR :=
    hilbertXI24ParallelepipedFaces
      (Geo := Geo)
      A1 B1 C1 D1
      A2 B2 C2 D2
      hRight

  have hOppL :
      HilbertParallelogramFaceEqual Geo SL.pi0 SL.pi1 /\
      HilbertParallelogramFaceEqual Geo SL.rho0 SL.rho1 /\
      HilbertParallelogramFaceEqual Geo SL.sigma0 SL.sigma1 := by
    simpa [SL] using
      hilbertXI24_oppositeFaceEqualities_for_XI10
        (Geo := Geo)
        A0 B0 C0 D0
        A1 B1 C1 D1
        hLeft

  have hOppR :
      HilbertParallelogramFaceEqual Geo SR.pi0 SR.pi1 /\
      HilbertParallelogramFaceEqual Geo SR.rho0 SR.rho1 /\
      HilbertParallelogramFaceEqual Geo SR.sigma0 SR.sigma1 := by
    simpa [SR] using
      hilbertXI24_oppositeFaceEqualities_for_XI10
        (Geo := Geo)
        A1 B1 C1 D1
        A2 B2 C2 D2
        hRight

  have hWidthB :
      Geo.Congruent B0 B1 B1 B2 :=
    hilbert_XI25_equal_width_B_wyler
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2
      h
      hWidthA

  have hPiShared :
      HilbertParallelogramFaceEqual
        Geo SL.pi1 SR.pi0 := by

    have hRefl :
        HilbertParallelogramFaceEqual
          Geo SL.pi1 SL.pi1 :=
      hilbertParallelogramFaceEqual_refl_space
        (Geo := Geo)
        SL.pi1

    simpa
      [SL, SR,
       hilbertXI24ParallelepipedFaces,
       HilbertParallelogramFaceEqual]
      using hRefl

  have hPi0 :
      HilbertParallelogramFaceEqual
        Geo SL.pi0 SR.pi0 :=
    hilbertParallelogramFaceEqual_trans_space
      (Geo := Geo)
      hOppL.1
      hPiShared

  have hRho0 :
      HilbertParallelogramFaceEqual
        Geo SL.rho0 SR.rho0 := by

    simpa [SL, SR, hilbertXI24ParallelepipedFaces] using
      hilbert_XI25_adjacent_rho_face_equal
        (Geo := Geo)
        rho0
        A0 B0 B1 A1 B2 A2
        h.slab.A0_on.2.1
        h.slab.B0_on.2.1
        h.slab.B1_on.2.1
        h.slab.A1_on.2.1
        h.slab.B2_on.2.1
        hLeft.face_rho0
        hRight.face_rho0
        h.between_B
        hWidthB

  have hSigma0 :
      HilbertParallelogramFaceEqual
        Geo SL.sigma0 SR.sigma0 := by

    simpa [SL, SR, hilbertXI24ParallelepipedFaces] using
      hilbert_XI25_adjacent_sigma_face_equal
        (Geo := Geo)
        sigma0
        C0 B0 B1 C1 B2 C2
        h.slab.C0_on.2.2
        h.slab.B0_on.2.2
        h.slab.B1_on.2.2
        h.slab.C1_on.2.2
        h.slab.B2_on.2.2
        hLeft.face_sigma0
        hRight.face_sigma0
        h.between_B
        hWidthB

  have hSolid :
      HilbertXI10EqualSimilarParallelepiped
        (HilbertParallelogramFaceEqual Geo)
        SL SR :=
    hilbertXI10EqualSimilarParallelepiped_of_three_adjacent
      (HilbertParallelogramFaceEqual Geo)
      (fun hEq =>
        hilbertParallelogramFaceEqual_symm_space
          (Geo := Geo) hEq)
      (fun h1 h2 =>
        hilbertParallelogramFaceEqual_trans_space
          (Geo := Geo) h1 h2)
      SL SR
      hOppL.1
      hOppL.2.1
      hOppL.2.2
      hOppR.1
      hOppR.2.1
      hOppR.2.2
      hPi0
      hRho0
      hSigma0

  simpa [SL, SR] using hSolid


theorem hilbert_XI25_adjacent_solids_equal_of_base_equal_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (hBase :
      HilbertXI25BaseEquivalent
        Geo
        (X.leftBase (Geo := Geo))
        (X.rightBase (Geo := Geo))) :
    HilbertXI25SolidEquivalent
      Geo
      (X.leftSolid (Geo := Geo))
      (X.rightSolid (Geo := Geo)) := by

  change
    TriangleCongruenceResult
      Geo
      X.B0 X.A0 X.B1
      X.B1 X.A1 X.B2
    at hBase

  have hWidthB :
      Geo.Congruent
        X.B0 X.B1
        X.B1 X.B2 :=
    hBase.sideAC

  have hXI24 :=
    hilbert_XI25_twoSlab_XI24_wyler
      (Geo := Geo)
      X.pi0 X.pi1 X.pi2
      X.rho0 X.rho1
      X.sigma0 X.sigma1
      X.A0 X.B0 X.C0 X.D0
      X.A1 X.B1 X.C1 X.D1
      X.A2 X.B2 X.C2 X.D2
      X.ordered.slab

  have hLeft := hXI24.1
  have hRight := hXI24.2

  have hLeftSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      X.rho0
      X.A0 X.B0 X.B1 X.A1
      X.ordered.slab.A0_on.2.1
      X.ordered.slab.B0_on.2.1
      X.ordered.slab.B1_on.2.1
      X.ordered.slab.A1_on.2.1
      hLeft.face_rho0

  have hRightSides :=
    hilbert_space_parallelogram_opposite_sides_congruent_XI
      (Geo := Geo)
      X.rho0
      X.A1 X.B1 X.B2 X.A2
      X.ordered.slab.A1_on.2.1
      X.ordered.slab.B1_on.2.1
      X.ordered.slab.B2_on.2.1
      X.ordered.slab.A2_on.2.1
      hRight.face_rho0

  have hB0B1_A0A1 :
      Geo.Congruent
        X.B0 X.B1
        X.A0 X.A1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      X.B0 X.B1
      X.A1 X.A0).mp
      hLeftSides.2

  have hB1B2_A1A2 :
      Geo.Congruent
        X.B1 X.B2
        X.A1 X.A2 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      X.B1 X.B2
      X.A2 X.A1).mp
      hRightSides.2

  have hB1B2_A0A1 :
      Geo.Congruent
        X.B1 X.B2
        X.A0 X.A1 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      X.B0 X.B1
      X.B1 X.B2
      X.A0 X.A1
      hWidthB
      hB0B1_A0A1

  have hWidthA :
      Geo.Congruent
        X.A0 X.A1
        X.A1 X.A2 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      X.B1 X.B2
      X.A0 X.A1
      X.A1 X.A2
      hB1B2_A0A1
      hB1B2_A1A2

  have hSolid :=
    hilbert_XI25_adjacent_elementary_solids_equal_wyler
      (Geo := Geo)
      X.pi0 X.pi1 X.pi2
      X.rho0 X.rho1
      X.sigma0 X.sigma1
      X.A0 X.B0 X.C0 X.D0
      X.A1 X.B1 X.C1 X.D1
      X.A2 X.B2 X.C2 X.D2
      X.ordered
      hWidthA

  simpa
    [HilbertXI25SolidEquivalent,
     HilbertXI25SolidCutWitness.leftSolid,
     HilbertXI25SolidCutWitness.rightSolid,
     HilbertXI25SolidCutWitness.leftXI24,
     HilbertXI25SolidCutWitness.rightXI24]
    using hSolid


namespace HilbertXI25TwoSlabComparisonCertificate

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [SP : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := SP)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := SP)]
  [HSE : HilbertSpaceEuclidean Geo]

/--
A source-level XI.25 comparison certificate yields the corresponding
solid comparison through the Hilbert-Wyler route.
-/
theorem solidComparison_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (h :
      HilbertXI25TwoSlabComparisonCertificate
        (Geo := Geo) X) :
    HilbertXI25SolidComparison
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.rightSolid (Geo := Geo)) := by

  cases h with
  | inl hEqual =>
      exact
        Or.inl
          (hilbert_XI25_adjacent_solids_equal_of_base_equal_wyler
            (Geo := Geo)
            X hEqual)

  | inr hStrict =>
      cases hStrict with
      | inl hLeftLess =>
          exact
            Or.inr
              (Or.inl
                (HilbertXI25AlignedProperPartWitness.solidLess
                  (Geo := Geo) hLeftLess))

      | inr hRightLess =>
          exact
            Or.inr
              (Or.inr
                (HilbertXI25AlignedProperPartWitness.solidLess
                  (Geo := Geo) hRightLess))

/--
Bundled comparison transfer through the Hilbert-Wyler route.

The base comparison is neutral and reused unchanged; the solid equality
branch is the Wyler one.
-/
theorem base_and_solid_comparison_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (h :
      HilbertXI25TwoSlabComparisonCertificate
        (Geo := Geo) X) :
    HilbertXI25BaseComparison
      (Geo := Geo)
      (X.leftBase (Geo := Geo))
      (X.rightBase (Geo := Geo))
    /\
    HilbertXI25SolidComparison
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.rightSolid (Geo := Geo)) := by

  exact
    And.intro
      (baseComparison (Geo := Geo) X h)
      (solidComparison_wyler (Geo := Geo) X h)

end HilbertXI25TwoSlabComparisonCertificate


/--
A concrete two-slab comparison certificate induces the corresponding
certificate on quotient magnitude classes through the Hilbert-Wyler
route.
-/
theorem hilbert_XI25_classComparisonCertificate_of_twoSlab_wyler
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (h :
      HilbertXI25TwoSlabComparisonCertificate
        (Geo := Geo) X) :
    HilbertXI25ClassComparisonCertificate
      (Geo := Geo)
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.leftBase (Geo := Geo)))
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.rightBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.leftSolid (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.rightSolid (Geo := Geo))) := by

  cases h with
  | inl hEqual =>
      apply Or.inl

      have hSolidEqual :
          HilbertXI25SolidEquivalent
            Geo
            (X.leftSolid (Geo := Geo))
            (X.rightSolid (Geo := Geo)) :=
        hilbert_XI25_adjacent_solids_equal_of_base_equal_wyler
          (Geo := Geo) X hEqual

      exact
        And.intro
          (Quotient.sound hEqual)
          (Quotient.sound hSolidEqual)

  | inr hStrict =>
      cases hStrict with
      | inl hLeftLess =>
          apply Or.inr
          apply Or.inl

          exact
            And.intro
              ((hilbertXI25BaseClassOf_less_iff
                  (Geo := Geo)
                  (X.leftBase (Geo := Geo))
                  (X.rightBase (Geo := Geo))).2
                (HilbertXI25AlignedProperPartWitness.baseLess
                  (Geo := Geo) hLeftLess))
              ((hilbertXI25SolidClassOf_less_iff
                  (Geo := Geo)
                  (X.leftSolid (Geo := Geo))
                  (X.rightSolid (Geo := Geo))).2
                (HilbertXI25AlignedProperPartWitness.solidLess
                  (Geo := Geo) hLeftLess))

      | inr hRightLess =>
          apply Or.inr
          apply Or.inr

          exact
            And.intro
              ((hilbertXI25BaseClassOf_less_iff
                  (Geo := Geo)
                  (X.rightBase (Geo := Geo))
                  (X.leftBase (Geo := Geo))).2
                (HilbertXI25AlignedProperPartWitness.baseLess
                  (Geo := Geo) hRightLess))
              ((hilbertXI25SolidClassOf_less_iff
                  (Geo := Geo)
                  (X.rightSolid (Geo := Geo))
                  (X.leftSolid (Geo := Geo))).2
                (HilbertXI25AlignedProperPartWitness.solidLess
                  (Geo := Geo) hRightLess))


namespace HilbertXI25SolidCutWitness

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [SP : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := SP)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := SP)]
  [HSE : HilbertSpaceEuclidean Geo]

/--
XI.24 data for the canonical solid of width `x`, obtained through the
Hilbert-Wyler carrier route.
-/
theorem widthXI24_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertXI24Conclusion
      Geo
      X.A0 X.B0 X.C0 X.D0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) x) := by

  exact
    euclid_proposition_11_24_wyler
      (Geo := Geo)
      X.pi0
      (X.widthSectionPlane (Geo := Geo) x)
      X.rho0 X.rho1
      X.sigma0 X.sigma1
      X.A0 X.B0 X.C0 X.D0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) x)
      (X.widthParallelepipedConfiguration
        (Geo := Geo) x)

end HilbertXI25SolidCutWitness


namespace HilbertXI25SolidCutWitness

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [SP : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := SP)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := SP)]
  [HSE : HilbertSpaceEuclidean Geo]

/--
Canonical concrete parallelepiped representing width `x`, with its
XI.24 package obtained through the Hilbert-Wyler route.
-/
noncomputable def widthSolid_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertXI25Parallelepiped Geo :=

  hilbertXI24ParallelepipedFaces
    (Geo := Geo)
    X.A0 X.B0 X.C0 X.D0
    (X.widthPointA (Geo := Geo) x)
    (X.widthPointB (Geo := Geo) x)
    (X.widthPointC (Geo := Geo) x)
    (X.widthPointD (Geo := Geo) x)
    (X.widthXI24_wyler (Geo := Geo) x)


/--
The canonical Wyler base corresponding to width `x` is the `rho0`
face of the canonical Wyler solid.
-/
noncomputable def widthBase_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertParallelogramFace Geo :=

  (X.widthSolid_wyler (Geo := Geo) x).rho0


/--
The `.b` vertex of the canonical Wyler base is `B0`.
-/
theorem widthBase_b_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    (X.widthBase_wyler (Geo := Geo) x).b = X.B0 := by

  rfl


/--
The `.c` vertex of the canonical Wyler base is `B(x)`.
-/
theorem widthBase_c_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    (X.widthBase_wyler (Geo := Geo) x).c =
      X.widthPointB (Geo := Geo) x := by

  rfl


/--
The `.b` vertex of the canonical Wyler base lies in `rho0`.
-/
theorem widthBase_b_on_rho0_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthBase_wyler (Geo := Geo) x).b
      X.rho0 := by

  simpa [widthBase_b_wyler] using
    X.ordered.slab.B0_on.2.1


/--
The `.c` vertex of the canonical Wyler base lies in `rho0`.
-/
theorem widthBase_c_on_rho0_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthBase_wyler (Geo := Geo) x).c
      X.rho0 := by

  simpa [widthBase_c_wyler] using
    X.widthPointB_on_rho0
      (Geo := Geo) x


/--
The distinguished edge of the canonical Wyler base represents exactly
the prescribed positive width class.
-/
theorem widthBase_widthClass_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    hilbert_XI25_widthClass
        (Geo := Geo)
        X.rho0
        (X.widthBase_wyler (Geo := Geo) x).b
        (X.widthBase_wyler (Geo := Geo) x).c
        (X.widthBase_b_on_rho0_wyler
          (Geo := Geo) x)
        (X.widthBase_c_on_rho0_wyler
          (Geo := Geo) x)
        (hilbert_XI25_base_width_ne
          (Geo := Geo)
          (X.widthBase_wyler (Geo := Geo) x))
      =
    x := by

  have h :=
    hilbert_XI25_widthPoint_class
      (Geo := Geo)
      X.rho0
      (X.B0rho (Geo := Geo))
      (X.B1rho (Geo := Geo))
      (X.B0rho_ne_B1rho
        (Geo := Geo))
      x

  change
    hilbert_XI25_widthClass
        (Geo := Geo)
        X.rho0
        X.B0
        (X.widthPointB (Geo := Geo) x)
        _
        _
        _
      =
    x

  unfold hilbert_XI25_widthClass
  dsimp

  let O1 : PlanePoint Geo X.rho0 :=
    Subtype.mk
      X.B0
      (X.widthBase_b_on_rho0_wyler
        (Geo := Geo) x)

  let P1 : PlanePoint Geo X.rho0 :=
    Subtype.mk
      (X.widthPointB (Geo := Geo) x)
      (X.widthBase_c_on_rho0_wyler
        (Geo := Geo) x)

  let O2 : PlanePoint Geo X.rho0 :=
    X.B0rho (Geo := Geo)

  let P2 : PlanePoint Geo X.rho0 :=
    hilbert_XI25_widthPoint
      (Geo := Geo)
      X.rho0
      (X.B0rho (Geo := Geo))
      (X.B1rho (Geo := Geo))
      (X.B0rho_ne_B1rho
        (Geo := Geo))
      x

  have hO : O1 = O2 := by
    apply Subtype.ext
    rfl

  have hP : P1 = P2 := by
    apply Subtype.ext
    rfl

  have hLeftNe : Ne O1 P1 := by
    intro hEq
    apply
      X.widthPointB_ne_origin
        (Geo := Geo) x
    exact
      congrArg Subtype.val hEq

  have hRightNe : Ne O2 P2 := by
    exact
      hilbert_XI25_widthPoint_ne
        (Geo := Geo)
        X.rho0
        (X.B0rho (Geo := Geo))
        (X.B1rho (Geo := Geo))
        (X.B0rho_ne_B1rho
          (Geo := Geo))
        x

  have hCong :
      (PlaneGeo Geo X.rho0).Congruent
        O1 P1 O2 P2 := by
    rw [<- hO, <- hP]
    exact
      hilbert_congruent_reflexive
        (PlaneGeo Geo X.rho0)
        O1 P1

  have hClassEq :
      hilbertPositiveSegmentClassOf
          (PlaneGeo Geo X.rho0)
          O1 P1 hLeftNe
        =
      hilbertPositiveSegmentClassOf
          (PlaneGeo Geo X.rho0)
          O2 P2 hRightNe := by
    exact Quotient.sound hCong

  exact hClassEq.trans h

end HilbertXI25SolidCutWitness


namespace HilbertXI25SolidCutWitness

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [SP : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := SP)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := SP)]
  [HSE : HilbertSpaceEuclidean Geo]


theorem widthSolid_equivalent_left_of_less_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25SolidEquivalent
      Geo
      (X.widthSolid_wyler (Geo := Geo) x)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).leftSolid
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25SolidEquivalent
        Geo
        (X.widthSolid_wyler (Geo := Geo) x)
        (X.widthSolid_wyler (Geo := Geo) x) :=
    hilbertXI25SolidEquivalent_refl_space
      (Geo := Geo)
      (X.widthSolid_wyler (Geo := Geo) x)

  simpa
    [widthSolid_wyler,
     widthXI24_wyler,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.leftSolid,
     HilbertXI25SolidCutWitness.leftXI24,
     hilbert_XI25_twoSlab_XI24_wyler,
     hilbertXI24ParallelepipedFaces]
    using hRefl


/--
The canonical base and the left base of the cut generated by `x<y`
are equivalent.
-/
theorem widthBase_equivalent_left_of_less_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25BaseEquivalent
      Geo
      (X.widthBase_wyler (Geo := Geo) x)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).leftBase
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25BaseEquivalent
        Geo
        (X.widthBase_wyler (Geo := Geo) x)
        (X.widthBase_wyler (Geo := Geo) x) :=
    hilbertXI25BaseEquivalent_refl_space
      (Geo := Geo)
      (X.widthBase_wyler (Geo := Geo) x)

  simpa
    [widthBase_wyler,
     widthSolid_wyler,
     widthXI24_wyler,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.leftBase,
     HilbertXI25SolidCutWitness.leftSolid,
     HilbertXI25SolidCutWitness.leftXI24,
     hilbert_XI25_twoSlab_XI24_wyler,
     hilbertXI24ParallelepipedFaces,
     HilbertXI25BaseEquivalent]
    using hRefl


/--
The canonical solid of width `y` and the whole solid of the cut
generated by `x<y` are XI.Def.10-equivalent.
-/
theorem widthSolid_equivalent_whole_of_less_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25SolidEquivalent
      Geo
      (X.widthSolid_wyler (Geo := Geo) y)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).wholeSolid
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25SolidEquivalent
        Geo
        (X.widthSolid_wyler (Geo := Geo) y)
        (X.widthSolid_wyler (Geo := Geo) y) :=
    hilbertXI25SolidEquivalent_refl_space
      (Geo := Geo)
      (X.widthSolid_wyler (Geo := Geo) y)

  simpa
    [widthSolid_wyler,
     widthXI24_wyler,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.wholeSolid,
     HilbertXI25SolidCutWitness.wholeXI24,
     hilbert_XI25_whole_XI24_wyler,
     hilbertXI24ParallelepipedFaces]
    using hRefl


/--
The canonical base of width `y` and the whole base of the cut
generated by `x<y` are equivalent.
-/
theorem widthBase_equivalent_whole_of_less_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25BaseEquivalent
      Geo
      (X.widthBase_wyler (Geo := Geo) y)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).wholeBase
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25BaseEquivalent
        Geo
        (X.widthBase_wyler (Geo := Geo) y)
        (X.widthBase_wyler (Geo := Geo) y) :=
    hilbertXI25BaseEquivalent_refl_space
      (Geo := Geo)
      (X.widthBase_wyler (Geo := Geo) y)

  simpa
    [widthBase_wyler,
     widthSolid_wyler,
     widthXI24_wyler,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.wholeBase,
     HilbertXI25SolidCutWitness.wholeSolid,
     HilbertXI25SolidCutWitness.wholeXI24,
     hilbert_XI25_whole_XI24_wyler,
     hilbertXI24ParallelepipedFaces,
     HilbertXI25BaseEquivalent]
    using hRefl


end HilbertXI25SolidCutWitness



namespace HilbertXI25SolidCutWitness

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [SP : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := SP)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := SP)]
  [HSE : HilbertSpaceEuclidean Geo]

/--
Every strict width comparison is realized by one actual aligned proper
part witness between the Wyler canonical bases and solids.
-/
theorem alignedProperPartWitness_of_width_less_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25AlignedProperPartWitness
      (Geo := Geo)
      (X.widthBase_wyler (Geo := Geo) x)
      (X.widthSolid_wyler (Geo := Geo) x)
      (X.widthBase_wyler (Geo := Geo) y)
      (X.widthSolid_wyler (Geo := Geo) y) := by

  let cut :=
    X.solidCutWitness_of_width_less
      (Geo := Geo)
      x y hxy

  exact
    Exists.intro cut
      (And.intro
        (Or.inl
          (And.intro
            (X.widthBase_equivalent_left_of_less_wyler
              (Geo := Geo)
              x y hxy)
            (X.widthSolid_equivalent_left_of_less_wyler
              (Geo := Geo)
              x y hxy)))
        (And.intro
          (X.widthBase_equivalent_whole_of_less_wyler
            (Geo := Geo)
            x y hxy)
          (X.widthSolid_equivalent_whole_of_less_wyler
            (Geo := Geo)
            x y hxy)))


/--
A seed nontrivial cut canonically generates the full Hilbert-Wyler
realization of every positive width in its carrier plane.
-/
noncomputable def toWidthRealization_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI25WidthRealization
      (Geo := Geo) X.rho0 where

  baseRep :=
    X.widthBase_wyler
      (Geo := Geo)

  solidRep :=
    X.widthSolid_wyler
      (Geo := Geo)

  solid_rho0 := by
    intro x
    rfl

  base_b_on := by
    intro x
    exact
      X.widthBase_b_on_rho0_wyler
        (Geo := Geo) x

  base_c_on := by
    intro x
    exact
      X.widthBase_c_on_rho0_wyler
        (Geo := Geo) x

  width_spec := by
    intro x
    exact
      X.widthBase_widthClass_wyler
        (Geo := Geo) x

  cut_of_less := by
    intro x y hxy

    exact
      X.alignedProperPartWitness_of_width_less_wyler
        (Geo := Geo)
        x y hxy

end HilbertXI25SolidCutWitness


namespace HilbertXI25SolidCutWitness

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [SP : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := SP)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := SP)]
  [HSE : HilbertSpaceEuclidean Geo]

/--
Euclid XI.25 through the Hilbert-Wyler route.

A single nontrivial seed cut generates the concrete Wyler realization
of every positive width.  The resulting base and solid magnitude
families satisfy Eudoxus V.Def.5 by the shared XI.25 comparison
machinery.
-/
theorem eudoxusProportion_from_seed_cut_wyler
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    EudoxusProportionBetween
      ((X.toWidthRealization_wyler
        (Geo := Geo)).toComparisonFaithfulFamily
          (Geo := Geo)).baseEudoxusMagnitude
      ((X.toWidthRealization_wyler
        (Geo := Geo)).toComparisonFaithfulFamily
          (Geo := Geo)).solidEudoxusMagnitude
      a b a b := by

  exact
    (X.toWidthRealization_wyler
      (Geo := Geo)).eudoxusProportion
        (Geo := Geo)
        a b

end HilbertXI25SolidCutWitness


end Geometry

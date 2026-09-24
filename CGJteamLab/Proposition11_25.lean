import CGJteamLab.Proposition11_15
import CGJteamLab.Proposition11_24

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.25 - geometric core

Production file for Euclid, Book XI, Proposition 25.

This first production stage contains the concrete geometry needed for
Euclid's repeated equal-width construction:

* two adjacent parallelepipedal slabs cut by three parallel planes;
* the source order of the successive sections;
* propagation of equal consecutive widths to all longitudinal edges;
* equality of the two relevant adjacent side faces;
* equality of two adjacent elementary parallelepipedal blocks in the
  sense of XI.Def.10.

General Book XI infrastructure is imported from `HilbertInterfaceXI`
through Proposition XI.24. In particular, carrier-plane transport,
I.29, spatial SAS, XI.Def.10, and the spatial algebra of
`HilbertParallelogramFaceEqual` are not reproved here.

No coordinates, numerical area, or numerical volume are introduced.
-/


/-!
# Euclid XI.25 - two adjacent parallelepipedal slabs

The geometric core of XI.25 uses three parallel section planes

    pi0 || pi1 || pi2

and two fixed pairs of parallel side planes

    rho0   || rho1,
    sigma0 || sigma1.

Each section plane contains four corner points:

    A_i = pi_i cap rho0 cap sigma1
    B_i = pi_i cap rho0 cap sigma0
    C_i = pi_i cap rho1 cap sigma0
    D_i = pi_i cap rho1 cap sigma1.

Thus the twelve vertices determine two adjacent parallelepipeds:

    left  slab : pi0 ... pi1,
    right slab : pi1 ... pi2.

This is the local geometry used repeatedly in Euclid XI.25.
-/

/--
Twelve-vertex configuration of two adjacent parallelepipedal slabs.

No metric equality between the two widths is imposed here.  This
structure contains only the incidence and parallel-plane data needed
to recognize the two solids and apply XI.24 to each one.
-/
structure HilbertXI25TwoSlabConfiguration
    [S : HilbertSpacePrimitive Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point) : Prop where

  pi01_parallel :
    HilbertSpacePlanesParallelIncidence Geo pi0 pi1

  pi12_parallel :
    HilbertSpacePlanesParallelIncidence Geo pi1 pi2

  pi02_parallel :
    HilbertSpacePlanesParallelIncidence Geo pi0 pi2

  rho_parallel :
    HilbertSpacePlanesParallelIncidence Geo rho0 rho1

  sigma_parallel :
    HilbertSpacePlanesParallelIncidence Geo sigma0 sigma1

  A0_on :
    S.OnPlane A0 pi0 /\
    S.OnPlane A0 rho0 /\
    S.OnPlane A0 sigma1

  B0_on :
    S.OnPlane B0 pi0 /\
    S.OnPlane B0 rho0 /\
    S.OnPlane B0 sigma0

  C0_on :
    S.OnPlane C0 pi0 /\
    S.OnPlane C0 rho1 /\
    S.OnPlane C0 sigma0

  D0_on :
    S.OnPlane D0 pi0 /\
    S.OnPlane D0 rho1 /\
    S.OnPlane D0 sigma1

  A1_on :
    S.OnPlane A1 pi1 /\
    S.OnPlane A1 rho0 /\
    S.OnPlane A1 sigma1

  B1_on :
    S.OnPlane B1 pi1 /\
    S.OnPlane B1 rho0 /\
    S.OnPlane B1 sigma0

  C1_on :
    S.OnPlane C1 pi1 /\
    S.OnPlane C1 rho1 /\
    S.OnPlane C1 sigma0

  D1_on :
    S.OnPlane D1 pi1 /\
    S.OnPlane D1 rho1 /\
    S.OnPlane D1 sigma1

  A2_on :
    S.OnPlane A2 pi2 /\
    S.OnPlane A2 rho0 /\
    S.OnPlane A2 sigma1

  B2_on :
    S.OnPlane B2 pi2 /\
    S.OnPlane B2 rho0 /\
    S.OnPlane B2 sigma0

  C2_on :
    S.OnPlane C2 pi2 /\
    S.OnPlane C2 rho1 /\
    S.OnPlane C2 sigma0

  D2_on :
    S.OnPlane D2 pi2 /\
    S.OnPlane D2 rho1 /\
    S.OnPlane D2 sigma1

/--
The left slab, between `pi0` and `pi1`, is a standard XI.24
parallelepipedal configuration.
-/
theorem HilbertXI25TwoSlabConfiguration.leftConfiguration
    [S : HilbertSpacePrimitive Geo]
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
    HilbertParallelepipedConfiguration
      (Geo := Geo)
      pi0 pi1
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1 := by

  exact
    {
      pi_parallel := h.pi01_parallel
      rho_parallel := h.rho_parallel
      sigma_parallel := h.sigma_parallel

      A_on := h.A0_on
      B_on := h.B0_on
      C_on := h.C0_on
      D_on := h.D0_on

      E_on := h.A1_on
      F_on := h.B1_on
      G_on := h.C1_on
      H_on := h.D1_on
    }

/--
The right slab, between `pi1` and `pi2`, is a standard XI.24
parallelepipedal configuration.
-/
theorem HilbertXI25TwoSlabConfiguration.rightConfiguration
    [S : HilbertSpacePrimitive Geo]
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
    HilbertParallelepipedConfiguration
      (Geo := Geo)
      pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A1 B1 C1 D1
      A2 B2 C2 D2 := by

  exact
    {
      pi_parallel := h.pi12_parallel
      rho_parallel := h.rho_parallel
      sigma_parallel := h.sigma_parallel

      A_on := h.A1_on
      B_on := h.B1_on
      C_on := h.C1_on
      D_on := h.D1_on

      E_on := h.A2_on
      F_on := h.B2_on
      G_on := h.C2_on
      H_on := h.D2_on
    }

/--
The whole slab, between `pi0` and `pi2`, is itself a standard XI.24
parallelepipedal configuration.

This is the geometric whole containing the left and right adjacent slabs.
It is the configuration needed later for the XI.25 `whole > proper part`
step.
-/
theorem HilbertXI25TwoSlabConfiguration.wholeConfiguration
    [S : HilbertSpacePrimitive Geo]
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
    HilbertParallelepipedConfiguration
      (Geo := Geo)
      pi0 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A2 B2 C2 D2 := by

  exact
    {
      pi_parallel := h.pi02_parallel
      rho_parallel := h.rho_parallel
      sigma_parallel := h.sigma_parallel

      A_on := h.A0_on
      B_on := h.B0_on
      C_on := h.C0_on
      D_on := h.D0_on

      E_on := h.A2_on
      F_on := h.B2_on
      G_on := h.C2_on
      H_on := h.D2_on
    }

/--
XI.24 applied to both adjacent slabs.

This theorem is the bridge from the twelve-vertex XI.25 configuration
to the already completed production theorem XI.24.
-/
theorem hilbert_XI25_twoSlab_XI24
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
    euclid_proposition_11_24
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
    euclid_proposition_11_24
      (Geo := Geo)
      pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A1 B1 C1 D1
      A2 B2 C2 D2
      hRightCfg

  exact And.intro hLeft hRight


/--
XI.24 applied to the whole slab between `pi0` and `pi2`.

Together with `hilbert_XI25_twoSlab_XI24`, this puts the left part,
right remainder, and whole solid on the same XI.Def.10 face API.
-/
theorem hilbert_XI25_whole_XI24
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
    euclid_proposition_11_24
      (Geo := Geo)
      pi0 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A2 B2 C2 D2
      hWholeCfg


/-!
# Euclid XI.25 - ordered adjacent slabs

The source proof of XI.25 does not merely use three parallel section
planes.  The successive sections occur in a definite order along the
four longitudinal edges.

For two adjacent slabs we therefore record

    A0 - A1 - A2,
    B0 - B1 - B2,
    C0 - C1 - C2,
    D0 - D1 - D2.

The present file also proves the first metric propagation lemma:
if the two consecutive widths are equal on one longitudinal edge,
then XI.24 and I.34 force equality of the corresponding consecutive
widths on all four longitudinal edges.
-/

/--
Ordered form of the two-slab XI.25 configuration.
-/
structure HilbertXI25OrderedTwoSlabConfiguration
    [S : HilbertSpacePrimitive Geo]
    (pi0 pi1 pi2 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A0 B0 C0 D0
     A1 B1 C1 D1
     A2 B2 C2 D2 : Geo.Point) : Prop where

  slab :
    HilbertXI25TwoSlabConfiguration
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2

  between_A :
    Geo.Between A0 A1 A2

  between_B :
    Geo.Between B0 B1 B2

  between_C :
    Geo.Between C0 C1 C2

  between_D :
    Geo.Between D0 D1 D2

/--
Equality of consecutive widths on the A-edge propagates to the B-edge.

This is the first metric transport needed for the adjacent-face
congruence step in XI.25.
-/
theorem hilbert_XI25_equal_width_B
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
    hilbert_XI25_twoSlab_XI24
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
theorem hilbert_XI25_equal_width_C
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
    hilbert_XI25_twoSlab_XI24
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
    hilbert_XI25_equal_width_B
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
theorem hilbert_XI25_equal_width_D
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
    hilbert_XI25_twoSlab_XI24
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
theorem hilbert_XI25_equal_width_all_edges
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
      (hilbert_XI25_equal_width_B
        (Geo := Geo)
        pi0 pi1 pi2
        rho0 rho1
        sigma0 sigma1
        A0 B0 C0 D0
        A1 B1 C1 D1
        A2 B2 C2 D2
        h hWidthA)
      (And.intro
        (hilbert_XI25_equal_width_C
          (Geo := Geo)
          pi0 pi1 pi2
          rho0 rho1
          sigma0 sigma1
          A0 B0 C0 D0
          A1 B1 C1 D1
          A2 B2 C2 D2
          h hWidthA)
        (hilbert_XI25_equal_width_D
          (Geo := Geo)
          pi0 pi1 pi2
          rho0 rho1
          sigma0 sigma1
          A0 B0 C0 D0
          A1 B1 C1 D1
          A2 B2 C2 D2
          h hWidthA))


/-!
# Adjacent side faces

The geometric content has already been isolated in
`hilbert_space_adjacent_parallelogram_triangle_congruent_XI`.
The two wrappers below only package its canonical diagonal-triangle
congruence as `HilbertParallelogramFaceEqual` for the two side-face
directions used in XI.25.
-/

theorem hilbert_XI25_adjacent_rho_face_equal
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (rho0 : S.Plane)
    (A0 B0 B1 A1 B2 A2 : Geo.Point)
    (hA0rho : S.OnPlane A0 rho0)
    (hB0rho : S.OnPlane B0 rho0)
    (hB1rho : S.OnPlane B1 rho0)
    (hA1rho : S.OnPlane A1 rho0)
    (hB2rho : S.OnPlane B2 rho0)
    (hLeft : IsParallelogram Geo A0 B0 B1 A1)
    (hRight : IsParallelogram Geo A1 B1 B2 A2)
    (hBetween : Geo.Between B0 B1 B2)
    (hWidth : Geo.Congruent B0 B1 B1 B2) :
    HilbertParallelogramFaceEqual
      Geo
      {
        a := A0
        b := B0
        c := B1
        d := A1
        isParallelogram := hLeft
      }
      {
        a := A1
        b := B1
        c := B2
        d := A2
        isParallelogram := hRight
      } := by

  change
    TriangleCongruenceResult
      Geo B0 A0 B1 B1 A1 B2

  exact
    hilbert_space_adjacent_parallelogram_triangle_congruent_XI
      (Geo := Geo)
      rho0
      A0 B0 B1 A1 B2 A2
      hA0rho
      hB0rho
      hB1rho
      hA1rho
      hB2rho
      hLeft
      hRight
      hBetween
      hWidth

theorem hilbert_XI25_adjacent_sigma_face_equal
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (sigma0 : S.Plane)
    (C0 B0 B1 C1 B2 C2 : Geo.Point)
    (hC0sigma : S.OnPlane C0 sigma0)
    (hB0sigma : S.OnPlane B0 sigma0)
    (hB1sigma : S.OnPlane B1 sigma0)
    (hC1sigma : S.OnPlane C1 sigma0)
    (hB2sigma : S.OnPlane B2 sigma0)
    (hLeft : IsParallelogram Geo C0 B0 B1 C1)
    (hRight : IsParallelogram Geo C1 B1 B2 C2)
    (hBetween : Geo.Between B0 B1 B2)
    (hWidth : Geo.Congruent B0 B1 B1 B2) :
    HilbertParallelogramFaceEqual
      Geo
      {
        a := C0
        b := B0
        c := B1
        d := C1
        isParallelogram := hLeft
      }
      {
        a := C1
        b := B1
        c := B2
        d := C2
        isParallelogram := hRight
      } := by

  exact
    hilbert_XI25_adjacent_rho_face_equal
      (Geo := Geo)
      sigma0
      C0 B0 B1 C1 B2 C2
      hC0sigma
      hB0sigma
      hB1sigma
      hC1sigma
      hB2sigma
      hLeft
      hRight
      hBetween
      hWidth


/-!
# Equality of adjacent elementary solids

For equal consecutive widths, XI.24 supplies opposite-face equalities,
the middle section is a common face, and the two side-face equalities
come from the preceding wrappers. XI.Def.10 then identifies the two
elementary parallelepipedal blocks.
-/

theorem hilbert_XI25_adjacent_elementary_solids_equal
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
      hilbert_XI25_twoSlab_XI24
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
    hilbert_XI25_twoSlab_XI24
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
    hilbert_XI25_equal_width_B
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


/-!
# XI.25 spatial magnitude layer

The geometric core of XI.25 is genuinely spatial and uses
`HilbertSpaceCongruence`, not a global planar `HilbertCongruence Geo`.

Accordingly, the quotient classes below are built from the spatial
algebra of `HilbertParallelogramFaceEqual`.

For the one-dimensional width magnitude we work inside one fixed
carrier plane `rho`.  The induced geometry `PlaneGeo Geo rho` has the
ordinary planar `HilbertCongruence` instance inherited from the spatial
Group III structure, so the Book V positive-segment machinery applies
there without installing any global planar structure on the ambient
three-space.
-/

/--
Concrete six-face parallelepiped object used by XI.25.
-/
abbrev HilbertXI25Parallelepiped :=
  HilbertParallelepipedFaces
    (HilbertParallelogramFace Geo)

/--
XI.Def.10 equivalence relation on concrete parallelepipeds.
-/
def HilbertXI25SolidEquivalent
    (S T : HilbertXI25Parallelepiped Geo) : Prop :=
  HilbertXI10EqualSimilarParallelepiped
    (HilbertParallelogramFaceEqual Geo)
    S T

/--
Spatial reflexivity of XI.Def.10 solid equivalence.
-/
theorem hilbertXI25SolidEquivalent_refl_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (T : HilbertXI25Parallelepiped Geo) :
    HilbertXI25SolidEquivalent Geo T T := by

  intro i

  exact
    hilbertParallelogramFaceEqual_refl_space
      (Geo := Geo)
      (T.faceAt i)

/--
Spatial symmetry of XI.Def.10 solid equivalence.
-/
theorem hilbertXI25SolidEquivalent_symm_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {T U : HilbertXI25Parallelepiped Geo}
    (h : HilbertXI25SolidEquivalent Geo T U) :
    HilbertXI25SolidEquivalent Geo U T := by

  intro i

  exact
    hilbertParallelogramFaceEqual_symm_space
      (Geo := Geo)
      (h i)

/--
Spatial transitivity of XI.Def.10 solid equivalence.
-/
theorem hilbertXI25SolidEquivalent_trans_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {R T U : HilbertXI25Parallelepiped Geo}
    (hRT : HilbertXI25SolidEquivalent Geo R T)
    (hTU : HilbertXI25SolidEquivalent Geo T U) :
    HilbertXI25SolidEquivalent Geo R U := by

  intro i

  exact
    hilbertParallelogramFaceEqual_trans_space
      (Geo := Geo)
      (hRT i)
      (hTU i)

/--
Spatial setoid of concrete parallelepipeds modulo XI.Def.10.
-/
def hilbertXI25SolidSetoid
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)] :
    Setoid (HilbertXI25Parallelepiped Geo) where

  r :=
    HilbertXI25SolidEquivalent Geo

  iseqv :=
    {
      refl :=
        hilbertXI25SolidEquivalent_refl_space
          (Geo := Geo)

      symm := by
        intro T U h
        exact
          hilbertXI25SolidEquivalent_symm_space
            (Geo := Geo)
            h

      trans := by
        intro R T U hRT hTU
        exact
          hilbertXI25SolidEquivalent_trans_space
            (Geo := Geo)
            hRT hTU
    }

/--
Synthetic spatial solid magnitude for XI.25.
-/
abbrev HilbertXI25SolidClass
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)] :=
  Quotient
    (hilbertXI25SolidSetoid
      (Geo := Geo))

/--
The XI.Def.10 magnitude class represented by a concrete parallelepiped.
-/
def hilbertXI25SolidClassOf
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (T : HilbertXI25Parallelepiped Geo) :
    HilbertXI25SolidClass Geo :=
  Quotient.mk'
    (s := hilbertXI25SolidSetoid
      (Geo := Geo))
    T

/--
XI.Def.10-equivalent concrete solids define the same spatial solid
magnitude class.
-/
theorem hilbertXI25SolidClass_eq_of_equivalent
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {T U : HilbertXI25Parallelepiped Geo}
    (h : HilbertXI25SolidEquivalent Geo T U) :
    hilbertXI25SolidClassOf
        (Geo := Geo) T
      =
    hilbertXI25SolidClassOf
        (Geo := Geo) U := by

  exact Quotient.sound h

/--
Two XI.24 parallelepipeds are equal in the XI.Def.10 sense once three
corresponding faces, one from each opposite pair, are equal.

This version is genuinely spatial.
-/
theorem hilbert_XI25_equalSolid_of_three_corresponding_faces
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D E F G Hpt : Geo.Point)
    (A' B' C' D' E' F' G' H' : Geo.Point)
    (hT :
      HilbertXI24Conclusion
        Geo
        A B C D E F G Hpt)
    (hU :
      HilbertXI24Conclusion
        Geo
        A' B' C' D' E' F' G' H')
    (hPi0 :
      HilbertParallelogramFaceEqual
        Geo
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT).pi0
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU).pi0)
    (hRho0 :
      HilbertParallelogramFaceEqual
        Geo
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT).rho0
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU).rho0)
    (hSigma0 :
      HilbertParallelogramFaceEqual
        Geo
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT).sigma0
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU).sigma0) :
    HilbertXI10EqualSimilarParallelepiped
      (HilbertParallelogramFaceEqual Geo)
      (hilbertXI24ParallelepipedFaces
        (Geo := Geo)
        A B C D E F G Hpt hT)
      (hilbertXI24ParallelepipedFaces
        (Geo := Geo)
        A' B' C' D' E' F' G' H' hU) := by

  let T :=
    hilbertXI24ParallelepipedFaces
      (Geo := Geo)
      A B C D E F G Hpt hT

  let U :=
    hilbertXI24ParallelepipedFaces
      (Geo := Geo)
      A' B' C' D' E' F' G' H' hU

  have hTOpp :
      HilbertParallelogramFaceEqual Geo T.pi0 T.pi1 /\
      HilbertParallelogramFaceEqual Geo T.rho0 T.rho1 /\
      HilbertParallelogramFaceEqual Geo T.sigma0 T.sigma1 := by
    simpa [T] using
      hilbertXI24_oppositeFaceEqualities_for_XI10
        (Geo := Geo)
        A B C D E F G Hpt
        hT

  have hUOpp :
      HilbertParallelogramFaceEqual Geo U.pi0 U.pi1 /\
      HilbertParallelogramFaceEqual Geo U.rho0 U.rho1 /\
      HilbertParallelogramFaceEqual Geo U.sigma0 U.sigma1 := by
    simpa [U] using
      hilbertXI24_oppositeFaceEqualities_for_XI10
        (Geo := Geo)
        A' B' C' D' E' F' G' H'
        hU

  have hPi0' :
      HilbertParallelogramFaceEqual
        Geo T.pi0 U.pi0 := by
    simpa [T, U] using hPi0

  have hRho0' :
      HilbertParallelogramFaceEqual
        Geo T.rho0 U.rho0 := by
    simpa [T, U] using hRho0

  have hSigma0' :
      HilbertParallelogramFaceEqual
        Geo T.sigma0 U.sigma0 := by
    simpa [T, U] using hSigma0

  have hSolid :
      HilbertXI10EqualSimilarParallelepiped
        (HilbertParallelogramFaceEqual Geo)
        T U := by

    exact
      hilbertXI10EqualSimilarParallelepiped_of_three_adjacent
        (HilbertParallelogramFaceEqual Geo)
        (fun h =>
          hilbertParallelogramFaceEqual_symm_space
            (Geo := Geo) h)
        (fun h1 h2 =>
          hilbertParallelogramFaceEqual_trans_space
            (Geo := Geo) h1 h2)
        T U
        hTOpp.1
        hTOpp.2.1
        hTOpp.2.2
        hUOpp.1
        hUOpp.2.1
        hUOpp.2.2
        hPi0'
        hRho0'
        hSigma0'

  simpa [T, U] using hSolid

/--
Three corresponding face equalities therefore give equality of spatial
solid magnitude classes.
-/
theorem hilbert_XI25_solidClass_eq_of_three_corresponding_faces
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D E F G Hpt : Geo.Point)
    (A' B' C' D' E' F' G' H' : Geo.Point)
    (hT :
      HilbertXI24Conclusion
        Geo
        A B C D E F G Hpt)
    (hU :
      HilbertXI24Conclusion
        Geo
        A' B' C' D' E' F' G' H')
    (hPi0 :
      HilbertParallelogramFaceEqual
        Geo
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT).pi0
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU).pi0)
    (hRho0 :
      HilbertParallelogramFaceEqual
        Geo
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT).rho0
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU).rho0)
    (hSigma0 :
      HilbertParallelogramFaceEqual
        Geo
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT).sigma0
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU).sigma0) :
    hilbertXI25SolidClassOf
        (Geo := Geo)
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A B C D E F G Hpt hT)
      =
    hilbertXI25SolidClassOf
        (Geo := Geo)
        (hilbertXI24ParallelepipedFaces
          (Geo := Geo)
          A' B' C' D' E' F' G' H' hU) := by

  apply
    hilbertXI25SolidClass_eq_of_equivalent
      (Geo := Geo)

  exact
    hilbert_XI25_equalSolid_of_three_corresponding_faces
      (Geo := Geo)
      A B C D E F G Hpt
      A' B' C' D' E' F' G' H'
      hT hU
      hPi0 hRho0 hSigma0

------------------------------------------------------------------------
-- Base magnitude classes
------------------------------------------------------------------------

/--
XI.24 face equality, viewed as an equivalence relation on concrete
parallelogram faces.
-/
def HilbertXI25BaseEquivalent
    (P Q : HilbertParallelogramFace Geo) : Prop :=
  HilbertParallelogramFaceEqual Geo P Q

theorem hilbertXI25BaseEquivalent_refl_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P : HilbertParallelogramFace Geo) :
    HilbertXI25BaseEquivalent Geo P P := by

  exact
    hilbertParallelogramFaceEqual_refl_space
      (Geo := Geo)
      P

theorem hilbertXI25BaseEquivalent_symm_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {P Q : HilbertParallelogramFace Geo}
    (h : HilbertXI25BaseEquivalent Geo P Q) :
    HilbertXI25BaseEquivalent Geo Q P := by

  exact
    hilbertParallelogramFaceEqual_symm_space
      (Geo := Geo)
      h

theorem hilbertXI25BaseEquivalent_trans_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {P Q R : HilbertParallelogramFace Geo}
    (hPQ : HilbertXI25BaseEquivalent Geo P Q)
    (hQR : HilbertXI25BaseEquivalent Geo Q R) :
    HilbertXI25BaseEquivalent Geo P R := by

  exact
    hilbertParallelogramFaceEqual_trans_space
      (Geo := Geo)
      hPQ hQR

def hilbertXI25BaseSetoid
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)] :
    Setoid (HilbertParallelogramFace Geo) where

  r :=
    HilbertXI25BaseEquivalent Geo

  iseqv :=
    {
      refl :=
        hilbertXI25BaseEquivalent_refl_space
          (Geo := Geo)

      symm := by
        intro P Q h
        exact
          hilbertXI25BaseEquivalent_symm_space
            (Geo := Geo)
            h

      trans := by
        intro P Q R hPQ hQR
        exact
          hilbertXI25BaseEquivalent_trans_space
            (Geo := Geo)
            hPQ hQR
    }

abbrev HilbertXI25BaseClass
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)] :=
  Quotient
    (hilbertXI25BaseSetoid
      (Geo := Geo))

def hilbertXI25BaseClassOf
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (P : HilbertParallelogramFace Geo) :
    HilbertXI25BaseClass Geo :=
  Quotient.mk'
    (s := hilbertXI25BaseSetoid
      (Geo := Geo))
    P

theorem hilbertXI25BaseClass_eq_of_faceEqual
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {P Q : HilbertParallelogramFace Geo}
    (h : HilbertParallelogramFaceEqual Geo P Q) :
    hilbertXI25BaseClassOf
        (Geo := Geo) P
      =
    hilbertXI25BaseClassOf
        (Geo := Geo) Q := by

  exact Quotient.sound h

------------------------------------------------------------------------
-- Width classes inside one carrier plane
------------------------------------------------------------------------

/--
Positive width magnitude in one fixed carrier plane.
-/
abbrev HilbertXI25WidthClass
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane) :=
  HilbertPositiveSegmentClass
    (PlaneGeo Geo rho)

/--
The positive width class represented by a nondegenerate ambient
segment AB contained in rho.
-/
noncomputable def hilbert_XI25_widthClass
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane)
    (A B : Geo.Point)
    (hArho : S.OnPlane A rho)
    (hBrho : S.OnPlane B rho)
    (hAB : Ne A B) :
    HilbertXI25WidthClass
      (Geo := Geo) rho := by

  let Ap : PlanePoint Geo rho :=
    { val := A, property := hArho }

  let Bp : PlanePoint Geo rho :=
    { val := B, property := hBrho }

  have hApBp : Ne Ap Bp := by
    intro hEq
    apply hAB
    exact congrArg Subtype.val hEq

  exact
    hilbertPositiveSegmentClassOf
      (PlaneGeo Geo rho)
      Ap Bp hApBp

/--
Ambiently congruent segments in one carrier plane determine the same
positive width class.
-/
theorem hilbert_XI25_widthClass_eq_of_congruent
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane)
    (A B C D : Geo.Point)
    (hArho : S.OnPlane A rho)
    (hBrho : S.OnPlane B rho)
    (hCrho : S.OnPlane C rho)
    (hDrho : S.OnPlane D rho)
    (hAB : Ne A B)
    (hCD : Ne C D)
    (hCong : Geo.Congruent A B C D) :
    hilbert_XI25_widthClass
        (Geo := Geo)
        rho A B hArho hBrho hAB
      =
    hilbert_XI25_widthClass
        (Geo := Geo)
        rho C D hCrho hDrho hCD := by

  let Ap : PlanePoint Geo rho :=
    { val := A, property := hArho }

  let Bp : PlanePoint Geo rho :=
    { val := B, property := hBrho }

  let Cp : PlanePoint Geo rho :=
    { val := C, property := hCrho }

  let Dp : PlanePoint Geo rho :=
    { val := D, property := hDrho }

  have hApBp : Ne Ap Bp := by
    intro hEq
    apply hAB
    exact congrArg Subtype.val hEq

  have hCpDp : Ne Cp Dp := by
    intro hEq
    apply hCD
    exact congrArg Subtype.val hEq

  have hPlaneCong :
      (PlaneGeo Geo rho).Congruent
        Ap Bp Cp Dp :=
    (planeGeo_congruent
      (Geo := Geo)
      rho Ap Bp Cp Dp).mpr
      hCong

  have hClass :
      hilbertPositiveSegmentClassOf
          (PlaneGeo Geo rho)
          Ap Bp hApBp
        =
      hilbertPositiveSegmentClassOf
          (PlaneGeo Geo rho)
          Cp Dp hCpDp := by
    exact Quotient.sound hPlaneCong

  simpa
    [hilbert_XI25_widthClass, Ap, Bp, Cp, Dp]
    using hClass

------------------------------------------------------------------------
-- Local width-generated family
------------------------------------------------------------------------

/--
A local XI.25 family based on positive width magnitudes in a fixed
carrier plane rho.
-/
structure HilbertXI25LocalFamily
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane) where

  baseAt :
    HilbertXI25WidthClass
        (Geo := Geo) rho ->
      HilbertXI25BaseClass Geo

  solidAt :
    HilbertXI25WidthClass
        (Geo := Geo) rho ->
      HilbertXI25SolidClass Geo

structure HilbertXI25GeneratedBaseMagnitude
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho) where

  width :
    HilbertXI25WidthClass
      (Geo := Geo) rho

structure HilbertXI25GeneratedSolidMagnitude
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho) where

  width :
    HilbertXI25WidthClass
      (Geo := Geo) rho

namespace HilbertXI25LocalFamily

variable
  [H : HilbertIncidence Geo]
  [HilbertOrder Geo]
  [S : HilbertSpacePrimitive Geo]
  [HSI : HilbertSpaceIncidence Geo]
  [HSO : HilbertSpaceOrder
    (Geo := Geo) (H := H) (S := S)]
  [HSC : HilbertSpaceCongruence
    (Geo := Geo) (H := H) (S := S)]

noncomputable def generatedBaseEudoxusMagnitude
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho) :
    EudoxusMagnitude
      (HilbertXI25GeneratedBaseMagnitude
        (Geo := Geo) F) where

  less :=
    fun x y =>
      HilbertPositiveSegmentLess
        (PlaneGeo Geo rho)
        x.width y.width

  multiple :=
    fun n x =>
      {
        width :=
          hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho)
            n x.width
      }

noncomputable def generatedSolidEudoxusMagnitude
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho) :
    EudoxusMagnitude
      (HilbertXI25GeneratedSolidMagnitude
        (Geo := Geo) F) where

  less :=
    fun x y =>
      HilbertPositiveSegmentLess
        (PlaneGeo Geo rho)
        x.width y.width

  multiple :=
    fun n x =>
      {
        width :=
          hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho)
            n x.width
      }

noncomputable def widthToGeneratedBase
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho) :
    EudoxusMagnitudeEmbedding
      (hilbertPositiveSegmentEudoxusMagnitude
        (Geo := PlaneGeo Geo rho))
      (generatedBaseEudoxusMagnitude
        (Geo := Geo) F) where

  toFun :=
    fun a => { width := a }

  map_multiple := by
    intro n a
    rfl

  less_iff := by
    intro a b
    rfl

  injective := by
    intro a b h
    exact
      congrArg
        HilbertXI25GeneratedBaseMagnitude.width
        h

noncomputable def widthToGeneratedSolid
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho) :
    EudoxusMagnitudeEmbedding
      (hilbertPositiveSegmentEudoxusMagnitude
        (Geo := PlaneGeo Geo rho))
      (generatedSolidEudoxusMagnitude
        (Geo := Geo) F) where

  toFun :=
    fun a => { width := a }

  map_multiple := by
    intro n a
    rfl

  less_iff := by
    intro a b
    rfl

  injective := by
    intro a b h
    exact
      congrArg
        HilbertXI25GeneratedSolidMagnitude.width
        h

/--
Pure magnitude-theoretic conclusion for a spatial XI.25 local family.
-/
theorem generated_base_solid_proportion
    {rho : S.Plane}
    (F : HilbertXI25LocalFamily
      (Geo := Geo) rho)
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    EudoxusProportionBetween
      (generatedBaseEudoxusMagnitude
        (Geo := Geo) F)
      (generatedSolidEudoxusMagnitude
        (Geo := Geo) F)
      ((widthToGeneratedBase
        (Geo := Geo) F).toFun a)
      ((widthToGeneratedBase
        (Geo := Geo) F).toFun b)
      ((widthToGeneratedSolid
        (Geo := Geo) F).toFun a)
      ((widthToGeneratedSolid
        (Geo := Geo) F).toFun b) := by

  exact
    eudoxusProportionBetween_of_common_source
      (widthToGeneratedBase
        (Geo := Geo) F)
      (widthToGeneratedSolid
        (Geo := Geo) F)
      a b

end HilbertXI25LocalFamily


------------------------------------------------------------------------
-- XI.25: cut witnesses and proper solid parts
------------------------------------------------------------------------

/-!
The missing strict-comparison step in Euclid XI.25 is not introduced
as a numerical volume order.

Instead, a strict solid comparison is witnessed geometrically:
a whole parallelepiped is cut by an interior parallel section into two
nonempty parallelepipeds. Either resulting slab is then a proper part
of the whole.

This is the source-faithful configuration needed for the Euclidean
Common Notion "the whole is greater than the part".
-/

/--
A first-class witness for a nontrivial parallel cut of one
parallelepiped into two adjacent parallelepipedal slabs.

The `ordered` field contains the strict betweenness data on all four
longitudinal edges, hence both pieces are nonempty.
-/
structure HilbertXI25SolidCutWitness
    [SP : HilbertSpacePrimitive Geo] where

  pi0 : SP.Plane
  pi1 : SP.Plane
  pi2 : SP.Plane

  rho0 : SP.Plane
  rho1 : SP.Plane

  sigma0 : SP.Plane
  sigma1 : SP.Plane

  A0 : Geo.Point
  B0 : Geo.Point
  C0 : Geo.Point
  D0 : Geo.Point

  A1 : Geo.Point
  B1 : Geo.Point
  C1 : Geo.Point
  D1 : Geo.Point

  A2 : Geo.Point
  B2 : Geo.Point
  C2 : Geo.Point
  D2 : Geo.Point

  ordered :
    HilbertXI25OrderedTwoSlabConfiguration
      (Geo := Geo)
      pi0 pi1 pi2
      rho0 rho1
      sigma0 sigma1
      A0 B0 C0 D0
      A1 B1 C1 D1
      A2 B2 C2 D2


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
XI.24 data for the left part of a solid cut.
-/
theorem leftXI24
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI24Conclusion
      Geo
      X.A0 X.B0 X.C0 X.D0
      X.A1 X.B1 X.C1 X.D1 :=

  (hilbert_XI25_twoSlab_XI24
    (Geo := Geo)
    X.pi0 X.pi1 X.pi2
    X.rho0 X.rho1
    X.sigma0 X.sigma1
    X.A0 X.B0 X.C0 X.D0
    X.A1 X.B1 X.C1 X.D1
    X.A2 X.B2 X.C2 X.D2
    X.ordered.slab).1

/--
XI.24 data for the right remainder of a solid cut.
-/
theorem rightXI24
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI24Conclusion
      Geo
      X.A1 X.B1 X.C1 X.D1
      X.A2 X.B2 X.C2 X.D2 :=

  (hilbert_XI25_twoSlab_XI24
    (Geo := Geo)
    X.pi0 X.pi1 X.pi2
    X.rho0 X.rho1
    X.sigma0 X.sigma1
    X.A0 X.B0 X.C0 X.D0
    X.A1 X.B1 X.C1 X.D1
    X.A2 X.B2 X.C2 X.D2
    X.ordered.slab).2

/--
XI.24 data for the whole solid spanning the two pieces.
-/
theorem wholeXI24
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI24Conclusion
      Geo
      X.A0 X.B0 X.C0 X.D0
      X.A2 X.B2 X.C2 X.D2 :=

  hilbert_XI25_whole_XI24
    (Geo := Geo)
    X.pi0 X.pi1 X.pi2
    X.rho0 X.rho1
    X.sigma0 X.sigma1
    X.A0 X.B0 X.C0 X.D0
    X.A1 X.B1 X.C1 X.D1
    X.A2 X.B2 X.C2 X.D2
    X.ordered.slab

/--
Canonical six-face object for the left part.
-/
def leftSolid
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI25Parallelepiped Geo :=

  hilbertXI24ParallelepipedFaces
    (Geo := Geo)
    X.A0 X.B0 X.C0 X.D0
    X.A1 X.B1 X.C1 X.D1
    (X.leftXI24 (Geo := Geo))

/--
Canonical six-face object for the right remainder.
-/
def rightSolid
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI25Parallelepiped Geo :=

  hilbertXI24ParallelepipedFaces
    (Geo := Geo)
    X.A1 X.B1 X.C1 X.D1
    X.A2 X.B2 X.C2 X.D2
    (X.rightXI24 (Geo := Geo))

/--
Canonical six-face object for the whole solid.
-/
def wholeSolid
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI25Parallelepiped Geo :=

  hilbertXI24ParallelepipedFaces
    (Geo := Geo)
    X.A0 X.B0 X.C0 X.D0
    X.A2 X.B2 X.C2 X.D2
    (X.wholeXI24 (Geo := Geo))

-- The A-edge of a cut records that the left piece, right piece, and whole
-- are all nondegenerate.
omit [HilbertOrder Geo] HSC HSE in theorem nonempty_A
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    Ne X.A0 X.A1 /\
    Ne X.A1 X.A2 /\
    Ne X.A0 X.A2 := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X.A0 X.A1 X.A2
      X.ordered.between_A

  exact
    And.intro
      hData.1
      (And.intro
        hData.2.1
        hData.2.2.1)

-- The B-edge gives the same nondegeneracy data.
omit [HilbertOrder Geo] HSC HSE in theorem nonempty_B
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    Ne X.B0 X.B1 /\
    Ne X.B1 X.B2 /\
    Ne X.B0 X.B2 := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X.B0 X.B1 X.B2
      X.ordered.between_B

  exact
    And.intro
      hData.1
      (And.intro
        hData.2.1
        hData.2.2.1)

-- The C-edge gives the same nondegeneracy data.
omit [HilbertOrder Geo] HSC HSE in theorem nonempty_C
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    Ne X.C0 X.C1 /\
    Ne X.C1 X.C2 /\
    Ne X.C0 X.C2 := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X.C0 X.C1 X.C2
      X.ordered.between_C

  exact
    And.intro
      hData.1
      (And.intro
        hData.2.1
        hData.2.2.1)

-- The D-edge gives the same nondegeneracy data.
omit [HilbertOrder Geo] HSC HSE in theorem nonempty_D
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    Ne X.D0 X.D1 /\
    Ne X.D1 X.D2 /\
    Ne X.D0 X.D2 := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X.D0 X.D1 X.D2
      X.ordered.between_D

  exact
    And.intro
      hData.1
      (And.intro
        hData.2.1
        hData.2.2.1)

-- Bundled nondegeneracy of all four longitudinal cut edges.
omit [HilbertOrder Geo] HSC HSE in theorem nonempty_all_edges
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    (Ne X.A0 X.A1 /\ Ne X.A1 X.A2 /\ Ne X.A0 X.A2) /\
    (Ne X.B0 X.B1 /\ Ne X.B1 X.B2 /\ Ne X.B0 X.B2) /\
    (Ne X.C0 X.C1 /\ Ne X.C1 X.C2 /\ Ne X.C0 X.C2) /\
    (Ne X.D0 X.D1 /\ Ne X.D1 X.D2 /\ Ne X.D0 X.D2) := by

  exact
    And.intro
      (X.nonempty_A (Geo := Geo))
      (And.intro
        (X.nonempty_B (Geo := Geo))
        (And.intro
          (X.nonempty_C (Geo := Geo))
          (X.nonempty_D (Geo := Geo))))

end HilbertXI25SolidCutWitness


/--
Source-faithful "proper part" relation for the solid comparison used in
Euclid XI.25.

`Part` is a proper part of `Whole` when there is an ordered nontrivial
parallel cut of a parallelepiped such that:

* `Part` is XI.Def.10-equal to either the left or the right cut piece;
* `Whole` is XI.Def.10-equal to the complete uncut parallelepiped.

The nonempty remainder is not an extra axiom: it follows from the
strict betweenness stored in the cut witness.
-/
def HilbertXI25ProperSolidPart
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (Part Whole : HilbertXI25Parallelepiped Geo) : Prop :=

  Exists
    (fun X : HilbertXI25SolidCutWitness
      (Geo := Geo) =>
      (HilbertXI25SolidEquivalent
          Geo Part
          (X.leftSolid (Geo := Geo))
       \/
       HilbertXI25SolidEquivalent
          Geo Part
          (X.rightSolid (Geo := Geo)))
      /\
      HilbertXI25SolidEquivalent
        Geo Whole
        (X.wholeSolid (Geo := Geo)))


/--
The left piece of every ordered cut is a proper solid part of its whole.
-/
theorem hilbert_XI25_left_properPart_whole
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
      (Geo := Geo)) :
    HilbertXI25ProperSolidPart
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  refine Exists.intro X ?_

  refine And.intro ?_ ?_

  · exact
      Or.inl
        (hilbertXI25SolidEquivalent_refl_space
          (Geo := Geo)
          (X.leftSolid (Geo := Geo)))

  · exact
      hilbertXI25SolidEquivalent_refl_space
        (Geo := Geo)
        (X.wholeSolid (Geo := Geo))


/--
The right piece of every ordered cut is a proper solid part of its whole.
-/
theorem hilbert_XI25_right_properPart_whole
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
      (Geo := Geo)) :
    HilbertXI25ProperSolidPart
      (Geo := Geo)
      (X.rightSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  refine Exists.intro X ?_

  refine And.intro ?_ ?_

  · exact
      Or.inr
        (hilbertXI25SolidEquivalent_refl_space
          (Geo := Geo)
          (X.rightSolid (Geo := Geo)))

  · exact
      hilbertXI25SolidEquivalent_refl_space
        (Geo := Geo)
        (X.wholeSolid (Geo := Geo))


/--
Proper-part witnesses are stable under replacing both compared solids by
XI.Def.10-equal solids.

This is the transport needed later when the subsolid cut from `LU` is not
literally `NU`, but is only equal to `NU` in Euclid's sense.
-/
theorem HilbertXI25ProperSolidPart.transport
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Part' Whole Whole' :
      HilbertXI25Parallelepiped Geo}
    (hPart :
      HilbertXI25SolidEquivalent
        Geo Part' Part)
    (hWhole :
      HilbertXI25SolidEquivalent
        Geo Whole' Whole)
    (h :
      HilbertXI25ProperSolidPart
        (Geo := Geo) Part Whole) :
    HilbertXI25ProperSolidPart
      (Geo := Geo) Part' Whole' := by

  rcases h with
    ⟨X, hPiece, hWholeX⟩

  refine ⟨X, ?_, ?_⟩

  · rcases hPiece with hLeft | hRight

    · exact
        Or.inl
          (hilbertXI25SolidEquivalent_trans_space
            (Geo := Geo)
            hPart
            hLeft)

    · exact
        Or.inr
          (hilbertXI25SolidEquivalent_trans_space
            (Geo := Geo)
            hPart
            hRight)

  · exact
      hilbertXI25SolidEquivalent_trans_space
        (Geo := Geo)
        hWhole
        hWholeX


/--
Every proper-part witness carries an explicitly nonempty cut.
-/
theorem HilbertXI25ProperSolidPart.has_nonempty_cut
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Whole :
      HilbertXI25Parallelepiped Geo}
    (h :
      HilbertXI25ProperSolidPart
        (Geo := Geo) Part Whole) :
    Exists
      (fun X : HilbertXI25SolidCutWitness
        (Geo := Geo) =>
        Ne X.A0 X.A1 /\
        Ne X.A1 X.A2 /\
        Ne X.A0 X.A2) := by

  rcases h with
    ⟨X, _hPiece, _hWhole⟩

  exact
    ⟨X, X.nonempty_A (Geo := Geo)⟩


------------------------------------------------------------------------
-- XI.25: three-way solid comparison witnesses
------------------------------------------------------------------------

/-!
Euclid V.Def.5 compares arbitrary positive multiples in three ways:

    less than,
    equal,
    greater than.

For XI.25 we now have source-faithful notions for the corresponding
solid cases:

* equality is XI.Def.10 equality;
* strict inequality is witnessed by a nontrivial parallel cut, i.e.
  `HilbertXI25ProperSolidPart`.

The definition below is only a witness that one of the three cases is
available.  It does NOT assert totality, exclusivity, or trichotomy for
all parallelepipeds.  Those stronger order properties must not be
silently assumed.
-/

/--
Strict comparison of XI.25 solids: `T` is less than `U` exactly when
`T` is a proper cut part of `U`.
-/
def HilbertXI25SolidLess
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T U : HilbertXI25Parallelepiped Geo) : Prop :=
  HilbertXI25ProperSolidPart
    (Geo := Geo) T U

/--
Strict greater-than comparison, expressed by reversing proper-part.
-/
def HilbertXI25SolidGreater
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T U : HilbertXI25Parallelepiped Geo) : Prop :=
  HilbertXI25ProperSolidPart
    (Geo := Geo) U T

/--
A source-faithful three-way comparison witness for two XI.25 solids.

The alternatives are, in order:

1. `T = U` in the XI.Def.10 sense;
2. `T < U`, witnessed by `T` being a proper cut part of `U`;
3. `T > U`, witnessed by `U` being a proper cut part of `T`.
-/
def HilbertXI25SolidComparison
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T U : HilbertXI25Parallelepiped Geo) : Prop :=
  HilbertXI25SolidEquivalent Geo T U
  \/
  HilbertXI25SolidLess
    (Geo := Geo) T U
  \/
  HilbertXI25SolidGreater
    (Geo := Geo) T U

/--
XI.Def.10 equality gives the equal branch of the comparison witness.
-/
theorem hilbert_XI25_solidComparison_of_equal
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {T U : HilbertXI25Parallelepiped Geo}
    (h :
      HilbertXI25SolidEquivalent Geo T U) :
    HilbertXI25SolidComparison
      (Geo := Geo) T U := by

  exact Or.inl h

/--
A proper-part witness gives the less-than branch.
-/
theorem hilbert_XI25_solidComparison_of_less
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {T U : HilbertXI25Parallelepiped Geo}
    (h :
      HilbertXI25SolidLess
        (Geo := Geo) T U) :
    HilbertXI25SolidComparison
      (Geo := Geo) T U := by

  exact Or.inr (Or.inl h)

/--
A reversed proper-part witness gives the greater-than branch.
-/
theorem hilbert_XI25_solidComparison_of_greater
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {T U : HilbertXI25Parallelepiped Geo}
    (h :
      HilbertXI25SolidGreater
        (Geo := Geo) T U) :
    HilbertXI25SolidComparison
      (Geo := Geo) T U := by

  exact Or.inr (Or.inr h)

/--
Every solid compares equally with itself.
-/
theorem hilbert_XI25_solidComparison_refl
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (T : HilbertXI25Parallelepiped Geo) :
    HilbertXI25SolidComparison
      (Geo := Geo) T T := by

  exact
    hilbert_XI25_solidComparison_of_equal
      (Geo := Geo)
      (hilbertXI25SolidEquivalent_refl_space
        (Geo := Geo) T)

/--
Reversing the two solids reverses less and greater and preserves equality.
-/
theorem HilbertXI25SolidComparison.symm
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {T U : HilbertXI25Parallelepiped Geo}
    (h :
      HilbertXI25SolidComparison
        (Geo := Geo) T U) :
    HilbertXI25SolidComparison
      (Geo := Geo) U T := by

  rcases h with hEq | hStrict

  · exact
      Or.inl
        (hilbertXI25SolidEquivalent_symm_space
          (Geo := Geo) hEq)

  · rcases hStrict with hLess | hGreater

    · exact Or.inr (Or.inr hLess)

    · exact Or.inr (Or.inl hGreater)

/--
Solid comparison is stable under replacing both solids by XI.Def.10-equal
representatives.

This is the comparison-level version of
`HilbertXI25ProperSolidPart.transport`.
-/
theorem HilbertXI25SolidComparison.transport
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {T T' U U' :
      HilbertXI25Parallelepiped Geo}
    (hT :
      HilbertXI25SolidEquivalent
        Geo T' T)
    (hU :
      HilbertXI25SolidEquivalent
        Geo U' U)
    (h :
      HilbertXI25SolidComparison
        (Geo := Geo) T U) :
    HilbertXI25SolidComparison
      (Geo := Geo) T' U' := by

  rcases h with hEq | hStrict

  · have hTU' :
        HilbertXI25SolidEquivalent
          Geo T U' :=
      hilbertXI25SolidEquivalent_trans_space
        (Geo := Geo)
        hEq
        (hilbertXI25SolidEquivalent_symm_space
          (Geo := Geo) hU)

    have hT'U' :
        HilbertXI25SolidEquivalent
          Geo T' U' :=
      hilbertXI25SolidEquivalent_trans_space
        (Geo := Geo)
        hT
        hTU'

    exact Or.inl hT'U'

  · rcases hStrict with hLess | hGreater

    · exact
        Or.inr
          (Or.inl
            (HilbertXI25ProperSolidPart.transport
              (Geo := Geo)
              hT hU hLess))

    · exact
        Or.inr
          (Or.inr
            (HilbertXI25ProperSolidPart.transport
              (Geo := Geo)
              hU hT hGreater))

/--
The left piece of a nontrivial cut is strictly less than the whole.
-/
theorem hilbert_XI25_left_less_whole
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
      (Geo := Geo)) :
    HilbertXI25SolidLess
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  exact
    hilbert_XI25_left_properPart_whole
      (Geo := Geo) X

/--
The right piece of a nontrivial cut is strictly less than the whole.
-/
theorem hilbert_XI25_right_less_whole
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
      (Geo := Geo)) :
    HilbertXI25SolidLess
      (Geo := Geo)
      (X.rightSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  exact
    hilbert_XI25_right_properPart_whole
      (Geo := Geo) X

/--
The whole is greater than its left cut piece.
-/
theorem hilbert_XI25_whole_greater_left
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
      (Geo := Geo)) :
    HilbertXI25SolidGreater
      (Geo := Geo)
      (X.wholeSolid (Geo := Geo))
      (X.leftSolid (Geo := Geo)) := by

  exact
    hilbert_XI25_left_properPart_whole
      (Geo := Geo) X

/--
The whole is greater than its right cut piece.
-/
theorem hilbert_XI25_whole_greater_right
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
      (Geo := Geo)) :
    HilbertXI25SolidGreater
      (Geo := Geo)
      (X.wholeSolid (Geo := Geo))
      (X.rightSolid (Geo := Geo)) := by

  exact
    hilbert_XI25_right_properPart_whole
      (Geo := Geo) X

/--
Comparison witnesses for the left piece and the whole.
-/
theorem hilbert_XI25_compare_left_whole
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
      (Geo := Geo)) :
    HilbertXI25SolidComparison
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  exact
    hilbert_XI25_solidComparison_of_less
      (Geo := Geo)
      (hilbert_XI25_left_less_whole
        (Geo := Geo) X)

/--
Comparison witnesses for the right piece and the whole.
-/
theorem hilbert_XI25_compare_right_whole
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
      (Geo := Geo)) :
    HilbertXI25SolidComparison
      (Geo := Geo)
      (X.rightSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  exact
    hilbert_XI25_solidComparison_of_less
      (Geo := Geo)
      (hilbert_XI25_right_less_whole
        (Geo := Geo) X)



------------------------------------------------------------------------
-- XI.25: aligned base/solid cuts
------------------------------------------------------------------------

/-!
For Euclid XI.25 the base figures cut together with the solid are the
parallelogram faces lying in one fixed side plane. In the canonical
face convention used here we take `rho0` as that base plane.

Thus every nontrivial solid cut carries, at the same time,

* a nontrivial cut of the corresponding base parallelogram, and
* a nontrivial cut of the parallelepiped itself.

This is the first source-faithful bridge between base comparison and
solid comparison. No order is defined through an external width
parameter.
-/

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
The base parallelogram of the left cut piece.
-/
def leftBase
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertParallelogramFace Geo :=
  (X.leftSolid (Geo := Geo)).rho0

/--
The base parallelogram of the right cut piece.
-/
def rightBase
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertParallelogramFace Geo :=
  (X.rightSolid (Geo := Geo)).rho0

/--
The uncut base parallelogram of the whole solid.
-/
def wholeBase
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertParallelogramFace Geo :=
  (X.wholeSolid (Geo := Geo)).rho0

end HilbertXI25SolidCutWitness


/--
Source-faithful proper-part relation for the base parallelograms used
in XI.25.

A base is a proper part of another base when both arise from the same
nontrivial parallel cut of a parallelepiped, up to the established
synthetic equality of parallelogram faces.
-/
def HilbertXI25ProperBasePart
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (Part Whole : HilbertParallelogramFace Geo) : Prop :=

  Exists
    (fun X : HilbertXI25SolidCutWitness
      (Geo := Geo) =>
      (HilbertXI25BaseEquivalent
          Geo Part
          (X.leftBase (Geo := Geo))
       \/
       HilbertXI25BaseEquivalent
          Geo Part
          (X.rightBase (Geo := Geo)))
      /\
      HilbertXI25BaseEquivalent
        Geo Whole
        (X.wholeBase (Geo := Geo)))


/--
The left base piece of every ordered solid cut is a proper part of the
whole base.
-/
theorem hilbert_XI25_leftBase_properPart_wholeBase
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
      (Geo := Geo)) :
    HilbertXI25ProperBasePart
      (Geo := Geo)
      (X.leftBase (Geo := Geo))
      (X.wholeBase (Geo := Geo)) := by

  refine ⟨X, ?_, ?_⟩

  · exact
      Or.inl
        (hilbertXI25BaseEquivalent_refl_space
          (Geo := Geo)
          (X.leftBase (Geo := Geo)))

  · exact
      hilbertXI25BaseEquivalent_refl_space
        (Geo := Geo)
        (X.wholeBase (Geo := Geo))


/--
The right base piece of every ordered solid cut is a proper part of the
whole base.
-/
theorem hilbert_XI25_rightBase_properPart_wholeBase
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
      (Geo := Geo)) :
    HilbertXI25ProperBasePart
      (Geo := Geo)
      (X.rightBase (Geo := Geo))
      (X.wholeBase (Geo := Geo)) := by

  refine ⟨X, ?_, ?_⟩

  · exact
      Or.inr
        (hilbertXI25BaseEquivalent_refl_space
          (Geo := Geo)
          (X.rightBase (Geo := Geo)))

  · exact
      hilbertXI25BaseEquivalent_refl_space
        (Geo := Geo)
        (X.wholeBase (Geo := Geo))


/--
Proper-base-part witnesses are stable under replacement by equal base
parallelograms.
-/
theorem HilbertXI25ProperBasePart.transport
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Part' Whole Whole' :
      HilbertParallelogramFace Geo}
    (hPart :
      HilbertXI25BaseEquivalent
        Geo Part' Part)
    (hWhole :
      HilbertXI25BaseEquivalent
        Geo Whole' Whole)
    (h :
      HilbertXI25ProperBasePart
        (Geo := Geo) Part Whole) :
    HilbertXI25ProperBasePart
      (Geo := Geo) Part' Whole' := by

  rcases h with
    ⟨X, hPiece, hWholeX⟩

  refine ⟨X, ?_, ?_⟩

  · rcases hPiece with hLeft | hRight

    · exact
        Or.inl
          (hilbertXI25BaseEquivalent_trans_space
            (Geo := Geo)
            hPart
            hLeft)

    · exact
        Or.inr
          (hilbertXI25BaseEquivalent_trans_space
            (Geo := Geo)
            hPart
            hRight)

  · exact
      hilbertXI25BaseEquivalent_trans_space
        (Geo := Geo)
        hWhole
        hWholeX


/--
Strict comparison of XI.25 base parallelograms.
-/
def HilbertXI25BaseLess
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (P Q : HilbertParallelogramFace Geo) : Prop :=
  HilbertXI25ProperBasePart
    (Geo := Geo) P Q

/--
Greater-than comparison of XI.25 base parallelograms.
-/
def HilbertXI25BaseGreater
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (P Q : HilbertParallelogramFace Geo) : Prop :=
  HilbertXI25ProperBasePart
    (Geo := Geo) Q P

/--
Three-way comparison witness for XI.25 bases.

As for solids, this records one available comparison case; it does not
assert totality or exclusivity for arbitrary parallelograms.
-/
def HilbertXI25BaseComparison
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (P Q : HilbertParallelogramFace Geo) : Prop :=
  HilbertXI25BaseEquivalent Geo P Q
  \/
  HilbertXI25BaseLess
    (Geo := Geo) P Q
  \/
  HilbertXI25BaseGreater
    (Geo := Geo) P Q


/--
The same nontrivial cut witnesses strict comparison of the base and of
the corresponding solid.
-/
theorem hilbert_XI25_left_cut_base_solid_less
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
      (Geo := Geo)) :
    HilbertXI25BaseLess
      (Geo := Geo)
      (X.leftBase (Geo := Geo))
      (X.wholeBase (Geo := Geo))
    /\
    HilbertXI25SolidLess
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  exact
    And.intro
      (hilbert_XI25_leftBase_properPart_wholeBase
        (Geo := Geo) X)
      (hilbert_XI25_left_less_whole
        (Geo := Geo) X)


/--
The same nontrivial cut witnesses strict comparison of the right base
piece and the corresponding right solid piece with their wholes.
-/
theorem hilbert_XI25_right_cut_base_solid_less
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
      (Geo := Geo)) :
    HilbertXI25BaseLess
      (Geo := Geo)
      (X.rightBase (Geo := Geo))
      (X.wholeBase (Geo := Geo))
    /\
    HilbertXI25SolidLess
      (Geo := Geo)
      (X.rightSolid (Geo := Geo))
      (X.wholeSolid (Geo := Geo)) := by

  exact
    And.intro
      (hilbert_XI25_rightBase_properPart_wholeBase
        (Geo := Geo) X)
      (hilbert_XI25_right_less_whole
        (Geo := Geo) X)


/--
Transport the left-cut strict comparison simultaneously to arbitrary
equal representatives of the base piece, base whole, solid piece, and
solid whole.

This is the direct formal shape needed for the omitted XI.25 step:
once a smaller comparison base and solid are identified with the
corresponding cut pieces, strictness transfers to both levels.
-/
theorem hilbert_XI25_transfer_less_of_left_cut
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
    (Psmall Pwhole : HilbertParallelogramFace Geo)
    (Ssmall Swhole : HilbertXI25Parallelepiped Geo)
    (hPsmall :
      HilbertXI25BaseEquivalent
        Geo Psmall
        (X.leftBase (Geo := Geo)))
    (hPwhole :
      HilbertXI25BaseEquivalent
        Geo Pwhole
        (X.wholeBase (Geo := Geo)))
    (hSsmall :
      HilbertXI25SolidEquivalent
        Geo Ssmall
        (X.leftSolid (Geo := Geo)))
    (hSwhole :
      HilbertXI25SolidEquivalent
        Geo Swhole
        (X.wholeSolid (Geo := Geo))) :
    HilbertXI25BaseLess
      (Geo := Geo) Psmall Pwhole
    /\
    HilbertXI25SolidLess
      (Geo := Geo) Ssmall Swhole := by

  have hBase :
      HilbertXI25BaseLess
        (Geo := Geo) Psmall Pwhole := by

    exact
      HilbertXI25ProperBasePart.transport
        (Geo := Geo)
        hPsmall
        hPwhole
        (hilbert_XI25_leftBase_properPart_wholeBase
          (Geo := Geo) X)

  have hSolid :
      HilbertXI25SolidLess
        (Geo := Geo) Ssmall Swhole := by

    exact
      HilbertXI25ProperSolidPart.transport
        (Geo := Geo)
        hSsmall
        hSwhole
        (hilbert_XI25_left_properPart_whole
          (Geo := Geo) X)

  exact And.intro hBase hSolid


/--
Right-cut version of the synchronized strict-comparison transport.
-/
theorem hilbert_XI25_transfer_less_of_right_cut
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
    (Psmall Pwhole : HilbertParallelogramFace Geo)
    (Ssmall Swhole : HilbertXI25Parallelepiped Geo)
    (hPsmall :
      HilbertXI25BaseEquivalent
        Geo Psmall
        (X.rightBase (Geo := Geo)))
    (hPwhole :
      HilbertXI25BaseEquivalent
        Geo Pwhole
        (X.wholeBase (Geo := Geo)))
    (hSsmall :
      HilbertXI25SolidEquivalent
        Geo Ssmall
        (X.rightSolid (Geo := Geo)))
    (hSwhole :
      HilbertXI25SolidEquivalent
        Geo Swhole
        (X.wholeSolid (Geo := Geo))) :
    HilbertXI25BaseLess
      (Geo := Geo) Psmall Pwhole
    /\
    HilbertXI25SolidLess
      (Geo := Geo) Ssmall Swhole := by

  have hBase :
      HilbertXI25BaseLess
        (Geo := Geo) Psmall Pwhole := by

    exact
      HilbertXI25ProperBasePart.transport
        (Geo := Geo)
        hPsmall
        hPwhole
        (hilbert_XI25_rightBase_properPart_wholeBase
          (Geo := Geo) X)

  have hSolid :
      HilbertXI25SolidLess
        (Geo := Geo) Ssmall Swhole := by

    exact
      HilbertXI25ProperSolidPart.transport
        (Geo := Geo)
        hSsmall
        hSwhole
        (hilbert_XI25_right_properPart_whole
          (Geo := Geo) X)

  exact And.intro hBase hSolid



------------------------------------------------------------------------
-- XI.25: comparison transfer for the two opposite multiple slabs
------------------------------------------------------------------------

/-!
The two large equimultiple solids occurring in Euclid XI.25 are again
two adjacent slabs separated by the original cutting plane.

Thus the comparison problem

    LF ? NF
    LU ? NU

is represented by one `HilbertXI25SolidCutWitness`:

* `leftBase` and `rightBase` are the two equimultiple bases;
* `leftSolid` and `rightSolid` are the two equimultiple solids.

The equality case is proved directly from base equality. Strict cases
are represented by a second, aligned cut witness inside the larger
slab, exactly as in Joyce's completion of Euclid's omitted argument.
-/

/--
For two adjacent XI.25 slabs, equality of the two corresponding base
parallelograms implies equality of the two solids.

The base equality contains equality of the longitudinal B-widths.
Using the parallelogram side equalities from XI.24, this gives equality
of the A-widths, after which the already established adjacent-solid
theorem applies.
-/
theorem hilbert_XI25_adjacent_solids_equal_of_base_equal
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
    hilbert_XI25_twoSlab_XI24
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
    hilbert_XI25_adjacent_elementary_solids_equal
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


/--
A synchronized strict comparison witness for a base and its
corresponding solid.

The smaller base and smaller solid are represented by the same piece
of one nontrivial cut; the larger base and larger solid are represented
by the whole of that cut. Equal representatives are allowed on all
four objects.
-/
def HilbertXI25AlignedProperPartWitness
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (Psmall : HilbertParallelogramFace Geo)
    (Ssmall : HilbertXI25Parallelepiped Geo)
    (Pwhole : HilbertParallelogramFace Geo)
    (Swhole : HilbertXI25Parallelepiped Geo) : Prop :=

  Exists
    (fun cut : HilbertXI25SolidCutWitness
      (Geo := Geo) =>
      ((HilbertXI25BaseEquivalent
          Geo Psmall
          (cut.leftBase (Geo := Geo))
        /\
        HilbertXI25SolidEquivalent
          Geo Ssmall
          (cut.leftSolid (Geo := Geo)))
       \/
       (HilbertXI25BaseEquivalent
          Geo Psmall
          (cut.rightBase (Geo := Geo))
        /\
        HilbertXI25SolidEquivalent
          Geo Ssmall
          (cut.rightSolid (Geo := Geo))))
      /\
      HilbertXI25BaseEquivalent
        Geo Pwhole
        (cut.wholeBase (Geo := Geo))
      /\
      HilbertXI25SolidEquivalent
        Geo Swhole
        (cut.wholeSolid (Geo := Geo)))


namespace HilbertXI25AlignedProperPartWitness

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
An aligned proper-part witness gives strict comparison of the bases.
-/
theorem baseLess
    {Psmall Pwhole :
      HilbertParallelogramFace Geo}
    {Ssmall Swhole :
      HilbertXI25Parallelepiped Geo}
    (W :
      HilbertXI25AlignedProperPartWitness
        (Geo := Geo)
        Psmall Ssmall
        Pwhole Swhole) :
    HilbertXI25BaseLess
      (Geo := Geo) Psmall Pwhole := by

  rcases W with
    ⟨cut, hPiece, hWholeBase, _hWholeSolid⟩

  rcases hPiece with hLeft | hRight

  · exact
      HilbertXI25ProperBasePart.transport
        (Geo := Geo)
        hLeft.1
        hWholeBase
        (hilbert_XI25_leftBase_properPart_wholeBase
          (Geo := Geo) cut)

  · exact
      HilbertXI25ProperBasePart.transport
        (Geo := Geo)
        hRight.1
        hWholeBase
        (hilbert_XI25_rightBase_properPart_wholeBase
          (Geo := Geo) cut)

/--
The same aligned witness gives strict comparison of the solids.
-/
theorem solidLess
    {Psmall Pwhole :
      HilbertParallelogramFace Geo}
    {Ssmall Swhole :
      HilbertXI25Parallelepiped Geo}
    (W :
      HilbertXI25AlignedProperPartWitness
        (Geo := Geo)
        Psmall Ssmall
        Pwhole Swhole) :
    HilbertXI25SolidLess
      (Geo := Geo) Ssmall Swhole := by

  rcases W with
    ⟨cut, hPiece, _hWholeBase, hWholeSolid⟩

  rcases hPiece with hLeft | hRight

  · exact
      HilbertXI25ProperSolidPart.transport
        (Geo := Geo)
        hLeft.2
        hWholeSolid
        (hilbert_XI25_left_properPart_whole
          (Geo := Geo) cut)

  · exact
      HilbertXI25ProperSolidPart.transport
        (Geo := Geo)
        hRight.2
        hWholeSolid
        (hilbert_XI25_right_properPart_whole
          (Geo := Geo) cut)

/--
The strict comparison sign is synchronized between base and solid.
-/
theorem baseSolidLess
    {Psmall Pwhole :
      HilbertParallelogramFace Geo}
    {Ssmall Swhole :
      HilbertXI25Parallelepiped Geo}
    (W :
      HilbertXI25AlignedProperPartWitness
        (Geo := Geo)
        Psmall Ssmall
        Pwhole Swhole) :
    HilbertXI25BaseLess
      (Geo := Geo) Psmall Pwhole
    /\
    HilbertXI25SolidLess
      (Geo := Geo) Ssmall Swhole := by

  exact
    And.intro
      (baseLess (Geo := Geo) W)
      (solidLess (Geo := Geo) W)

end HilbertXI25AlignedProperPartWitness


/--
A source-level certificate for the three possible comparisons of the
two equimultiple bases and solids in XI.25.

The three disjuncts are:

* equal bases;
* left base/solid is a proper aligned part of the right;
* right base/solid is a proper aligned part of the left.

The strict cases contain the extra cut required by Joyce's completion
of Euclid's omitted argument.
-/
def HilbertXI25TwoSlabComparisonCertificate
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
      (Geo := Geo)) : Prop :=

  HilbertXI25BaseEquivalent
    Geo
    (X.leftBase (Geo := Geo))
    (X.rightBase (Geo := Geo))
  \/
  HilbertXI25AlignedProperPartWitness
    (Geo := Geo)
    (X.leftBase (Geo := Geo))
    (X.leftSolid (Geo := Geo))
    (X.rightBase (Geo := Geo))
    (X.rightSolid (Geo := Geo))
  \/
  HilbertXI25AlignedProperPartWitness
    (Geo := Geo)
    (X.rightBase (Geo := Geo))
    (X.rightSolid (Geo := Geo))
    (X.leftBase (Geo := Geo))
    (X.leftSolid (Geo := Geo))


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
A comparison certificate yields the corresponding base comparison.
-/
theorem baseComparison
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (h :
      HilbertXI25TwoSlabComparisonCertificate
        (Geo := Geo) X) :
    HilbertXI25BaseComparison
      (Geo := Geo)
      (X.leftBase (Geo := Geo))
      (X.rightBase (Geo := Geo)) := by

  rcases h with hEqual | hStrict

  · exact Or.inl hEqual

  · rcases hStrict with hLeftLess | hRightLess

    · exact
        Or.inr
          (Or.inl
            (HilbertXI25AlignedProperPartWitness.baseLess
              (Geo := Geo) hLeftLess))

    · exact
        Or.inr
          (Or.inr
            (HilbertXI25AlignedProperPartWitness.baseLess
              (Geo := Geo) hRightLess))

/--
A comparison certificate yields the solid comparison with exactly the
same sign as the base comparison.
-/
theorem solidComparison
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (h :
      HilbertXI25TwoSlabComparisonCertificate
        (Geo := Geo) X) :
    HilbertXI25SolidComparison
      (Geo := Geo)
      (X.leftSolid (Geo := Geo))
      (X.rightSolid (Geo := Geo)) := by

  rcases h with hEqual | hStrict

  · exact
      Or.inl
        (hilbert_XI25_adjacent_solids_equal_of_base_equal
          (Geo := Geo)
          X hEqual)

  · rcases hStrict with hLeftLess | hRightLess

    · exact
        Or.inr
          (Or.inl
            (HilbertXI25AlignedProperPartWitness.solidLess
              (Geo := Geo) hLeftLess))

    · exact
        Or.inr
          (Or.inr
            (HilbertXI25AlignedProperPartWitness.solidLess
              (Geo := Geo) hRightLess))

/--
Bundled XI.25 comparison transfer: one source-level certificate
produces base and solid comparisons with the same branch.
-/
theorem base_and_solid_comparison
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
      (solidComparison (Geo := Geo) X h)

end HilbertXI25TwoSlabComparisonCertificate



------------------------------------------------------------------------
-- XI.25: quotient strict order and Eudoxus comparison interface
------------------------------------------------------------------------

/-!
Euclid V.Def.5 compares magnitudes, not chosen concrete representatives.
For XI.25 the natural magnitude objects are therefore the quotient
classes already introduced:

* `HilbertXI25BaseClass`;
* `HilbertXI25SolidClass`.

The strict relations below are quotient lifts of the source-faithful
proper-part relations. Their well-definedness uses exactly the
transport theorems proved above.

This is the correct interface for the final Eudoxus step: equality is
ordinary equality of quotient classes, while strict comparison still
means geometric proper-part comparison.
-/

/--
Strict order on XI.25 base magnitude classes.
-/
def HilbertXI25BaseClassLess
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a b : HilbertXI25BaseClass Geo) : Prop :=

  Quotient.liftOn₂
    a
    b
    (fun P Q =>
      HilbertXI25BaseLess
        (Geo := Geo) P Q)
    (by
      intro P Q P' Q' hP hQ
      apply propext
      constructor

      · intro hPQ

        exact
          HilbertXI25ProperBasePart.transport
            (Geo := Geo)
            (hilbertXI25BaseEquivalent_symm_space
              (Geo := Geo) hP)
            (hilbertXI25BaseEquivalent_symm_space
              (Geo := Geo) hQ)
            hPQ

      · intro hP'Q'

        exact
          HilbertXI25ProperBasePart.transport
            (Geo := Geo)
            hP
            hQ
            hP'Q')


/--
Strict order on XI.25 solid magnitude classes.
-/
def HilbertXI25SolidClassLess
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a b : HilbertXI25SolidClass Geo) : Prop :=

  Quotient.liftOn₂
    a
    b
    (fun S T =>
      HilbertXI25SolidLess
        (Geo := Geo) S T)
    (by
      intro S T S' T' hS hT
      apply propext
      constructor

      · intro hST

        exact
          HilbertXI25ProperSolidPart.transport
            (Geo := Geo)
            (hilbertXI25SolidEquivalent_symm_space
              (Geo := Geo) hS)
            (hilbertXI25SolidEquivalent_symm_space
              (Geo := Geo) hT)
            hST

      · intro hS'T'

        exact
          HilbertXI25ProperSolidPart.transport
            (Geo := Geo)
            hS
            hT
            hS'T')


/--
On concrete representatives, quotient base order is exactly the
geometric proper-base-part relation.
-/
theorem hilbertXI25BaseClassOf_less_iff
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (P Q : HilbertParallelogramFace Geo) :
    HilbertXI25BaseClassLess
        (Geo := Geo)
        (hilbertXI25BaseClassOf
          (Geo := Geo) P)
        (hilbertXI25BaseClassOf
          (Geo := Geo) Q)
      <->
    HilbertXI25BaseLess
      (Geo := Geo) P Q := by

  rfl


/--
On concrete representatives, quotient solid order is exactly the
geometric proper-solid-part relation.
-/
theorem hilbertXI25SolidClassOf_less_iff
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (S T : HilbertXI25Parallelepiped Geo) :
    HilbertXI25SolidClassLess
        (Geo := Geo)
        (hilbertXI25SolidClassOf
          (Geo := Geo) S)
        (hilbertXI25SolidClassOf
          (Geo := Geo) T)
      <->
    HilbertXI25SolidLess
      (Geo := Geo) S T := by

  rfl


/--
Equality of concrete base classes is exactly equality of the concrete
bases in the established XI.25 face sense.
-/
theorem hilbertXI25BaseClassOf_eq_iff
    [H : HilbertIncidence Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (P Q : HilbertParallelogramFace Geo) :
    hilbertXI25BaseClassOf
        (Geo := Geo) P
      =
    hilbertXI25BaseClassOf
        (Geo := Geo) Q
      <->
    HilbertXI25BaseEquivalent
      Geo P Q := by

  constructor

  · intro h
    exact Quotient.exact h

  · intro h
    exact Quotient.sound h


/--
Equality of concrete solid classes is exactly XI.Def.10 equality.
-/
theorem hilbertXI25SolidClassOf_eq_iff
    [H : HilbertIncidence Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (S T : HilbertXI25Parallelepiped Geo) :
    hilbertXI25SolidClassOf
        (Geo := Geo) S
      =
    hilbertXI25SolidClassOf
        (Geo := Geo) T
      <->
    HilbertXI25SolidEquivalent
      Geo S T := by

  constructor

  · intro h
    exact Quotient.exact h

  · intro h
    exact Quotient.sound h


/--
Eudoxus magnitude structure on XI.25 base classes once a positive
natural-multiple operation has been supplied.

The order itself is not supplied by the caller: it is the geometric
proper-part order constructed above.
-/
def hilbertXI25BaseEudoxusMagnitude
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (multiple :
      Nat ->
      HilbertXI25BaseClass Geo ->
      HilbertXI25BaseClass Geo) :
    EudoxusMagnitude
      (HilbertXI25BaseClass Geo) where

  less :=
    HilbertXI25BaseClassLess
      (Geo := Geo)

  multiple := multiple


/--
Eudoxus magnitude structure on XI.25 solid classes once a positive
natural-multiple operation has been supplied.
-/
def hilbertXI25SolidEudoxusMagnitude
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (multiple :
      Nat ->
      HilbertXI25SolidClass Geo ->
      HilbertXI25SolidClass Geo) :
    EudoxusMagnitude
      (HilbertXI25SolidClass Geo) where

  less :=
    HilbertXI25SolidClassLess
      (Geo := Geo)

  multiple := multiple


/--
The three comparison clauses required by one pair of multiple indices
in Euclid V.Def.5.

This predicate is deliberately separated from the construction of the
multiples. The remaining geometric work of XI.25 is precisely to prove
this agreement for every pair `m,n` from Euclid's repeated-slab
construction.
-/
def HilbertXI25ClassComparisonAgreement
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a b : HilbertXI25BaseClass Geo)
    (s t : HilbertXI25SolidClass Geo) : Prop :=

  (HilbertXI25BaseClassLess
      (Geo := Geo) a b
    <->
   HilbertXI25SolidClassLess
      (Geo := Geo) s t)
  /\
  (a = b <-> s = t)
  /\
  (HilbertXI25BaseClassLess
      (Geo := Geo) b a
    <->
   HilbertXI25SolidClassLess
      (Geo := Geo) t s)


/--
If the three XI.25 comparison clauses agree for every pair of positive
multiple indices, Euclid V.Def.5 follows immediately.

This theorem performs only the final logical packaging. It assumes no
numerical area or volume and no width-defined order.
-/
theorem hilbert_XI25_eudoxus_of_comparison_agreement
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [_HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [_HSE : HilbertSpaceEuclidean Geo]
    (baseMultiple :
      Nat ->
      HilbertXI25BaseClass Geo ->
      HilbertXI25BaseClass Geo)
    (solidMultiple :
      Nat ->
      HilbertXI25SolidClass Geo ->
      HilbertXI25SolidClass Geo)
    (a b : HilbertXI25BaseClass Geo)
    (s t : HilbertXI25SolidClass Geo)
    (hCompare :
      forall m n : Nat,
        HilbertXI25ClassComparisonAgreement
          (Geo := Geo)
          (baseMultiple m a)
          (baseMultiple n b)
          (solidMultiple m s)
          (solidMultiple n t)) :
    EudoxusProportionBetween
      (hilbertXI25BaseEudoxusMagnitude
        (Geo := Geo) baseMultiple)
      (hilbertXI25SolidEudoxusMagnitude
        (Geo := Geo) solidMultiple)
      a b s t := by

  intro m n

  exact hCompare m n



------------------------------------------------------------------------
-- XI.25: Common Notion 5 for cut bases and solids
------------------------------------------------------------------------

/-!
Euclid's strict comparison step uses Common Notion 5:

    the whole is greater than the part.

For XI.25 this can be proved synthetically from the existing cut data.
No global congruence structure is installed on ambient 3-space.

The contradiction is taken inside the fixed side plane `rho0`.
There the induced geometry `PlaneGeo Geo rho0` has the ordinary planar
Hilbert congruence structure. If a proper cut base were equal to its
whole base, the canonical diagonal-triangle witness would make a proper
subsegment congruent to the whole longitudinal side, contradicting the
standard Hilbert segment theorem.
-/

/--
The left base of a nontrivial XI.25 cut is not equal to the whole base.
-/
theorem hilbert_XI25_leftBase_not_equivalent_wholeBase
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
      (Geo := Geo)) :
    Not
      (HilbertXI25BaseEquivalent
        Geo
        (X.leftBase (Geo := Geo))
        (X.wholeBase (Geo := Geo))) := by

  intro hEq

  let B0p : PlanePoint Geo X.rho0 :=
    ⟨X.B0, X.ordered.slab.B0_on.2.1⟩

  let B1p : PlanePoint Geo X.rho0 :=
    ⟨X.B1, X.ordered.slab.B1_on.2.1⟩

  let B2p : PlanePoint Geo X.rho0 :=
    ⟨X.B2, X.ordered.slab.B2_on.2.1⟩

  have hBetweenPlane :
      (PlaneGeo Geo X.rho0).Between
        B0p B1p B2p := by

    apply
      (planeGeo_between
        (Geo := Geo)
        X.rho0
        B0p B1p B2p).mpr

    simpa [B0p, B1p, B2p] using
      X.ordered.between_B

  have hLess :
      HilbertSegmentLess
        (PlaneGeo Geo X.rho0)
        B0p B1p B0p B2p :=
    hilbert_segmentLess_of_between
      (PlaneGeo Geo X.rho0)
      B0p B1p B2p
      hBetweenPlane

  have hEqAmbient :
      Geo.Congruent
        X.B0 X.B1
        X.B0 X.B2 := by

    change
      TriangleCongruenceResult
        Geo
        X.B0 X.A0 X.B1
        X.B0 X.A0 X.B2
      at hEq

    exact hEq.sideAC

  have hEqPlane :
      (PlaneGeo Geo X.rho0).Congruent
        B0p B1p B0p B2p := by

    apply
      (planeGeo_congruent
        (Geo := Geo)
        X.rho0
        B0p B1p B0p B2p).mpr

    simpa [B0p, B1p, B2p] using hEqAmbient

  exact
    (hilbert_segmentLess_not_congruent
      (PlaneGeo Geo X.rho0)
      B0p B1p B0p B2p
      hLess)
      hEqPlane


/--
The right base of a nontrivial XI.25 cut is not equal to the whole base.
-/
theorem hilbert_XI25_rightBase_not_equivalent_wholeBase
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
      (Geo := Geo)) :
    Not
      (HilbertXI25BaseEquivalent
        Geo
        (X.rightBase (Geo := Geo))
        (X.wholeBase (Geo := Geo))) := by

  intro hEq

  let B0p : PlanePoint Geo X.rho0 :=
    ⟨X.B0, X.ordered.slab.B0_on.2.1⟩

  let B1p : PlanePoint Geo X.rho0 :=
    ⟨X.B1, X.ordered.slab.B1_on.2.1⟩

  let B2p : PlanePoint Geo X.rho0 :=
    ⟨X.B2, X.ordered.slab.B2_on.2.1⟩

  have hB2B1B0 :
      Geo.Between X.B2 X.B1 X.B0 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X.B0 X.B1 X.B2
      X.ordered.between_B).2.2.2.2

  have hBetweenPlane :
      (PlaneGeo Geo X.rho0).Between
        B2p B1p B0p := by

    apply
      (planeGeo_between
        (Geo := Geo)
        X.rho0
        B2p B1p B0p).mpr

    simpa [B0p, B1p, B2p] using hB2B1B0

  have hLess :
      HilbertSegmentLess
        (PlaneGeo Geo X.rho0)
        B2p B1p B2p B0p :=
    hilbert_segmentLess_of_between
      (PlaneGeo Geo X.rho0)
      B2p B1p B0p
      hBetweenPlane

  have hEqAmbient :
      Geo.Congruent
        X.B1 X.B2
        X.B0 X.B2 := by

    change
      TriangleCongruenceResult
        Geo
        X.B1 X.A1 X.B2
        X.B0 X.A0 X.B2
      at hEq

    exact hEq.sideAC

  have hEqPlane0 :
      (PlaneGeo Geo X.rho0).Congruent
        B1p B2p B0p B2p := by

    apply
      (planeGeo_congruent
        (Geo := Geo)
        X.rho0
        B1p B2p B0p B2p).mpr

    simpa [B0p, B1p, B2p] using hEqAmbient

  have hEqPlane1 :
      (PlaneGeo Geo X.rho0).Congruent
        B2p B1p B0p B2p :=
    CongruentReverseFirst
      (PlaneGeo Geo X.rho0)
      B1p B2p B0p B2p
      hEqPlane0

  have hEqPlane :
      (PlaneGeo Geo X.rho0).Congruent
        B2p B1p B2p B0p :=
    (Geometry.Geo.congruent_reverse_second
      (PlaneGeo Geo X.rho0)
      B2p B1p B0p B2p).mp
      hEqPlane1

  exact
    (hilbert_segmentLess_not_congruent
      (PlaneGeo Geo X.rho0)
      B2p B1p B2p B0p
      hLess)
      hEqPlane


/--
Common Notion 5 for XI.25 bases: a proper cut part cannot be equal to
the whole base.
-/
theorem HilbertXI25ProperBasePart.not_equivalent
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Whole : HilbertParallelogramFace Geo}
    (hPart :
      HilbertXI25ProperBasePart
        (Geo := Geo) Part Whole) :
    Not
      (HilbertXI25BaseEquivalent
        Geo Part Whole) := by

  intro hEq

  rcases hPart with
    ⟨X, hPiece, hWhole⟩

  rcases hPiece with hLeft | hRight

  · have hLeftPart :
        HilbertXI25BaseEquivalent
          Geo
          (X.leftBase (Geo := Geo))
          Part :=
      hilbertXI25BaseEquivalent_symm_space
        (Geo := Geo) hLeft

    have hLeftWhole0 :
        HilbertXI25BaseEquivalent
          Geo
          (X.leftBase (Geo := Geo))
          Whole :=
      hilbertXI25BaseEquivalent_trans_space
        (Geo := Geo)
        hLeftPart
        hEq

    have hLeftWhole :
        HilbertXI25BaseEquivalent
          Geo
          (X.leftBase (Geo := Geo))
          (X.wholeBase (Geo := Geo)) :=
      hilbertXI25BaseEquivalent_trans_space
        (Geo := Geo)
        hLeftWhole0
        hWhole

    exact
      (hilbert_XI25_leftBase_not_equivalent_wholeBase
        (Geo := Geo) X)
        hLeftWhole

  · have hRightPart :
        HilbertXI25BaseEquivalent
          Geo
          (X.rightBase (Geo := Geo))
          Part :=
      hilbertXI25BaseEquivalent_symm_space
        (Geo := Geo) hRight

    have hRightWhole0 :
        HilbertXI25BaseEquivalent
          Geo
          (X.rightBase (Geo := Geo))
          Whole :=
      hilbertXI25BaseEquivalent_trans_space
        (Geo := Geo)
        hRightPart
        hEq

    have hRightWhole :
        HilbertXI25BaseEquivalent
          Geo
          (X.rightBase (Geo := Geo))
          (X.wholeBase (Geo := Geo)) :=
      hilbertXI25BaseEquivalent_trans_space
        (Geo := Geo)
        hRightWhole0
        hWhole

    exact
      (hilbert_XI25_rightBase_not_equivalent_wholeBase
        (Geo := Geo) X)
        hRightWhole


/--
A proper solid part induces a proper-part relation on the corresponding
`rho0` base faces.
-/
theorem HilbertXI25ProperSolidPart.rho0_properBasePart
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Whole : HilbertXI25Parallelepiped Geo}
    (hPart :
      HilbertXI25ProperSolidPart
        (Geo := Geo) Part Whole) :
    HilbertXI25ProperBasePart
      (Geo := Geo)
      Part.rho0
      Whole.rho0 := by

  rcases hPart with
    ⟨X, hPiece, hWhole⟩

  refine ⟨X, ?_, ?_⟩

  · rcases hPiece with hLeft | hRight

    · apply Or.inl

      have hFace :=
        hLeft HilbertParallelepipedFaceIndex.rho0

      change
        HilbertXI25BaseEquivalent
          Geo
          Part.rho0
          (X.leftSolid (Geo := Geo)).rho0
        at hFace

      simpa
        [HilbertXI25SolidCutWitness.leftBase]
        using hFace

    · apply Or.inr

      have hFace :=
        hRight HilbertParallelepipedFaceIndex.rho0

      change
        HilbertXI25BaseEquivalent
          Geo
          Part.rho0
          (X.rightSolid (Geo := Geo)).rho0
        at hFace

      simpa
        [HilbertXI25SolidCutWitness.rightBase]
        using hFace

  · have hFace :=
      hWhole HilbertParallelepipedFaceIndex.rho0

    change
      HilbertXI25BaseEquivalent
        Geo
        Whole.rho0
        (X.wholeSolid (Geo := Geo)).rho0
      at hFace

    simpa
      [HilbertXI25SolidCutWitness.wholeBase]
      using hFace


/--
Common Notion 5 for XI.25 solids: a proper cut part cannot be
XI.Def.10-equal to the whole solid.
-/
theorem HilbertXI25ProperSolidPart.not_equivalent
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Whole : HilbertXI25Parallelepiped Geo}
    (hPart :
      HilbertXI25ProperSolidPart
        (Geo := Geo) Part Whole) :
    Not
      (HilbertXI25SolidEquivalent
        Geo Part Whole) := by

  intro hEq

  have hBasePart :
      HilbertXI25ProperBasePart
        (Geo := Geo)
        Part.rho0
        Whole.rho0 :=
    hPart.rho0_properBasePart
      (Geo := Geo)

  have hBaseEq :
      HilbertXI25BaseEquivalent
        Geo Part.rho0 Whole.rho0 := by

    have hFace :=
      hEq HilbertParallelepipedFaceIndex.rho0

    change
      HilbertXI25BaseEquivalent
        Geo Part.rho0 Whole.rho0
      at hFace

    exact hFace

  exact
    (hBasePart.not_equivalent
      (Geo := Geo))
      hBaseEq


/--
Strict base comparison excludes XI.25 base equality.
-/
theorem HilbertXI25BaseLess.not_equivalent
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {P Q : HilbertParallelogramFace Geo}
    (h :
      HilbertXI25BaseLess
        (Geo := Geo) P Q) :
    Not
      (HilbertXI25BaseEquivalent
        Geo P Q) := by

  exact
    HilbertXI25ProperBasePart.not_equivalent
      (Geo := Geo) h


/--
Strict solid comparison excludes XI.Def.10 equality.
-/
theorem HilbertXI25SolidLess.not_equivalent
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {S T : HilbertXI25Parallelepiped Geo}
    (h :
      HilbertXI25SolidLess
        (Geo := Geo) S T) :
    Not
      (HilbertXI25SolidEquivalent
        Geo S T) := by

  exact
    HilbertXI25ProperSolidPart.not_equivalent
      (Geo := Geo) h


/--
Irreflexivity of strict order on XI.25 base magnitude classes.
-/
theorem hilbertXI25BaseClassLess_irrefl
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a : HilbertXI25BaseClass Geo) :
    Not
      (HilbertXI25BaseClassLess
        (Geo := Geo) a a) := by

  refine Quotient.inductionOn a ?_

  intro P hLess

  change
    HilbertXI25BaseLess
      (Geo := Geo) P P
    at hLess

  exact
    (hLess.not_equivalent
      (Geo := Geo))
      (hilbertXI25BaseEquivalent_refl_space
        (Geo := Geo) P)


/--
Irreflexivity of strict order on XI.25 solid magnitude classes.
-/
theorem hilbertXI25SolidClassLess_irrefl
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a : HilbertXI25SolidClass Geo) :
    Not
      (HilbertXI25SolidClassLess
        (Geo := Geo) a a) := by

  refine Quotient.inductionOn a ?_

  intro S hLess

  change
    HilbertXI25SolidLess
      (Geo := Geo) S S
    at hLess

  exact
    (hLess.not_equivalent
      (Geo := Geo))
      (hilbertXI25SolidEquivalent_refl_space
        (Geo := Geo) S)


/--
Strict base-class comparison implies inequality of magnitude classes.
-/
theorem hilbertXI25BaseClassLess_ne
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {a b : HilbertXI25BaseClass Geo}
    (h :
      HilbertXI25BaseClassLess
        (Geo := Geo) a b) :
    Ne a b := by

  intro hab
  subst b

  exact
    (hilbertXI25BaseClassLess_irrefl
      (Geo := Geo) a)
      h


/--
Strict solid-class comparison implies inequality of magnitude classes.
-/
theorem hilbertXI25SolidClassLess_ne
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {a b : HilbertXI25SolidClass Geo}
    (h :
      HilbertXI25SolidClassLess
        (Geo := Geo) a b) :
    Ne a b := by

  intro hab
  subst b

  exact
    (hilbertXI25SolidClassLess_irrefl
      (Geo := Geo) a)
      h



------------------------------------------------------------------------
-- XI.25: synchronized repeated-slab multiples
------------------------------------------------------------------------

/-!
The positive multiples in Euclid XI.25 are not introduced by a global
addition law on all base or solid classes.

Instead, one repeatedly appends one elementary slab.  A single
geometric cut simultaneously records

    previous base  + unit base  = new base,
    previous solid + unit solid = new solid.

The equalities above are only explanatory notation.  Formally the
statement is represented by one concrete ordered cut and quotient-class
identifications of its left piece, right piece, and whole.

This is the source-faithful recursive notion of an `(n+1)`-fold positive
multiple.  It does not use numerical area, numerical volume, or the
discarded width-defined `LocalFamily` order.
-/

/--
One synchronized addition step for XI.25 magnitudes.

The left piece represents the previously accumulated multiple, the
right piece represents one new unit slab, and the whole represents the
next multiple.
-/
def HilbertXI25AlignedCutSum
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (Pleft : HilbertXI25BaseClass Geo)
    (Sleft : HilbertXI25SolidClass Geo)
    (Pright : HilbertXI25BaseClass Geo)
    (Sright : HilbertXI25SolidClass Geo)
    (Pwhole : HilbertXI25BaseClass Geo)
    (Swhole : HilbertXI25SolidClass Geo) : Prop :=

  Exists
    (fun X : HilbertXI25SolidCutWitness
      (Geo := Geo) =>
      Pleft =
        hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.leftBase (Geo := Geo))
      /\
      Sleft =
        hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.leftSolid (Geo := Geo))
      /\
      Pright =
        hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.rightBase (Geo := Geo))
      /\
      Sright =
        hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.rightSolid (Geo := Geo))
      /\
      Pwhole =
        hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.wholeBase (Geo := Geo))
      /\
      Swhole =
        hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.wholeSolid (Geo := Geo)))


namespace HilbertXI25AlignedCutSum

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
Every concrete XI.25 cut gives its canonical synchronized sum step.
-/
theorem of_cut
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI25AlignedCutSum
      (Geo := Geo)
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.leftBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.leftSolid (Geo := Geo)))
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.rightBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.rightSolid (Geo := Geo)))
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.wholeBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.wholeSolid (Geo := Geo))) := by

  exact
    ⟨X, rfl, rfl, rfl, rfl, rfl, rfl⟩


/--
In every synchronized sum step the accumulated left part is strictly
smaller than the new whole, simultaneously for bases and solids.
-/
theorem left_less
    {Pleft Pright Pwhole :
      HilbertXI25BaseClass Geo}
    {Sleft Sright Swhole :
      HilbertXI25SolidClass Geo}
    (h :
      HilbertXI25AlignedCutSum
        (Geo := Geo)
        Pleft Sleft
        Pright Sright
        Pwhole Swhole) :
    HilbertXI25BaseClassLess
      (Geo := Geo) Pleft Pwhole
    /\
    HilbertXI25SolidClassLess
      (Geo := Geo) Sleft Swhole := by

  rcases h with
    ⟨X,
      hPleft, hSleft,
      _hPright, _hSright,
      hPwhole, hSwhole⟩

  constructor

  · rw [hPleft, hPwhole]

    exact
      (hilbertXI25BaseClassOf_less_iff
        (Geo := Geo)
        (X.leftBase (Geo := Geo))
        (X.wholeBase (Geo := Geo))).2
        (hilbert_XI25_leftBase_properPart_wholeBase
          (Geo := Geo) X)

  · rw [hSleft, hSwhole]

    exact
      (hilbertXI25SolidClassOf_less_iff
        (Geo := Geo)
        (X.leftSolid (Geo := Geo))
        (X.wholeSolid (Geo := Geo))).2
        (hilbert_XI25_left_less_whole
          (Geo := Geo) X)


/--
In every synchronized sum step the newly appended unit is also strictly
smaller than the new whole, simultaneously for bases and solids.
-/
theorem right_less
    {Pleft Pright Pwhole :
      HilbertXI25BaseClass Geo}
    {Sleft Sright Swhole :
      HilbertXI25SolidClass Geo}
    (h :
      HilbertXI25AlignedCutSum
        (Geo := Geo)
        Pleft Sleft
        Pright Sright
        Pwhole Swhole) :
    HilbertXI25BaseClassLess
      (Geo := Geo) Pright Pwhole
    /\
    HilbertXI25SolidClassLess
      (Geo := Geo) Sright Swhole := by

  rcases h with
    ⟨X,
      _hPleft, _hSleft,
      hPright, hSright,
      hPwhole, hSwhole⟩

  constructor

  · rw [hPright, hPwhole]

    exact
      (hilbertXI25BaseClassOf_less_iff
        (Geo := Geo)
        (X.rightBase (Geo := Geo))
        (X.wholeBase (Geo := Geo))).2
        (hilbert_XI25_rightBase_properPart_wholeBase
          (Geo := Geo) X)

  · rw [hSright, hSwhole]

    exact
      (hilbertXI25SolidClassOf_less_iff
        (Geo := Geo)
        (X.rightSolid (Geo := Geo))
        (X.wholeSolid (Geo := Geo))).2
        (hilbert_XI25_right_less_whole
          (Geo := Geo) X)


/--
Neither the accumulated part nor the appended unit can equal the new
whole.
-/
theorem parts_ne_whole
    {Pleft Pright Pwhole :
      HilbertXI25BaseClass Geo}
    {Sleft Sright Swhole :
      HilbertXI25SolidClass Geo}
    (h :
      HilbertXI25AlignedCutSum
        (Geo := Geo)
        Pleft Sleft
        Pright Sright
        Pwhole Swhole) :
    (Ne Pleft Pwhole /\ Ne Sleft Swhole)
    /\
    (Ne Pright Pwhole /\ Ne Sright Swhole) := by

  have hLeft := h.left_less (Geo := Geo)
  have hRight := h.right_less (Geo := Geo)

  exact
    And.intro
      (And.intro
        (hilbertXI25BaseClassLess_ne
          (Geo := Geo) hLeft.1)
        (hilbertXI25SolidClassLess_ne
          (Geo := Geo) hLeft.2))
      (And.intro
        (hilbertXI25BaseClassLess_ne
          (Geo := Geo) hRight.1)
        (hilbertXI25SolidClassLess_ne
          (Geo := Geo) hRight.2))

end HilbertXI25AlignedCutSum


/--
Source-faithful positive repeated multiple.

Indexing matches Book V:

* `0` means one copy;
* `1` means two copies;
* `n` means `n+1` copies.

At every successor stage one geometrically appends one unit slab by an
`HilbertXI25AlignedCutSum`.
-/
def HilbertXI25RepeatedSlabMultiple
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo) :
    Nat ->
    HilbertXI25BaseClass Geo ->
    HilbertXI25SolidClass Geo ->
    Prop

  | 0, totalBase, totalSolid =>
      totalBase = unitBase
      /\
      totalSolid = unitSolid

  | Nat.succ n, totalBase, totalSolid =>
      Exists
        (fun previousBase : HilbertXI25BaseClass Geo =>
          Exists
            (fun previousSolid : HilbertXI25SolidClass Geo =>
              HilbertXI25RepeatedSlabMultiple
                  unitBase unitSolid
                  n previousBase previousSolid
              /\
              HilbertXI25AlignedCutSum
                (Geo := Geo)
                previousBase previousSolid
                unitBase unitSolid
                totalBase totalSolid))


namespace HilbertXI25RepeatedSlabMultiple

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
One copy is the unit base and unit solid themselves.
-/
theorem one
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo) :
    HilbertXI25RepeatedSlabMultiple
      (Geo := Geo)
      unitBase unitSolid
      0 unitBase unitSolid := by

  exact And.intro rfl rfl


/--
Append one unit slab to an already constructed positive multiple.
-/
theorem succ
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo)
    (n : Nat)
    (previousBase totalBase :
      HilbertXI25BaseClass Geo)
    (previousSolid totalSolid :
      HilbertXI25SolidClass Geo)
    (hPrevious :
      HilbertXI25RepeatedSlabMultiple
        (Geo := Geo)
        unitBase unitSolid
        n previousBase previousSolid)
    (hStep :
      HilbertXI25AlignedCutSum
        (Geo := Geo)
        previousBase previousSolid
        unitBase unitSolid
        totalBase totalSolid) :
    HilbertXI25RepeatedSlabMultiple
      (Geo := Geo)
      unitBase unitSolid
      (Nat.succ n) totalBase totalSolid := by

  change
    Exists
      (fun previousBase' : HilbertXI25BaseClass Geo =>
        Exists
          (fun previousSolid' : HilbertXI25SolidClass Geo =>
            HilbertXI25RepeatedSlabMultiple
                (Geo := Geo)
                unitBase unitSolid
                n previousBase' previousSolid'
            /\
            HilbertXI25AlignedCutSum
              (Geo := Geo)
              previousBase' previousSolid'
              unitBase unitSolid
              totalBase totalSolid))

  exact
    ⟨previousBase,
      previousSolid,
      hPrevious,
      hStep⟩


/--
Every nontrivial repeated multiple exposes the previous multiple and
the final synchronized cut used to append one unit.
-/
theorem succ_decompose
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo)
    (n : Nat)
    (totalBase : HilbertXI25BaseClass Geo)
    (totalSolid : HilbertXI25SolidClass Geo)
    (h :
      HilbertXI25RepeatedSlabMultiple
        (Geo := Geo)
        unitBase unitSolid
        (Nat.succ n) totalBase totalSolid) :
    Exists
      (fun previousBase : HilbertXI25BaseClass Geo =>
        Exists
          (fun previousSolid : HilbertXI25SolidClass Geo =>
            HilbertXI25RepeatedSlabMultiple
                (Geo := Geo)
                unitBase unitSolid
                n previousBase previousSolid
            /\
            HilbertXI25AlignedCutSum
              (Geo := Geo)
              previousBase previousSolid
              unitBase unitSolid
              totalBase totalSolid)) := by

  change
    Exists
      (fun previousBase : HilbertXI25BaseClass Geo =>
        Exists
          (fun previousSolid : HilbertXI25SolidClass Geo =>
            HilbertXI25RepeatedSlabMultiple
                (Geo := Geo)
                unitBase unitSolid
                n previousBase previousSolid
            /\
            HilbertXI25AlignedCutSum
              (Geo := Geo)
              previousBase previousSolid
              unitBase unitSolid
              totalBase totalSolid))
    at h

  exact h


/--
The previous multiple is strictly smaller than the next multiple in
both magnitude kinds.
-/
theorem previous_less_of_succ
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo)
    (n : Nat)
    (totalBase : HilbertXI25BaseClass Geo)
    (totalSolid : HilbertXI25SolidClass Geo)
    (h :
      HilbertXI25RepeatedSlabMultiple
        (Geo := Geo)
        unitBase unitSolid
        (Nat.succ n) totalBase totalSolid) :
    Exists
      (fun previousBase : HilbertXI25BaseClass Geo =>
        Exists
          (fun previousSolid : HilbertXI25SolidClass Geo =>
            HilbertXI25RepeatedSlabMultiple
                (Geo := Geo)
                unitBase unitSolid
                n previousBase previousSolid
            /\
            HilbertXI25BaseClassLess
              (Geo := Geo)
              previousBase totalBase
            /\
            HilbertXI25SolidClassLess
              (Geo := Geo)
              previousSolid totalSolid)) := by

  change
    Exists
      (fun previousBase : HilbertXI25BaseClass Geo =>
        Exists
          (fun previousSolid : HilbertXI25SolidClass Geo =>
            HilbertXI25RepeatedSlabMultiple
                (Geo := Geo)
                unitBase unitSolid
                n previousBase previousSolid
            /\
            HilbertXI25AlignedCutSum
              (Geo := Geo)
              previousBase previousSolid
              unitBase unitSolid
              totalBase totalSolid))
    at h

  rcases h with
    ⟨previousBase,
      previousSolid,
      hPrevious,
      hStep⟩

  have hLess :=
    hStep.left_less (Geo := Geo)

  exact
    ⟨previousBase,
      previousSolid,
      hPrevious,
      hLess.1,
      hLess.2⟩


/--
For every successor multiple, one elementary unit is a proper part of
the whole in both magnitude kinds.
-/
theorem unit_less_of_succ
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo)
    (n : Nat)
    (totalBase : HilbertXI25BaseClass Geo)
    (totalSolid : HilbertXI25SolidClass Geo)
    (h :
      HilbertXI25RepeatedSlabMultiple
        (Geo := Geo)
        unitBase unitSolid
        (Nat.succ n) totalBase totalSolid) :
    HilbertXI25BaseClassLess
      (Geo := Geo)
      unitBase totalBase
    /\
    HilbertXI25SolidClassLess
      (Geo := Geo)
      unitSolid totalSolid := by

  change
    Exists
      (fun previousBase : HilbertXI25BaseClass Geo =>
        Exists
          (fun previousSolid : HilbertXI25SolidClass Geo =>
            HilbertXI25RepeatedSlabMultiple
                (Geo := Geo)
                unitBase unitSolid
                n previousBase previousSolid
            /\
            HilbertXI25AlignedCutSum
              (Geo := Geo)
              previousBase previousSolid
              unitBase unitSolid
              totalBase totalSolid))
    at h

  rcases h with
    ⟨previousBase,
      previousSolid,
      _hPrevious,
      hStep⟩

  exact
    hStep.right_less (Geo := Geo)

end HilbertXI25RepeatedSlabMultiple


/--
A complete coherent choice of all positive multiples of one XI.25 base
and solid pair.

The successor field is geometric: each next value must arise by an
actual synchronized cut that appends one new unit slab.
-/
structure HilbertXI25PositiveMultipleSystem
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (unitBase : HilbertXI25BaseClass Geo)
    (unitSolid : HilbertXI25SolidClass Geo) where

  baseMultiple :
    Nat -> HilbertXI25BaseClass Geo

  solidMultiple :
    Nat -> HilbertXI25SolidClass Geo

  zeroBase :
    baseMultiple 0 = unitBase

  zeroSolid :
    solidMultiple 0 = unitSolid

  step :
    forall n : Nat,
      HilbertXI25AlignedCutSum
        (Geo := Geo)
        (baseMultiple n)
        (solidMultiple n)
        unitBase unitSolid
        (baseMultiple (Nat.succ n))
        (solidMultiple (Nat.succ n))


namespace HilbertXI25PositiveMultipleSystem

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
Every entry of a positive-multiple system is an `(n+1)`-fold repeated
slab multiple in the recursive geometric sense above.
-/
theorem repeated
    {unitBase : HilbertXI25BaseClass Geo}
    {unitSolid : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PositiveMultipleSystem
        (Geo := Geo)
        unitBase unitSolid) :
    forall n : Nat,
      HilbertXI25RepeatedSlabMultiple
        (Geo := Geo)
        unitBase unitSolid
        n
        (M.baseMultiple n)
        (M.solidMultiple n) := by

  intro n
  induction n with

  | zero =>
      exact
        And.intro
          M.zeroBase
          M.zeroSolid

  | succ n ih =>
      exact
        HilbertXI25RepeatedSlabMultiple.succ
          (Geo := Geo)
          unitBase unitSolid
          n
          (M.baseMultiple n)
          (M.baseMultiple (Nat.succ n))
          (M.solidMultiple n)
          (M.solidMultiple (Nat.succ n))
          ih
          (M.step n)


/--
Successive positive multiples are strictly increasing on both the base
and solid sides.
-/
theorem step_less
    {unitBase : HilbertXI25BaseClass Geo}
    {unitSolid : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PositiveMultipleSystem
        (Geo := Geo)
        unitBase unitSolid)
    (n : Nat) :
    HilbertXI25BaseClassLess
      (Geo := Geo)
      (M.baseMultiple n)
      (M.baseMultiple (Nat.succ n))
    /\
    HilbertXI25SolidClassLess
      (Geo := Geo)
      (M.solidMultiple n)
      (M.solidMultiple (Nat.succ n)) := by

  exact
    (M.step n).left_less
      (Geo := Geo)


/--
The unit slab is a proper part of every multiple with at least two
copies.
-/
theorem unit_less_succ
    {unitBase : HilbertXI25BaseClass Geo}
    {unitSolid : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PositiveMultipleSystem
        (Geo := Geo)
        unitBase unitSolid)
    (n : Nat) :
    HilbertXI25BaseClassLess
      (Geo := Geo)
      unitBase
      (M.baseMultiple (Nat.succ n))
    /\
    HilbertXI25SolidClassLess
      (Geo := Geo)
      unitSolid
      (M.solidMultiple (Nat.succ n)) := by

  exact
    (M.step n).right_less
      (Geo := Geo)


/--
A positive-multiple system is intentionally local to one paired unit
magnitude.  It therefore does not itself define the global operation

    Nat -> M -> M

required by `EudoxusMagnitude`.

The final XI.25 ratio step will use two such systems, one for each side
of the ratio, and compare their chosen multiple sequences directly.
This avoids reintroducing the rejected width-defined global family.
-/
theorem local_multiple_system_checkpoint
    {unitBase : HilbertXI25BaseClass Geo}
    {unitSolid : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PositiveMultipleSystem
        (Geo := Geo)
        unitBase unitSolid) :
    M.baseMultiple 0 = unitBase
    /\
    M.solidMultiple 0 = unitSolid := by

  exact And.intro M.zeroBase M.zeroSolid

end HilbertXI25PositiveMultipleSystem


/--
Two adjacent equal XI.25 slabs are already the first nontrivial
(two-copy) repeated multiple.

Only equality of the corresponding base faces is required explicitly;
the solid equality follows from the established XI.25 adjacent-solid
theorem.
-/
theorem hilbert_XI25_two_equal_slabs_are_repeated_multiple
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
    HilbertXI25RepeatedSlabMultiple
      (Geo := Geo)
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.leftBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.leftSolid (Geo := Geo)))
      (Nat.succ 0)
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.wholeBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.wholeSolid (Geo := Geo))) := by

  have hSolid :
      HilbertXI25SolidEquivalent
        Geo
        (X.leftSolid (Geo := Geo))
        (X.rightSolid (Geo := Geo)) :=
    hilbert_XI25_adjacent_solids_equal_of_base_equal
      (Geo := Geo)
      X hBase

  have hBaseClass :
      hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.leftBase (Geo := Geo))
        =
      hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.rightBase (Geo := Geo)) :=
    Quotient.sound hBase

  have hSolidClass :
      hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.leftSolid (Geo := Geo))
        =
      hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.rightSolid (Geo := Geo)) :=
    hilbertXI25SolidClass_eq_of_equivalent
      (Geo := Geo)
      hSolid

  have hStep :
      HilbertXI25AlignedCutSum
        (Geo := Geo)
        (hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.leftBase (Geo := Geo)))
        (hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.leftSolid (Geo := Geo)))
        (hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.leftBase (Geo := Geo)))
        (hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.leftSolid (Geo := Geo)))
        (hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.wholeBase (Geo := Geo)))
        (hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.wholeSolid (Geo := Geo))) := by

    exact
      ⟨X,
        rfl,
        rfl,
        hBaseClass,
        hSolidClass,
        rfl,
        rfl⟩

  exact
    HilbertXI25RepeatedSlabMultiple.succ
      (Geo := Geo)
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.leftBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.leftSolid (Geo := Geo)))
      0
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.leftBase (Geo := Geo)))
      (hilbertXI25BaseClassOf
        (Geo := Geo)
        (X.wholeBase (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.leftSolid (Geo := Geo)))
      (hilbertXI25SolidClassOf
        (Geo := Geo)
        (X.wholeSolid (Geo := Geo)))
      (HilbertXI25RepeatedSlabMultiple.one
        (Geo := Geo)
        (hilbertXI25BaseClassOf
          (Geo := Geo)
          (X.leftBase (Geo := Geo)))
        (hilbertXI25SolidClassOf
          (Geo := Geo)
          (X.leftSolid (Geo := Geo))))
      hStep



------------------------------------------------------------------------
-- XI.25: pairwise comparison certificates for chosen multiples
------------------------------------------------------------------------

/-!
At the level of Euclid V.Def.5, a fixed pair of positive multiples has
exactly three relevant comparison outcomes:

    equal,
    left smaller,
    right smaller.

For XI.25 the base comparison and the solid comparison must have the
same outcome. The certificate below records precisely that synchronized
fact for actual quotient magnitude classes.

This is intentionally weaker than a global order/trichotomy theorem.
It is exactly the proposition-specific information supplied by Euclid's
comparison construction for one chosen pair `m,n`.
-/

/--
Synchronized comparison data for one pair of XI.25 base/solid
magnitudes.
-/
def HilbertXI25ClassComparisonCertificate
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a b : HilbertXI25BaseClass Geo)
    (s t : HilbertXI25SolidClass Geo) : Prop :=

  (a = b /\ s = t)
  \/
  (HilbertXI25BaseClassLess
      (Geo := Geo) a b
   /\
   HilbertXI25SolidClassLess
      (Geo := Geo) s t)
  \/
  (HilbertXI25BaseClassLess
      (Geo := Geo) b a
   /\
   HilbertXI25SolidClassLess
      (Geo := Geo) t s)


/--
The only additional order fact needed to turn a synchronized
three-case certificate into the three biconditionals of V.Def.5 is
asymmetry of strict comparison.

We keep this fact explicit. It is not silently built into the
definition of `HilbertXI25BaseClassLess` or
`HilbertXI25SolidClassLess`.
-/
structure HilbertXI25ClassComparisonAsymmetry
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo] : Prop where

  base :
    forall {a b : HilbertXI25BaseClass Geo},
      HilbertXI25BaseClassLess
          (Geo := Geo) a b ->
        Not
          (HilbertXI25BaseClassLess
            (Geo := Geo) b a)

  solid :
    forall {s t : HilbertXI25SolidClass Geo},
      HilbertXI25SolidClassLess
          (Geo := Geo) s t ->
        Not
          (HilbertXI25SolidClassLess
            (Geo := Geo) t s)


namespace HilbertXI25ClassComparisonCertificate

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
A synchronized comparison certificate, together with asymmetry of the
strict relations, gives exactly the three comparison biconditionals
required by Euclid V.Def.5.
-/
theorem toComparisonAgreement
    {a b : HilbertXI25BaseClass Geo}
    {s t : HilbertXI25SolidClass Geo}
    (hAsymm :
      HilbertXI25ClassComparisonAsymmetry
        (Geo := Geo))
    (h :
      HilbertXI25ClassComparisonCertificate
        (Geo := Geo) a b s t) :
    HilbertXI25ClassComparisonAgreement
      (Geo := Geo) a b s t := by

  rcases h with hEqual | hStrict

  · rcases hEqual with
      ⟨hBaseEq, hSolidEq⟩

    constructor

    · constructor

      · intro hBaseLess
        exact False.elim
          ((hilbertXI25BaseClassLess_ne
              (Geo := Geo) hBaseLess)
            hBaseEq)

      · intro hSolidLess
        exact False.elim
          ((hilbertXI25SolidClassLess_ne
              (Geo := Geo) hSolidLess)
            hSolidEq)

    · constructor

      · constructor
        · intro _h
          exact hSolidEq
        · intro _h
          exact hBaseEq

      · constructor

        · intro hBaseLess
          exact False.elim
            ((hilbertXI25BaseClassLess_ne
                (Geo := Geo) hBaseLess)
              hBaseEq.symm)

        · intro hSolidLess
          exact False.elim
            ((hilbertXI25SolidClassLess_ne
                (Geo := Geo) hSolidLess)
              hSolidEq.symm)

  · rcases hStrict with hLeftLess | hRightLess

    · rcases hLeftLess with
        ⟨hBaseLess, hSolidLess⟩

      constructor

      · constructor
        · intro _h
          exact hSolidLess
        · intro _h
          exact hBaseLess

      · constructor

        · constructor

          · intro hEq
            exact False.elim
              ((hilbertXI25BaseClassLess_ne
                  (Geo := Geo) hBaseLess)
                hEq)

          · intro hEq
            exact False.elim
              ((hilbertXI25SolidClassLess_ne
                  (Geo := Geo) hSolidLess)
                hEq)

        · constructor

          · intro hBaseReverse
            exact False.elim
              ((hAsymm.base hBaseLess)
                hBaseReverse)

          · intro hSolidReverse
            exact False.elim
              ((hAsymm.solid hSolidLess)
                hSolidReverse)

    · rcases hRightLess with
        ⟨hBaseReverse, hSolidReverse⟩

      constructor

      · constructor

        · intro hBaseLess
          exact False.elim
            ((hAsymm.base hBaseReverse)
              hBaseLess)

        · intro hSolidLess
          exact False.elim
            ((hAsymm.solid hSolidReverse)
              hSolidLess)

      · constructor

        · constructor

          · intro hEq
            exact False.elim
              ((hilbertXI25BaseClassLess_ne
                  (Geo := Geo) hBaseReverse)
                hEq.symm)

          · intro hEq
            exact False.elim
              ((hilbertXI25SolidClassLess_ne
                  (Geo := Geo) hSolidReverse)
                hEq.symm)

        · constructor
          · intro _h
            exact hSolidReverse
          · intro _h
            exact hBaseReverse

end HilbertXI25ClassComparisonCertificate


/--
A concrete two-slab comparison certificate induces the corresponding
certificate on quotient magnitude classes.
-/
theorem hilbert_XI25_classComparisonCertificate_of_twoSlab
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

  rcases h with hEqual | hStrict

  · apply Or.inl

    have hSolidEqual :
        HilbertXI25SolidEquivalent
          Geo
          (X.leftSolid (Geo := Geo))
          (X.rightSolid (Geo := Geo)) :=
      hilbert_XI25_adjacent_solids_equal_of_base_equal
        (Geo := Geo) X hEqual

    exact
      And.intro
        (Quotient.sound hEqual)
        (Quotient.sound hSolidEqual)

  · rcases hStrict with hLeftLess | hRightLess

    · apply Or.inr
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

    · apply Or.inr
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


------------------------------------------------------------------------
-- XI.25: two local positive-multiple systems
------------------------------------------------------------------------

/-!
Euclid compares the `m`-fold multiple of one base/solid pair with the
`n`-fold multiple of the other pair.

The structure below keeps the two source-faithful positive-multiple
systems separate and records, for every pair of indices, the
synchronized comparison certificate produced by the geometric
comparison construction.

This is the exact local data needed before the final V.Def.5 wrapper.
-/

structure HilbertXI25PairedPositiveMultipleSystems
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a b : HilbertXI25BaseClass Geo)
    (s t : HilbertXI25SolidClass Geo) where

  left :
    HilbertXI25PositiveMultipleSystem
      (Geo := Geo) a s

  right :
    HilbertXI25PositiveMultipleSystem
      (Geo := Geo) b t

  compare :
    forall m n : Nat,
      HilbertXI25ClassComparisonCertificate
        (Geo := Geo)
        (left.baseMultiple m)
        (right.baseMultiple n)
        (left.solidMultiple m)
        (right.solidMultiple n)


namespace HilbertXI25PairedPositiveMultipleSystems

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
Under strict-comparison asymmetry, every selected pair of multiples
satisfies the three V.Def.5 comparison biconditionals.
-/
theorem comparisonAgreement
    {a b : HilbertXI25BaseClass Geo}
    {s t : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PairedPositiveMultipleSystems
        (Geo := Geo) a b s t)
    (hAsymm :
      HilbertXI25ClassComparisonAsymmetry
        (Geo := Geo))
    (m n : Nat) :
    HilbertXI25ClassComparisonAgreement
      (Geo := Geo)
      (M.left.baseMultiple m)
      (M.right.baseMultiple n)
      (M.left.solidMultiple m)
      (M.right.solidMultiple n) := by

  exact
    HilbertXI25ClassComparisonCertificate.toComparisonAgreement
      (Geo := Geo)
      hAsymm
      (M.compare m n)


/--
Local V.Def.5 comparison statement for the two geometrically chosen
multiple systems.
-/
def LocalVDef5
    {a b : HilbertXI25BaseClass Geo}
    {s t : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PairedPositiveMultipleSystems
        (Geo := Geo) a b s t) : Prop :=

  forall m n : Nat,
    HilbertXI25ClassComparisonAgreement
      (Geo := Geo)
      (M.left.baseMultiple m)
      (M.right.baseMultiple n)
      (M.left.solidMultiple m)
      (M.right.solidMultiple n)


/--
The pairwise geometric comparison certificates imply the complete
local V.Def.5 statement once asymmetry of strict comparison is
available.
-/
theorem localVDef5
    {a b : HilbertXI25BaseClass Geo}
    {s t : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PairedPositiveMultipleSystems
        (Geo := Geo) a b s t)
    (hAsymm :
      HilbertXI25ClassComparisonAsymmetry
        (Geo := Geo)) :
    M.LocalVDef5
      (Geo := Geo) := by

  intro m n

  exact
    M.comparisonAgreement
      (Geo := Geo)
      hAsymm m n

end HilbertXI25PairedPositiveMultipleSystems



------------------------------------------------------------------------
-- XI.25: spatial strict segment order and asymmetry
------------------------------------------------------------------------

/-!
The quotient order used by XI.25 is geometric proper-part order.
To prove that it is asymmetric we need one proposition-independent
piece of ambient metric infrastructure: strict comparison of segments
under `HilbertSpaceCongruence`.

We deliberately do not install a global `HilbertCongruence Geo`
instance in 3-space. Instead we reconstruct only the Group III
consequences needed here. Segment-construction uniqueness is reduced to
the already established planar theorem in one explicit carrier plane.

The resulting strict segment order is the direct ambient analogue of
`HilbertSegmentLess`.
-/

/--
Ambient strict comparison of two segments under spatial congruence.
-/
def HilbertXI25SpaceSegmentLess
    (A B C D : Geo.Point) : Prop :=
  Exists
    (fun P : Geo.Point =>
      Geo.Between C P D
      /\
      Geo.Congruent A B C P)


/--
Uniqueness of laying off a segment on an ambient ray.

The candidates and the ray are placed in one explicit carrier plane;
there the ordinary planar uniqueness theorem applies.
-/
theorem hilbert_space_segment_construction_unique_XI25
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B O R X Y : Geo.Point)
    (hOR : Ne O R)
    (hRayX : HilbertSameRay Geo O R X)
    (hRayY : HilbertSameRay Geo O R Y)
    (hOX_AB : Geo.Congruent O X A B)
    (hOY_AB : Geo.Congruent O Y A B) :
    X = Y := by

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo) O R hOR with
    ⟨l, hOl, hRl⟩

  rcases
      hilbert_point_off_line
        (Geo := Geo) l with
    ⟨Z, hZl⟩

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo) l Z hZl with
    ⟨pi, hlpi, _hZpi, _hUnique⟩

  have hOpi : SP.OnPlane O pi :=
    hlpi O hOl

  have hRpi : SP.OnPlane R pi :=
    hlpi R hRl

  have hXpi : SP.OnPlane X pi :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      pi
      O R X
      hOR
      hOpi hRpi
      hRayX.2.2.1

  have hYpi : SP.OnPlane Y pi :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      pi
      O R Y
      hOR
      hOpi hRpi
      hRayY.2.2.1

  let Op : PlanePoint Geo pi :=
    ⟨O, hOpi⟩

  let Rp : PlanePoint Geo pi :=
    ⟨R, hRpi⟩

  let Xp : PlanePoint Geo pi :=
    ⟨X, hXpi⟩

  let Yp : PlanePoint Geo pi :=
    ⟨Y, hYpi⟩

  have hRayXPlane :
      HilbertSameRay
        (PlaneGeo Geo pi) Op Rp Xp := by

    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Rp Xp).mpr

    simpa [Op, Rp, Xp] using hRayX

  have hRayYPlane :
      HilbertSameRay
        (PlaneGeo Geo pi) Op Rp Yp := by

    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi Op Rp Yp).mpr

    simpa [Op, Rp, Yp] using hRayY

  have hOX : Ne O X :=
    hRayX.2.1.symm

  have hOY : Ne O Y :=
    hRayY.2.1.symm

  have hAB_OX :
      Geo.Congruent A B O X :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      O X A B
      hOX
      hOX_AB

  have hAB_OY :
      Geo.Congruent A B O Y :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      O Y A B
      hOY
      hOY_AB

  have hOX_OY :
      Geo.Congruent O X O Y :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A B
      O X
      O Y
      hAB_OX
      hAB_OY

  have hOX_OY_plane :
      (PlaneGeo Geo pi).Congruent
        Op Xp Op Yp := by

    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Op Xp Op Yp).mpr

    simpa [Op, Xp, Yp] using hOX_OY

  have hOX_refl_plane :
      (PlaneGeo Geo pi).Congruent
        Op Xp Op Xp :=
    hilbert_congruent_reflexive
      (PlaneGeo Geo pi)
      Op Xp

  have hOY_OX_plane :
      (PlaneGeo Geo pi).Congruent
        Op Yp Op Xp :=
    HilbertCongruence.segment_congruence_common
      (Geo := PlaneGeo Geo pi)
      Op Xp
      Op Yp
      Op Xp
      hOX_OY_plane
      hOX_refl_plane

  have hXYplane : Xp = Yp :=
    hilbert_segment_construction_unique
      (PlaneGeo Geo pi)
      Op Xp
      Op Rp
      Xp Yp
      hRayXPlane
      hRayYPlane
      hOX_refl_plane
      hOY_OX_plane

  exact
    congrArg Subtype.val hXYplane


/--
Ambient version of the standard layoff lemma: if AB is a proper part
of AC and congruent copies OP,OQ are laid off on the same ray, then
P lies between O and Q.
-/
theorem hilbert_space_layoff_shorter_between_XI25
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B C O R P Q : Geo.Point)
    (hABC : Geo.Between A B C)
    (hRayP : HilbertSameRay Geo O R P)
    (hRayQ : HilbertSameRay Geo O R Q)
    (hOP_AB : Geo.Congruent O P A B)
    (hOQ_AC : Geo.Congruent O Q A C) :
    Geo.Between O P Q := by

  have hABCdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A B C hABC

  have hBC : Ne B C :=
    hABCdata.2.1

  have hOP : Ne O P :=
    hRayP.2.1.symm

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo)
        O P hOP with
    ⟨T, hOPT⟩

  have hPT : Ne P T :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      O P T hOPT).2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        B C
        P T
        hPT with
    ⟨S, hRayTS, hPS_BC⟩

  have hRayPOO :
      HilbertSameRay Geo P O O :=
    hilbert_sameRay_refl
      Geo P O hOP

  have hOPS :
      Geo.Between O P S :=
    hilbert_between_transport_sameRays
      Geo
      O P T
      O S
      hOPT
      hRayPOO
      hRayTS

  have hOS_AC :
      Geo.Congruent O S A C :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      O P S
      A B C
      hOPS
      hABC
      hOP_AB
      hPS_BC

  have hRayOPS :
      HilbertSameRay Geo O P S :=
    hilbert_sameRay_of_between
      Geo O P S hOPS

  have hRayOPR :
      HilbertSameRay Geo O P R :=
    hilbert_sameRay_symm
      Geo O R P hRayP

  have hRayORS :
      HilbertSameRay Geo O R S :=
    hilbert_sameRay_of_common
      Geo
      O P R S
      hRayOPR
      hRayOPS

  have hOR : Ne O R :=
    hRayP.1.symm

  have hSQ : S = Q :=
    hilbert_space_segment_construction_unique_XI25
      (Geo := Geo)
      A C
      O R
      S Q
      hOR
      hRayORS
      hRayQ
      hOS_AC
      hOQ_AC

  subst S

  exact hOPS


/--
Left transport of ambient strict segment comparison through spatial
congruence.
-/
theorem hilbert_space_segmentLess_congruent_left_XI25
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B A' B' C D : Geo.Point)
    (hLess :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo) A B C D)
    (hA'B' : Ne A' B')
    (hCong :
      Geo.Congruent A' B' A B) :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo) A' B' C D := by

  rcases hLess with
    ⟨P, hCPD, hAB_CP⟩

  have hAB_A'B' :
      Geo.Congruent A B A' B' :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A' B' A B
      hA'B'
      hCong

  have hA'B'_CP :
      Geo.Congruent A' B' C P :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A B
      A' B'
      C P
      hAB_A'B'
      hAB_CP

  exact
    ⟨P, hCPD, hA'B'_CP⟩


/--
Right transport of ambient strict segment comparison through spatial
congruence.
-/
theorem hilbert_space_segmentLess_congruent_right_XI25
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B C D C' D' : Geo.Point)
    (hLess :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo) A B C D)
    (hAB : Ne A B)
    (hC'D' : Ne C' D')
    (hCong :
      Geo.Congruent C D C' D') :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo) A B C' D' := by

  rcases hLess with
    ⟨P, hCPD, hAB_CP⟩

  have hCPDdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C P D hCPD

  have hCP : Ne C P :=
    hCPDdata.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        C P
        C' D'
        hC'D' with
    ⟨P', hRayP', hC'P'_CP⟩

  have hRayD' :
      HilbertSameRay Geo C' D' D' :=
    hilbert_sameRay_refl
      Geo C' D' hC'D'.symm

  have hC'P' : Ne C' P' :=
    hRayP'.2.1.symm

  have hCP_C'P' :
      Geo.Congruent C P C' P' :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      C' P'
      C P
      hC'P'
      hC'P'_CP

  have hCD : Ne C D :=
    hCPDdata.2.2.1

  have hC'D'_CD :
      Geo.Congruent C' D' C D :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      C D
      C' D'
      hCD
      hCong

  have hC'P'D' :
      Geo.Between C' P' D' :=
    hilbert_space_layoff_shorter_between_XI25
      (Geo := Geo)
      C P D
      C' D'
      P' D'
      hCPD
      hRayP'
      hRayD'
      hC'P'_CP
      hC'D'_CD

  have hCP_AB :
      Geo.Congruent C P A B :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A B
      C P
      hAB
      hAB_CP

  have hAB_C'P' :
      Geo.Congruent A B C' P' :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      C P
      A B
      C' P'
      hCP_AB
      hCP_C'P'

  exact
    ⟨P',
      hC'P'D',
      hAB_C'P'⟩


/--
A prefix determined by betweenness is strictly shorter than the whole
ambient segment.
-/
theorem hilbert_space_segmentLess_of_between_XI25
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      A B A C := by

  have hAB : Ne A B :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A B C hABC).1

  exact
    ⟨B,
      hABC,
      hilbert_space_congruent_reflexive
        (Geo := Geo)
        A B hAB⟩


/--
A suffix determined by betweenness is also strictly shorter than the
whole ambient segment.
-/
theorem hilbert_space_segmentLess_suffix_of_between_XI25
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      B C A C := by

  have hData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A B C hABC

  have hCB_A :
      Geo.Between C B A :=
    hData.2.2.2.2

  have hCB : Ne C B :=
    hData.2.1.symm

  have hCA : Ne C A :=
    hData.2.2.1.symm

  have hBC : Ne B C :=
    hData.2.1

  have hAC : Ne A C :=
    hData.2.2.1

  have h0 :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo)
        C B C A :=
    hilbert_space_segmentLess_of_between_XI25
      (Geo := Geo)
      C B A hCB_A

  have hCB_CB :
      Geo.Congruent C B C B :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      C B hCB

  have hBC_CB :
      Geo.Congruent B C C B :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      C B C B).mp
      hCB_CB

  have h1 :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo)
        B C C A :=
    hilbert_space_segmentLess_congruent_left_XI25
      (Geo := Geo)
      C B
      B C
      C A
      h0
      hBC
      hBC_CB

  have hCA_CA :
      Geo.Congruent C A C A :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      C A hCA

  have hCA_AC :
      Geo.Congruent C A A C :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      C A C A).mp
      hCA_CA

  exact
    hilbert_space_segmentLess_congruent_right_XI25
      (Geo := Geo)
      B C
      C A
      A C
      h1
      hBC
      hAC
      hCA_AC


/--
Asymmetry of ambient strict segment comparison.

This is the spatial Group III analogue of
`hilbert_segmentLess_asymm`.
-/
theorem hilbert_space_segmentLess_asymm_XI25
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B C D : Geo.Point)
    (hABCD :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo) A B C D) :
    Not
      (HilbertXI25SpaceSegmentLess
        (Geo := Geo) C D A B) := by

  intro hCDAB

  rcases hABCD with
    ⟨P, hCPD, hAB_CP⟩

  rcases hCDAB with
    ⟨Q, hAQB, hCD_AQ⟩

  have hAB : Ne A B :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A Q B hAQB).2.2.1

  rcases
      HilbertSpaceOrder.between_extension
        (Geo := Geo)
        A B hAB with
    ⟨S, hABS⟩

  have hBS : Ne B S :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A B S hABS).2.1

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        P D
        B S
        hBS with
    ⟨R, hRayR, hBR_PD⟩

  have hRayA :
      HilbertSameRay Geo B A A :=
    hilbert_sameRay_refl
      Geo B A hAB

  have hABR :
      Geo.Between A B R :=
    hilbert_between_transport_sameRays
      Geo
      A B S
      A R
      hABS
      hRayA
      hRayR

  have hCP_AB :
      Geo.Congruent C P A B :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A B
      C P
      hAB
      hAB_CP

  have hBR : Ne B R :=
    hRayR.2.1.symm

  have hPD_BR :
      Geo.Congruent P D B R :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      B R
      P D
      hBR
      hBR_PD

  have hCD_AR :
      Geo.Congruent C D A R :=
    HilbertSpaceCongruence.segment_additivity
      (Geo := Geo)
      C P D
      A B R
      hCPD
      hABR
      hCP_AB
      hPD_BR

  have hCD : Ne C D :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      C P D hCPD).2.2.1

  have hAR_CD :
      Geo.Congruent A R C D :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      C D
      A R
      hCD
      hCD_AR

  have hAQ_CD :
      Geo.Congruent A Q C D :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      C D
      A Q
      hCD
      hCD_AQ

  have hRayQ0 :
      HilbertSameRay Geo A Q B :=
    hilbert_sameRay_of_between
      Geo A Q B hAQB

  have hRayQ :
      HilbertSameRay Geo A B Q :=
    hilbert_sameRay_symm
      Geo A Q B hRayQ0

  have hRayR' :
      HilbertSameRay Geo A B R :=
    hilbert_sameRay_of_between
      Geo A B R hABR

  have hRQ : R = Q :=
    hilbert_space_segment_construction_unique_XI25
      (Geo := Geo)
      C D
      A B
      R Q
      hAB
      hRayR'
      hRayQ
      hAR_CD
      hAQ_CD

  subst R

  have hAQBcol :
      PrimCollinear Geo A Q B :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      A Q B hAQB).2.2.2.1

  have hNotABQ :
      Not (Geo.Between A B Q) :=
    (HilbertSpaceOrder.between_unique
      (Geo := Geo)
      A Q B
      hAQBcol
      hAQB).2

  exact hNotABQ hABR


------------------------------------------------------------------------
-- XI.25: canonical base width comparison
------------------------------------------------------------------------

/--
The canonical longitudinal side `b-c` of every parallelogram face is
nondegenerate.
-/
theorem hilbert_XI25_base_width_ne
    (P : HilbertParallelogramFace Geo) :
    Ne P.b P.c :=

  P.isParallelogram.2.1


/--
The left cut base has strictly smaller longitudinal width than the
whole cut base.
-/
theorem hilbert_XI25_leftBase_width_less_wholeBase
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
      (Geo := Geo)) :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      (X.leftBase (Geo := Geo)).b
      (X.leftBase (Geo := Geo)).c
      (X.wholeBase (Geo := Geo)).b
      (X.wholeBase (Geo := Geo)).c := by

  change
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      X.B0 X.B1
      X.B0 X.B2

  exact
    hilbert_space_segmentLess_of_between_XI25
      (Geo := Geo)
      X.B0 X.B1 X.B2
      X.ordered.between_B


/--
The right cut base also has strictly smaller longitudinal width than
the whole cut base.
-/
theorem hilbert_XI25_rightBase_width_less_wholeBase
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
      (Geo := Geo)) :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      (X.rightBase (Geo := Geo)).b
      (X.rightBase (Geo := Geo)).c
      (X.wholeBase (Geo := Geo)).b
      (X.wholeBase (Geo := Geo)).c := by

  change
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      X.B1 X.B2
      X.B0 X.B2

  exact
    hilbert_space_segmentLess_suffix_of_between_XI25
      (Geo := Geo)
      X.B0 X.B1 X.B2
      X.ordered.between_B


/--
Every XI.25 proper-base-part witness induces a strict comparison of
the canonical longitudinal side lengths.
-/
theorem HilbertXI25ProperBasePart.width_less
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {Part Whole : HilbertParallelogramFace Geo}
    (h :
      HilbertXI25ProperBasePart
        (Geo := Geo) Part Whole) :
    HilbertXI25SpaceSegmentLess
      (Geo := Geo)
      Part.b Part.c
      Whole.b Whole.c := by

  rcases h with
    ⟨X, hPiece, hWhole⟩

  have hPartNe :
      Ne Part.b Part.c :=
    hilbert_XI25_base_width_ne
      (Geo := Geo) Part

  have hWholeNe :
      Ne Whole.b Whole.c :=
    hilbert_XI25_base_width_ne
      (Geo := Geo) Whole

  rcases hPiece with hLeft | hRight

  · have hCanonical :
        HilbertXI25SpaceSegmentLess
          (Geo := Geo)
          (X.leftBase (Geo := Geo)).b
          (X.leftBase (Geo := Geo)).c
          (X.wholeBase (Geo := Geo)).b
          (X.wholeBase (Geo := Geo)).c :=
      hilbert_XI25_leftBase_width_less_wholeBase
        (Geo := Geo) X

    change
      TriangleCongruenceResult
        Geo
        Part.b Part.a Part.c
        (X.leftBase (Geo := Geo)).b
        (X.leftBase (Geo := Geo)).a
        (X.leftBase (Geo := Geo)).c
      at hLeft

    change
      TriangleCongruenceResult
        Geo
        Whole.b Whole.a Whole.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).a
        (X.wholeBase (Geo := Geo)).c
      at hWhole

    have h1 :
        HilbertXI25SpaceSegmentLess
          (Geo := Geo)
          Part.b Part.c
          (X.wholeBase (Geo := Geo)).b
          (X.wholeBase (Geo := Geo)).c :=
      hilbert_space_segmentLess_congruent_left_XI25
        (Geo := Geo)
        (X.leftBase (Geo := Geo)).b
        (X.leftBase (Geo := Geo)).c
        Part.b Part.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).c
        hCanonical
        hPartNe
        hLeft.sideAC

    have hWholeCanonical :
        Geo.Congruent
          (X.wholeBase (Geo := Geo)).b
          (X.wholeBase (Geo := Geo)).c
          Whole.b Whole.c :=
      hilbert_space_congruent_symmetry
        (Geo := Geo)
        Whole.b Whole.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).c
        hWholeNe
        hWhole.sideAC

    exact
      hilbert_space_segmentLess_congruent_right_XI25
        (Geo := Geo)
        Part.b Part.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).c
        Whole.b Whole.c
        h1
        hPartNe
        hWholeNe
        hWholeCanonical

  · have hCanonical :
        HilbertXI25SpaceSegmentLess
          (Geo := Geo)
          (X.rightBase (Geo := Geo)).b
          (X.rightBase (Geo := Geo)).c
          (X.wholeBase (Geo := Geo)).b
          (X.wholeBase (Geo := Geo)).c :=
      hilbert_XI25_rightBase_width_less_wholeBase
        (Geo := Geo) X

    change
      TriangleCongruenceResult
        Geo
        Part.b Part.a Part.c
        (X.rightBase (Geo := Geo)).b
        (X.rightBase (Geo := Geo)).a
        (X.rightBase (Geo := Geo)).c
      at hRight

    change
      TriangleCongruenceResult
        Geo
        Whole.b Whole.a Whole.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).a
        (X.wholeBase (Geo := Geo)).c
      at hWhole

    have h1 :
        HilbertXI25SpaceSegmentLess
          (Geo := Geo)
          Part.b Part.c
          (X.wholeBase (Geo := Geo)).b
          (X.wholeBase (Geo := Geo)).c :=
      hilbert_space_segmentLess_congruent_left_XI25
        (Geo := Geo)
        (X.rightBase (Geo := Geo)).b
        (X.rightBase (Geo := Geo)).c
        Part.b Part.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).c
        hCanonical
        hPartNe
        hRight.sideAC

    have hWholeCanonical :
        Geo.Congruent
          (X.wholeBase (Geo := Geo)).b
          (X.wholeBase (Geo := Geo)).c
          Whole.b Whole.c :=
      hilbert_space_congruent_symmetry
        (Geo := Geo)
        Whole.b Whole.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).c
        hWholeNe
        hWhole.sideAC

    exact
      hilbert_space_segmentLess_congruent_right_XI25
        (Geo := Geo)
        Part.b Part.c
        (X.wholeBase (Geo := Geo)).b
        (X.wholeBase (Geo := Geo)).c
        Whole.b Whole.c
        h1
        hPartNe
        hWholeNe
        hWholeCanonical


/--
Asymmetry of XI.25 proper-base comparison.
-/
theorem HilbertXI25BaseLess.asymm
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {P Q : HilbertParallelogramFace Geo}
    (hPQ :
      HilbertXI25BaseLess
        (Geo := Geo) P Q) :
    Not
      (HilbertXI25BaseLess
        (Geo := Geo) Q P) := by

  intro hQP

  have hWidthPQ :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo)
        P.b P.c Q.b Q.c :=
    HilbertXI25ProperBasePart.width_less
      (Geo := Geo) hPQ

  have hWidthQP :
      HilbertXI25SpaceSegmentLess
        (Geo := Geo)
        Q.b Q.c P.b P.c :=
    HilbertXI25ProperBasePart.width_less
      (Geo := Geo) hQP

  exact
    (hilbert_space_segmentLess_asymm_XI25
      (Geo := Geo)
      P.b P.c Q.b Q.c
      hWidthPQ)
      hWidthQP


/--
Asymmetry of XI.25 proper-solid comparison follows from the `rho0`
proper-base comparison.
-/
theorem HilbertXI25SolidLess.asymm
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {S T : HilbertXI25Parallelepiped Geo}
    (hST :
      HilbertXI25SolidLess
        (Geo := Geo) S T) :
    Not
      (HilbertXI25SolidLess
        (Geo := Geo) T S) := by

  intro hTS

  have hBaseST :
      HilbertXI25BaseLess
        (Geo := Geo)
        S.rho0 T.rho0 :=
    HilbertXI25ProperSolidPart.rho0_properBasePart
      (Geo := Geo) hST

  have hBaseTS :
      HilbertXI25BaseLess
        (Geo := Geo)
        T.rho0 S.rho0 :=
    HilbertXI25ProperSolidPart.rho0_properBasePart
      (Geo := Geo) hTS

  exact
    (hBaseST.asymm
      (Geo := Geo))
      hBaseTS


/--
Asymmetry of strict comparison on XI.25 base quotient classes.
-/
theorem hilbertXI25BaseClassLess_asymm
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (a b : HilbertXI25BaseClass Geo)
    (hab :
      HilbertXI25BaseClassLess
        (Geo := Geo) a b) :
    Not
      (HilbertXI25BaseClassLess
        (Geo := Geo) b a) := by

  revert hab

  refine Quotient.inductionOn₂ a b ?_

  intro P Q

  change
    HilbertXI25BaseLess
        (Geo := Geo) P Q
      ->
    Not
      (HilbertXI25BaseLess
        (Geo := Geo) Q P)

  exact
    fun hPQ =>
      hPQ.asymm
        (Geo := Geo)


/--
Asymmetry of strict comparison on XI.25 solid quotient classes.
-/
theorem hilbertXI25SolidClassLess_asymm
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (s t : HilbertXI25SolidClass Geo)
    (hst :
      HilbertXI25SolidClassLess
        (Geo := Geo) s t) :
    Not
      (HilbertXI25SolidClassLess
        (Geo := Geo) t s) := by

  revert hst

  refine Quotient.inductionOn₂ s t ?_

  intro S T

  change
    HilbertXI25SolidLess
        (Geo := Geo) S T
      ->
    Not
      (HilbertXI25SolidLess
        (Geo := Geo) T S)

  exact
    fun hST =>
      hST.asymm
        (Geo := Geo)


/--
The asymmetry package previously kept explicit as a missing obligation
is now a theorem of the existing spatial Hilbert infrastructure.
-/
theorem hilbert_XI25_classComparisonAsymmetry
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo] :
    HilbertXI25ClassComparisonAsymmetry
      (Geo := Geo) := by

  exact
    {
      base := by
        intro a b hab
        exact
          hilbertXI25BaseClassLess_asymm
            (Geo := Geo)
            a b hab

      solid := by
        intro s t hst
        exact
          hilbertXI25SolidClassLess_asymm
            (Geo := Geo)
            s t hst
    }


/--
The local V.Def.5 statement for a paired multiple system no longer
needs asymmetry as an external hypothesis.
-/
theorem HilbertXI25PairedPositiveMultipleSystems.localVDef5_proved
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {a b : HilbertXI25BaseClass Geo}
    {s t : HilbertXI25SolidClass Geo}
    (M :
      HilbertXI25PairedPositiveMultipleSystems
        (Geo := Geo) a b s t) :
    M.LocalVDef5
      (Geo := Geo) := by

  exact
    M.localVDef5
      (Geo := Geo)
      (hilbert_XI25_classComparisonAsymmetry
        (Geo := Geo))



------------------------------------------------------------------------
-- XI.25: noncircular width-faithful local families
------------------------------------------------------------------------

/-!
The old `HilbertXI25LocalFamily` was useful as a representation device,
but its generated base and solid orders were both defined directly from
width order.  That is too weak for the final XI.25 proof: it makes the
comparison conclusion true by definition.

The structure below reverses the dependency.

* width keeps the existing Book V order in one fixed `PlaneGeo rho`;
* bases keep the geometric quotient order `HilbertXI25BaseClassLess`;
* solids keep the geometric quotient order `HilbertXI25SolidClassLess`;
* the family must prove that a strict width comparison produces the
  corresponding genuine base and solid proper-part comparisons.

From this one geometric transfer theorem and trichotomy of positive
segment classes, strict comparison is automatically reflected as well.
Thus the generated Eudoxus magnitudes below use the actual geometric
base/solid orders, not a width-defined surrogate.
-/

/--
A local XI.25 family in one fixed carrier plane whose width order
faithfully generates genuine base and solid comparisons.
-/
structure HilbertXI25ComparisonFaithfulFamily
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (rho : SP.Plane) where

  baseAt :
    HilbertXI25WidthClass
        (Geo := Geo) rho ->
      HilbertXI25BaseClass Geo

  solidAt :
    HilbertXI25WidthClass
        (Geo := Geo) rho ->
      HilbertXI25SolidClass Geo

  less_transfer :
    forall x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho,
      HilbertPositiveSegmentLess
          (PlaneGeo Geo rho) x y ->
        HilbertXI25BaseClassLess
            (Geo := Geo)
            (baseAt x) (baseAt y)
        /\
        HilbertXI25SolidClassLess
            (Geo := Geo)
            (solidAt x) (solidAt y)


namespace HilbertXI25ComparisonFaithfulFamily

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
For a faithful family, genuine base comparison is equivalent to strict
width comparison.
-/
theorem base_less_iff_width_less
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25BaseClassLess
        (Geo := Geo)
        (F.baseAt x) (F.baseAt y)
      <->
    HilbertPositiveSegmentLess
      (PlaneGeo Geo rho) x y := by

  constructor

  · intro hBase

    rcases
        hilbertPositiveSegmentLess_trichotomy
          (PlaneGeo Geo rho) x y
      with hxy | hEq | hyx

    · exact hxy

    · subst y

      exact
        False.elim
          ((hilbertXI25BaseClassLess_irrefl
              (Geo := Geo)
              (F.baseAt x))
            hBase)

    · have hReverse :
          HilbertXI25BaseClassLess
            (Geo := Geo)
            (F.baseAt y) (F.baseAt x) :=
        (F.less_transfer y x hyx).1

      exact
        False.elim
          ((hilbertXI25BaseClassLess_asymm
              (Geo := Geo)
              (F.baseAt x) (F.baseAt y)
              hBase)
            hReverse)

  · intro hxy
    exact
      (F.less_transfer x y hxy).1


/--
For a faithful family, genuine solid comparison is equivalent to strict
width comparison.
-/
theorem solid_less_iff_width_less
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25SolidClassLess
        (Geo := Geo)
        (F.solidAt x) (F.solidAt y)
      <->
    HilbertPositiveSegmentLess
      (PlaneGeo Geo rho) x y := by

  constructor

  · intro hSolid

    rcases
        hilbertPositiveSegmentLess_trichotomy
          (PlaneGeo Geo rho) x y
      with hxy | hEq | hyx

    · exact hxy

    · subst y

      exact
        False.elim
          ((hilbertXI25SolidClassLess_irrefl
              (Geo := Geo)
              (F.solidAt x))
            hSolid)

    · have hReverse :
          HilbertXI25SolidClassLess
            (Geo := Geo)
            (F.solidAt y) (F.solidAt x) :=
        (F.less_transfer y x hyx).2

      exact
        False.elim
          ((hilbertXI25SolidClassLess_asymm
              (Geo := Geo)
              (F.solidAt x) (F.solidAt y)
              hSolid)
            hReverse)

  · intro hxy
    exact
      (F.less_transfer x y hxy).2


/--
The width parameter is injective on generated base classes.
-/
theorem baseAt_injective
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho) :
    Function.Injective F.baseAt := by

  intro x y hEq

  rcases
      hilbertPositiveSegmentLess_trichotomy
        (PlaneGeo Geo rho) x y
    with hxy | hxy | hyx

  · have hLess :
        HilbertXI25BaseClassLess
          (Geo := Geo)
          (F.baseAt x) (F.baseAt y) :=
      (F.less_transfer x y hxy).1

    exact
      False.elim
        ((hilbertXI25BaseClassLess_ne
            (Geo := Geo) hLess)
          hEq)

  · exact hxy

  · have hLess :
        HilbertXI25BaseClassLess
          (Geo := Geo)
          (F.baseAt y) (F.baseAt x) :=
      (F.less_transfer y x hyx).1

    exact
      False.elim
        ((hilbertXI25BaseClassLess_ne
            (Geo := Geo) hLess)
          hEq.symm)


/--
The width parameter is injective on generated solid classes.
-/
theorem solidAt_injective
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho) :
    Function.Injective F.solidAt := by

  intro x y hEq

  rcases
      hilbertPositiveSegmentLess_trichotomy
        (PlaneGeo Geo rho) x y
    with hxy | hxy | hyx

  · have hLess :
        HilbertXI25SolidClassLess
          (Geo := Geo)
          (F.solidAt x) (F.solidAt y) :=
      (F.less_transfer x y hxy).2

    exact
      False.elim
        ((hilbertXI25SolidClassLess_ne
            (Geo := Geo) hLess)
          hEq)

  · exact hxy

  · have hLess :
        HilbertXI25SolidClassLess
          (Geo := Geo)
          (F.solidAt y) (F.solidAt x) :=
      (F.less_transfer y x hyx).2

    exact
      False.elim
        ((hilbertXI25SolidClassLess_ne
            (Geo := Geo) hLess)
          hEq.symm)


/--
Equality of generated base classes is exactly equality of widths.
-/
theorem baseAt_eq_iff
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    F.baseAt x = F.baseAt y
      <->
    x = y := by

  constructor

  · intro hEq
    exact
      HilbertXI25ComparisonFaithfulFamily.baseAt_injective
        (Geo := Geo) F hEq

  · intro h
    exact congrArg F.baseAt h


/--
Equality of generated solid classes is exactly equality of widths.
-/
theorem solidAt_eq_iff
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    F.solidAt x = F.solidAt y
      <->
    x = y := by

  constructor

  · intro hEq
    exact
      HilbertXI25ComparisonFaithfulFamily.solidAt_injective
        (Geo := Geo) F hEq

  · intro h
    exact congrArg F.solidAt h


/--
One width trichotomy produces the synchronized base/solid comparison
certificate required by XI.25.
-/
theorem comparisonCertificate
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25ClassComparisonCertificate
      (Geo := Geo)
      (F.baseAt x)
      (F.baseAt y)
      (F.solidAt x)
      (F.solidAt y) := by

  rcases
      hilbertPositiveSegmentLess_trichotomy
        (PlaneGeo Geo rho) x y
    with hxy | hEq | hyx

  · exact
      Or.inr
        (Or.inl
          (F.less_transfer x y hxy))

  · subst y
    exact
      Or.inl
        (And.intro rfl rfl)

  · exact
      Or.inr
        (Or.inr
          (F.less_transfer y x hyx))


/--
Actual geometric base magnitude generated by a faithful width family.

The carrier is still the width class, but strict comparison is the
genuine XI.25 base proper-part relation.
-/
noncomputable def baseEudoxusMagnitude
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho) :
    EudoxusMagnitude
      (HilbertXI25WidthClass
        (Geo := Geo) rho) where

  less :=
    fun x y =>
      HilbertXI25BaseClassLess
        (Geo := Geo)
        (F.baseAt x) (F.baseAt y)

  multiple :=
    fun n x =>
      hilbertPositiveSegmentMultiple
        (PlaneGeo Geo rho) n x


/--
Actual geometric solid magnitude generated by a faithful width family.

Strict comparison is the genuine XI.25 solid proper-part relation.
-/
noncomputable def solidEudoxusMagnitude
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho) :
    EudoxusMagnitude
      (HilbertXI25WidthClass
        (Geo := Geo) rho) where

  less :=
    fun x y =>
      HilbertXI25SolidClassLess
        (Geo := Geo)
        (F.solidAt x) (F.solidAt y)

  multiple :=
    fun n x =>
      hilbertPositiveSegmentMultiple
        (PlaneGeo Geo rho) n x


/--
Faithful embedding of the ordinary positive width magnitude into the
actual geometric base magnitude.
-/
noncomputable def widthToBaseMagnitude
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho) :
    EudoxusMagnitudeEmbedding
      (hilbertPositiveSegmentEudoxusMagnitude
        (Geo := PlaneGeo Geo rho))
      (F.baseEudoxusMagnitude
        (Geo := Geo)) where

  toFun := id

  map_multiple := by
    intro n x
    rfl

  less_iff := by
    intro x y
    exact
      (F.base_less_iff_width_less
        (Geo := Geo) x y).symm

  injective := by
    intro x y h
    exact h


/--
Faithful embedding of the ordinary positive width magnitude into the
actual geometric solid magnitude.
-/
noncomputable def widthToSolidMagnitude
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho) :
    EudoxusMagnitudeEmbedding
      (hilbertPositiveSegmentEudoxusMagnitude
        (Geo := PlaneGeo Geo rho))
      (F.solidEudoxusMagnitude
        (Geo := Geo)) where

  toFun := id

  map_multiple := by
    intro n x
    rfl

  less_iff := by
    intro x y
    exact
      (F.solid_less_iff_width_less
        (Geo := Geo) x y).symm

  injective := by
    intro x y h
    exact h


/--
Noncircular Eudoxus conclusion for a faithful XI.25 family.

The source order is width order, but the two target orders are the
actual geometric base and solid proper-part relations.
-/
theorem eudoxusProportion
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    EudoxusProportionBetween
      (F.baseEudoxusMagnitude
        (Geo := Geo))
      (F.solidEudoxusMagnitude
        (Geo := Geo))
      a b a b := by

  exact
    eudoxusProportionBetween_of_common_source
      (F.widthToBaseMagnitude
        (Geo := Geo))
      (F.widthToSolidMagnitude
        (Geo := Geo))
      a b


/--
The comparison certificate for arbitrary positive multiples follows
directly from Book V trichotomy on the corresponding width multiples.
-/
theorem multipleComparisonCertificate
    {rho : SP.Plane}
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho)
    (m n : Nat) :
    HilbertXI25ClassComparisonCertificate
      (Geo := Geo)
      (F.baseAt
        (hilbertPositiveSegmentMultiple
          (PlaneGeo Geo rho) m a))
      (F.baseAt
        (hilbertPositiveSegmentMultiple
          (PlaneGeo Geo rho) n b))
      (F.solidAt
        (hilbertPositiveSegmentMultiple
          (PlaneGeo Geo rho) m a))
      (F.solidAt
        (hilbertPositiveSegmentMultiple
          (PlaneGeo Geo rho) n b)) := by

  exact
    F.comparisonCertificate
      (Geo := Geo)
      (hilbertPositiveSegmentMultiple
        (PlaneGeo Geo rho) m a)
      (hilbertPositiveSegmentMultiple
        (PlaneGeo Geo rho) n b)

end HilbertXI25ComparisonFaithfulFamily


------------------------------------------------------------------------
-- XI.25: width-tracked geometric multiple systems
------------------------------------------------------------------------

/-!
The following structure connects the abstract faithful-family conclusion
back to Euclid's actual repeated slab construction.

The two `HilbertXI25PositiveMultipleSystem`s certify that every successor
is obtained by a genuine synchronized geometric cut.

The `left_spec` and `right_spec` fields say that the selected geometric
multiples are exactly the images of the corresponding positive width
multiples.  Therefore their pairwise comparison certificates no longer
need to be postulated: they are generated by width trichotomy.
-/

structure HilbertXI25WidthTrackedPairedMultipleSystems
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (rho : SP.Plane)
    (F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho)
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho) where

  left :
    HilbertXI25PositiveMultipleSystem
      (Geo := Geo)
      (F.baseAt a)
      (F.solidAt a)

  right :
    HilbertXI25PositiveMultipleSystem
      (Geo := Geo)
      (F.baseAt b)
      (F.solidAt b)

  left_spec :
    forall n : Nat,
      left.baseMultiple n =
        F.baseAt
          (hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho) n a)
      /\
      left.solidMultiple n =
        F.solidAt
          (hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho) n a)

  right_spec :
    forall n : Nat,
      right.baseMultiple n =
        F.baseAt
          (hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho) n b)
      /\
      right.solidMultiple n =
        F.solidAt
          (hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho) n b)


namespace HilbertXI25WidthTrackedPairedMultipleSystems

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
For every pair of selected geometric multiples, comparison is generated
rather than assumed.
-/
theorem comparisonCertificate
    {rho : SP.Plane}
    {F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho}
    {a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25WidthTrackedPairedMultipleSystems
        (Geo := Geo)
        rho F a b)
    (m n : Nat) :
    HilbertXI25ClassComparisonCertificate
      (Geo := Geo)
      (M.left.baseMultiple m)
      (M.right.baseMultiple n)
      (M.left.solidMultiple m)
      (M.right.solidMultiple n) := by

  have hLeft :=
    M.left_spec m

  have hRight :=
    M.right_spec n

  rw [
    hLeft.1,
    hRight.1,
    hLeft.2,
    hRight.2
  ]

  exact
    F.multipleComparisonCertificate
      (Geo := Geo)
      a b m n


/--
A width-tracked pair automatically gives the previously defined paired
positive-multiple system, including its `compare` field.
-/
def toPairedPositiveMultipleSystems
    {rho : SP.Plane}
    {F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho}
    {a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25WidthTrackedPairedMultipleSystems
        (Geo := Geo)
        rho F a b) :
    HilbertXI25PairedPositiveMultipleSystems
      (Geo := Geo)
      (F.baseAt a)
      (F.baseAt b)
      (F.solidAt a)
      (F.solidAt b) where

  left := M.left

  right := M.right

  compare := by
    intro m n
    exact
      M.comparisonCertificate
        (Geo := Geo) m n


/--
Hence the full local V.Def.5 statement for all `m,n` is automatic from
width tracking and the faithful geometric comparison theorem.
-/
theorem localVDef5
    {rho : SP.Plane}
    {F :
      HilbertXI25ComparisonFaithfulFamily
        (Geo := Geo) rho}
    {a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25WidthTrackedPairedMultipleSystems
        (Geo := Geo)
        rho F a b) :
    (M.toPairedPositiveMultipleSystems
        (Geo := Geo)).LocalVDef5
      (Geo := Geo) := by

  exact
    (M.toPairedPositiveMultipleSystems
      (Geo := Geo)).localVDef5_proved
        (Geo := Geo)

end HilbertXI25WidthTrackedPairedMultipleSystems



------------------------------------------------------------------------
-- XI.25: concrete geometric realization of width magnitudes
------------------------------------------------------------------------

/-!
The faithful-family layer above is already noncircular, but its
`baseAt` and `solidAt` values are quotient classes.

The structure below isolates the remaining genuinely geometric content
of XI.25.  A width is realized by:

* one concrete parallelogram face;
* one concrete parallelepiped;
* the face is exactly the `rho0` face of that parallelepiped;
* the canonical longitudinal edge of the face represents the prescribed
  width class;
* every strict width comparison is witnessed by one actual ordered
  parallel cut which simultaneously makes the smaller base and smaller
  solid proper parts of the larger ones.

Thus `width < width'` is not used to DEFINE base or solid comparison.
It must be realized by an explicit `HilbertXI25SolidCutWitness`.
-/

/--
Concrete realization of all positive widths in one fixed XI.25 carrier
plane.
-/
structure HilbertXI25WidthRealization
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    (rho : SP.Plane) where

  baseRep :
    HilbertXI25WidthClass
        (Geo := Geo) rho ->
      HilbertParallelogramFace Geo

  solidRep :
    HilbertXI25WidthClass
        (Geo := Geo) rho ->
      HilbertXI25Parallelepiped Geo

  solid_rho0 :
    forall x :
      HilbertXI25WidthClass
        (Geo := Geo) rho,
      (solidRep x).rho0 = baseRep x

  base_b_on :
    forall x :
      HilbertXI25WidthClass
        (Geo := Geo) rho,
      SP.OnPlane (baseRep x).b rho

  base_c_on :
    forall x :
      HilbertXI25WidthClass
        (Geo := Geo) rho,
      SP.OnPlane (baseRep x).c rho

  width_spec :
    forall x :
      HilbertXI25WidthClass
        (Geo := Geo) rho,
      hilbert_XI25_widthClass
          (Geo := Geo)
          rho
          (baseRep x).b
          (baseRep x).c
          (base_b_on x)
          (base_c_on x)
          (hilbert_XI25_base_width_ne
            (Geo := Geo)
            (baseRep x))
        =
      x

  cut_of_less :
    forall
      (x y :
        HilbertXI25WidthClass
          (Geo := Geo) rho),
      HilbertPositiveSegmentLess
          (PlaneGeo Geo rho) x y ->
        HilbertXI25AlignedProperPartWitness
          (Geo := Geo)
          (baseRep x)
          (solidRep x)
          (baseRep y)
          (solidRep y)


namespace HilbertXI25WidthRealization

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
Concrete realized base magnitude class.
-/
def baseAt
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25BaseClass Geo :=

  hilbertXI25BaseClassOf
    (Geo := Geo)
    (R.baseRep x)


/--
Concrete realized solid magnitude class.
-/
def solidAt
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25SolidClass Geo :=

  hilbertXI25SolidClassOf
    (Geo := Geo)
    (R.solidRep x)


/--
The concrete realization determines a genuine noncircular faithful
family.
-/
def toComparisonFaithfulFamily
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho) :
    HilbertXI25ComparisonFaithfulFamily
      (Geo := Geo) rho where

  baseAt :=
    R.baseAt
      (Geo := Geo)

  solidAt :=
    R.solidAt
      (Geo := Geo)

  less_transfer := by
    intro x y hxy

    have hCut :=
      R.cut_of_less x y hxy

    have hBase :
        HilbertXI25BaseLess
          (Geo := Geo)
          (R.baseRep x)
          (R.baseRep y) :=
      HilbertXI25AlignedProperPartWitness.baseLess
        (Geo := Geo)
        hCut

    have hSolid :
        HilbertXI25SolidLess
          (Geo := Geo)
          (R.solidRep x)
          (R.solidRep y) :=
      HilbertXI25AlignedProperPartWitness.solidLess
        (Geo := Geo)
        hCut

    exact
      And.intro
        ((hilbertXI25BaseClassOf_less_iff
            (Geo := Geo)
            (R.baseRep x)
            (R.baseRep y)).2
          hBase)
        ((hilbertXI25SolidClassOf_less_iff
            (Geo := Geo)
            (R.solidRep x)
            (R.solidRep y)).2
          hSolid)


/--
The faithful-family base map is definitionally the quotient class of
the concrete realized base.
-/
theorem faithful_baseAt
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    (R.toComparisonFaithfulFamily
        (Geo := Geo)).baseAt x
      =
    hilbertXI25BaseClassOf
      (Geo := Geo)
      (R.baseRep x) := by

  rfl


/--
The faithful-family solid map is definitionally the quotient class of
the concrete realized solid.
-/
theorem faithful_solidAt
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    (R.toComparisonFaithfulFamily
        (Geo := Geo)).solidAt x
      =
    hilbertXI25SolidClassOf
      (Geo := Geo)
      (R.solidRep x) := by

  rfl


/--
The concrete base representative carries exactly the width used to
index it.
-/
theorem realized_width
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    hilbert_XI25_widthClass
        (Geo := Geo)
        rho
        (R.baseRep x).b
        (R.baseRep x).c
        (R.base_b_on x)
        (R.base_c_on x)
        (hilbert_XI25_base_width_ne
          (Geo := Geo)
          (R.baseRep x))
      =
    x := by

  exact R.width_spec x


/--
The represented base really is the distinguished `rho0` face of the
represented solid.
-/
theorem realized_base_is_solid_rho0
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    (R.solidRep x).rho0 =
      R.baseRep x := by

  exact R.solid_rho0 x


/--
Every strict width comparison yields genuine strict comparison of the
realized base classes.
-/
theorem base_less_of_width_less
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    {x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo rho) x y) :
    HilbertXI25BaseClassLess
      (Geo := Geo)
      (R.baseAt (Geo := Geo) x)
      (R.baseAt (Geo := Geo) y) := by

  exact
    ((R.toComparisonFaithfulFamily
        (Geo := Geo)).less_transfer
      x y hxy).1


/--
Every strict width comparison yields genuine strict comparison of the
realized solid classes.
-/
theorem solid_less_of_width_less
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    {x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo rho) x y) :
    HilbertXI25SolidClassLess
      (Geo := Geo)
      (R.solidAt (Geo := Geo) x)
      (R.solidAt (Geo := Geo) y) := by

  exact
    ((R.toComparisonFaithfulFamily
        (Geo := Geo)).less_transfer
      x y hxy).2


/--
Consequently strict comparison of realized bases is equivalent to
strict width comparison.
-/
theorem base_less_iff_width_less
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25BaseClassLess
        (Geo := Geo)
        (R.baseAt (Geo := Geo) x)
        (R.baseAt (Geo := Geo) y)
      <->
    HilbertPositiveSegmentLess
      (PlaneGeo Geo rho) x y := by

  exact
    (R.toComparisonFaithfulFamily
      (Geo := Geo)).base_less_iff_width_less
        (Geo := Geo) x y


/--
Consequently strict comparison of realized solids is equivalent to
strict width comparison.
-/
theorem solid_less_iff_width_less
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25SolidClassLess
        (Geo := Geo)
        (R.solidAt (Geo := Geo) x)
        (R.solidAt (Geo := Geo) y)
      <->
    HilbertPositiveSegmentLess
      (PlaneGeo Geo rho) x y := by

  exact
    (R.toComparisonFaithfulFamily
      (Geo := Geo)).solid_less_iff_width_less
        (Geo := Geo) x y


/--
The comparison of two realized widths is therefore synchronized for
bases and solids.
-/
theorem comparisonCertificate
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertXI25ClassComparisonCertificate
      (Geo := Geo)
      (R.baseAt (Geo := Geo) x)
      (R.baseAt (Geo := Geo) y)
      (R.solidAt (Geo := Geo) x)
      (R.solidAt (Geo := Geo) y) := by

  exact
    (R.toComparisonFaithfulFamily
      (Geo := Geo)).comparisonCertificate
        (Geo := Geo) x y


/--
The realized base and solid magnitudes satisfy the Eudoxus conclusion
for every pair of realized widths.
-/
theorem eudoxusProportion
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    EudoxusProportionBetween
      ((R.toComparisonFaithfulFamily
          (Geo := Geo)).baseEudoxusMagnitude
        (Geo := Geo))
      ((R.toComparisonFaithfulFamily
          (Geo := Geo)).solidEudoxusMagnitude
        (Geo := Geo))
      a b a b := by

  exact
    (R.toComparisonFaithfulFamily
      (Geo := Geo)).eudoxusProportion
        (Geo := Geo) a b

end HilbertXI25WidthRealization


------------------------------------------------------------------------
-- XI.25: realized repeated positive multiples
------------------------------------------------------------------------

/-!
A concrete width realization by itself supplies all magnitude
comparisons.  Euclid's proof also constructs the positive multiples as
actual chains of adjacent slabs.

The next structure records that the already-defined geometric
`HilbertXI25PositiveMultipleSystem` follows exactly the positive width
multiples under one concrete realization.
-/

/--
One geometrically repeated positive-multiple system tracked by a
concrete width realization.
-/
structure HilbertXI25RealizedPositiveMultipleSystem
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (unit :
      HilbertXI25WidthClass
        (Geo := Geo) rho) where

  system :
    HilbertXI25PositiveMultipleSystem
      (Geo := Geo)
      (R.baseAt (Geo := Geo) unit)
      (R.solidAt (Geo := Geo) unit)

  spec :
    forall n : Nat,
      system.baseMultiple n =
        R.baseAt
          (Geo := Geo)
          (hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho) n unit)
      /\
      system.solidMultiple n =
        R.solidAt
          (Geo := Geo)
          (hilbertPositiveSegmentMultiple
            (PlaneGeo Geo rho) n unit)


namespace HilbertXI25RealizedPositiveMultipleSystem

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
Index zero is the concrete unit magnitude.
-/
theorem zero_spec
    {rho : SP.Plane}
    {R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho}
    {unit :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25RealizedPositiveMultipleSystem
        (Geo := Geo) R unit) :
    M.system.baseMultiple 0 =
      R.baseAt (Geo := Geo) unit
    /\
    M.system.solidMultiple 0 =
      R.solidAt (Geo := Geo) unit := by

  simpa only [
    hilbertPositiveSegmentMultiple_zero
  ] using M.spec 0


/--
Every selected multiple is also a recursive repeated-slab multiple.
-/
theorem repeated
    {rho : SP.Plane}
    {R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho}
    {unit :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25RealizedPositiveMultipleSystem
        (Geo := Geo) R unit)
    (n : Nat) :
    HilbertXI25RepeatedSlabMultiple
      (Geo := Geo)
      (R.baseAt (Geo := Geo) unit)
      (R.solidAt (Geo := Geo) unit)
      n
      (M.system.baseMultiple n)
      (M.system.solidMultiple n) := by

  exact
    M.system.repeated
      (Geo := Geo) n

end HilbertXI25RealizedPositiveMultipleSystem


/--
Two concrete repeated systems living in one width realization.
-/
structure HilbertXI25RealizedPairedMultipleSystems
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    [HSE : HilbertSpaceEuclidean Geo]
    {rho : SP.Plane}
    (R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho)
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho) where

  left :
    HilbertXI25RealizedPositiveMultipleSystem
      (Geo := Geo) R a

  right :
    HilbertXI25RealizedPositiveMultipleSystem
      (Geo := Geo) R b


namespace HilbertXI25RealizedPairedMultipleSystems

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
A concrete realized pair gives the width-tracked paired system from the
previous layer.
-/
def toWidthTrackedPairedMultipleSystems
    {rho : SP.Plane}
    {R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho}
    {a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25RealizedPairedMultipleSystems
        (Geo := Geo) R a b) :
    HilbertXI25WidthTrackedPairedMultipleSystems
      (Geo := Geo)
      rho
      (R.toComparisonFaithfulFamily
        (Geo := Geo))
      a b where

  left :=
    M.left.system

  right :=
    M.right.system

  left_spec :=
    M.left.spec

  right_spec :=
    M.right.spec


/--
Therefore all pairwise multiple comparisons are generated by the
concrete width realization.
-/
theorem comparisonCertificate
    {rho : SP.Plane}
    {R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho}
    {a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25RealizedPairedMultipleSystems
        (Geo := Geo) R a b)
    (m n : Nat) :
    HilbertXI25ClassComparisonCertificate
      (Geo := Geo)
      (M.left.system.baseMultiple m)
      (M.right.system.baseMultiple n)
      (M.left.system.solidMultiple m)
      (M.right.system.solidMultiple n) := by

  exact
    (M.toWidthTrackedPairedMultipleSystems
      (Geo := Geo)).comparisonCertificate
        (Geo := Geo) m n


/--
And hence the full local V.Def.5 comparison statement holds for the
two concrete repeated-slab systems.
-/
theorem localVDef5
    {rho : SP.Plane}
    {R :
      HilbertXI25WidthRealization
        (Geo := Geo) rho}
    {a b :
      HilbertXI25WidthClass
        (Geo := Geo) rho}
    (M :
      HilbertXI25RealizedPairedMultipleSystems
        (Geo := Geo) R a b) :
    (M.toWidthTrackedPairedMultipleSystems
        (Geo := Geo)).toPairedPositiveMultipleSystems
          (Geo := Geo)
          |>.LocalVDef5
            (Geo := Geo) := by

  exact
    (M.toWidthTrackedPairedMultipleSystems
      (Geo := Geo)).localVDef5
        (Geo := Geo)

end HilbertXI25RealizedPairedMultipleSystems



------------------------------------------------------------------------
-- Positive segment classes: canonical realization on one fixed ray
------------------------------------------------------------------------

/-!
A quotient class of positive segments is convenient for Book V, but the
remaining geometry of XI.25 needs actual ordered points.

Fix a nondegenerate ray `OR`.  Every positive segment class can be laid
off on this ray by Hilbert III.1 / Book Zero #49.  We choose one such
point once and for all.

Because layoff on a fixed ray is unique, this gives a canonical
geometric representative of every positive segment class.  More
importantly, Book Zero #51 converts strict comparison of the radial
segment classes into actual betweenness of the chosen endpoints.

No numerical length is introduced.
-/

/--
Data realizing one positive segment class on a prescribed ray.
-/
structure HilbertPositiveSegmentRayPointData
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) where

  point : Geo.Point

  sameRay :
    HilbertSameRay Geo O R point

  ne_origin :
    Ne O point

  class_eq :
    hilbertPositiveSegmentClassOf
        Geo O point ne_origin
      =
    x


/--
Every positive segment class has a representative on any prescribed
nondegenerate ray.
-/
theorem hilbertPositiveSegmentRayPointData_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) :
    Nonempty
      (HilbertPositiveSegmentRayPointData
        (Geo := Geo)
        O R hOR x) := by

  refine Quotient.inductionOn x ?_

  intro s

  rcases
      bookZero_49_layoff
        Geo
        O R
        s.val.1 s.val.2
        hOR
        s.property
    with
    ⟨P, hRayP, hOP_s⟩

  have hOP : Ne O P :=
    hRayP.2.1.symm

  refine
    ⟨{
      point := P
      sameRay := hRayP
      ne_origin := hOP
      class_eq := ?_
    }⟩

  exact
    Quotient.sound hOP_s


/--
Chosen realization data for a positive segment class on a fixed ray.
-/
noncomputable def hilbertPositiveSegmentRayPointData
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentRayPointData
      (Geo := Geo)
      O R hOR x :=

  Classical.choice
    (hilbertPositiveSegmentRayPointData_exists
      (Geo := Geo)
      O R hOR x)


/--
Canonical point realizing a positive segment class on the prescribed
ray.
-/
noncomputable def hilbertPositiveSegmentPointOnRay
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) :
    Geo.Point :=

  (hilbertPositiveSegmentRayPointData
    (Geo := Geo)
    O R hOR x).point


/--
The canonical realization lies on the prescribed ray.
-/
theorem hilbertPositiveSegmentPointOnRay_sameRay
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) :
    HilbertSameRay
      Geo
      O R
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR x) := by

  exact
    (hilbertPositiveSegmentRayPointData
      (Geo := Geo)
      O R hOR x).sameRay


/--
The origin and the canonical positive endpoint are distinct.
-/
theorem hilbertPositiveSegmentPointOnRay_ne
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) :
    Ne
      O
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR x) := by

  exact
    (hilbertPositiveSegmentRayPointData
      (Geo := Geo)
      O R hOR x).ne_origin


/--
The radial segment from the origin to the chosen endpoint represents
exactly the original positive segment class.
-/
theorem hilbertPositiveSegmentPointOnRay_class
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentClassOf
        Geo
        O
        (hilbertPositiveSegmentPointOnRay
          (Geo := Geo)
          O R hOR x)
        (hilbertPositiveSegmentPointOnRay_ne
          (Geo := Geo)
          O R hOR x)
      =
    x := by

  exact
    (hilbertPositiveSegmentRayPointData
      (Geo := Geo)
      O R hOR x).class_eq


/--
The canonical endpoint map on a fixed ray is injective.
-/
theorem hilbertPositiveSegmentPointOnRay_injective
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R) :
    Function.Injective
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR) := by

  intro x y hPoint

  have hx :=
    hilbertPositiveSegmentPointOnRay_class
      (Geo := Geo)
      O R hOR x

  have hy :=
    hilbertPositiveSegmentPointOnRay_class
      (Geo := Geo)
      O R hOR y

  have hCong :
      Geo.Congruent
        O
        (hilbertPositiveSegmentPointOnRay
          (Geo := Geo)
          O R hOR x)
        O
        (hilbertPositiveSegmentPointOnRay
          (Geo := Geo)
          O R hOR y) := by

    rw [hPoint]

    exact
      hilbert_congruent_reflexive
        Geo
        O
        (hilbertPositiveSegmentPointOnRay
          (Geo := Geo)
          O R hOR y)

  have hRadial :
      hilbertPositiveSegmentClassOf
          Geo
          O
          (hilbertPositiveSegmentPointOnRay
            (Geo := Geo)
            O R hOR x)
          (hilbertPositiveSegmentPointOnRay_ne
            (Geo := Geo)
            O R hOR x)
        =
      hilbertPositiveSegmentClassOf
          Geo
          O
          (hilbertPositiveSegmentPointOnRay
            (Geo := Geo)
            O R hOR y)
          (hilbertPositiveSegmentPointOnRay_ne
            (Geo := Geo)
            O R hOR y) := by

    exact
      Quotient.sound hCong

  calc
    x =
        hilbertPositiveSegmentClassOf
          Geo
          O
          (hilbertPositiveSegmentPointOnRay
            (Geo := Geo)
            O R hOR x)
          (hilbertPositiveSegmentPointOnRay_ne
            (Geo := Geo)
            O R hOR x) := hx.symm

    _ =
        hilbertPositiveSegmentClassOf
          Geo
          O
          (hilbertPositiveSegmentPointOnRay
            (Geo := Geo)
            O R hOR y)
          (hilbertPositiveSegmentPointOnRay_ne
            (Geo := Geo)
            O R hOR y) := hRadial

    _ = y := hy


/--
Strict comparison of positive segment classes becomes strict
betweenness of their canonical endpoints on the common ray.
-/
theorem hilbertPositiveSegmentPointOnRay_between_of_less
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x y : HilbertPositiveSegmentClass Geo)
    (hxy :
      HilbertPositiveSegmentLess Geo x y) :
    Geo.Between
      O
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR x)
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR y) := by

  let X :=
    hilbertPositiveSegmentPointOnRay
      (Geo := Geo)
      O R hOR x

  let Y :=
    hilbertPositiveSegmentPointOnRay
      (Geo := Geo)
      O R hOR y

  have hOX : Ne O X := by
    simpa [X] using
      hilbertPositiveSegmentPointOnRay_ne
        (Geo := Geo)
        O R hOR x

  have hOY : Ne O Y := by
    simpa [Y] using
      hilbertPositiveSegmentPointOnRay_ne
        (Geo := Geo)
        O R hOR y

  have hClassX :
      hilbertPositiveSegmentClassOf
          Geo O X hOX
        =
      x := by

    simpa [X] using
      hilbertPositiveSegmentPointOnRay_class
        (Geo := Geo)
        O R hOR x

  have hClassY :
      hilbertPositiveSegmentClassOf
          Geo O Y hOY
        =
      y := by

    simpa [Y] using
      hilbertPositiveSegmentPointOnRay_class
        (Geo := Geo)
        O R hOR y

  have hClassLess :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf
          Geo O X hOX)
        (hilbertPositiveSegmentClassOf
          Geo O Y hOY) := by

    rw [hClassX, hClassY]
    exact hxy

  have hSegmentLess :
      HilbertSegmentLess
        Geo
        O X
        O Y :=
    (hilbertPositiveSegmentClassOf_less_iff
      Geo
      O X
      O Y
      hOX hOY).1
      hClassLess

  have hRayX :
      HilbertSameRay Geo O R X := by
    simpa [X] using
      hilbertPositiveSegmentPointOnRay_sameRay
        (Geo := Geo)
        O R hOR x

  have hRayY :
      HilbertSameRay Geo O R Y := by
    simpa [Y] using
      hilbertPositiveSegmentPointOnRay_sameRay
        (Geo := Geo)
        O R hOR y

  have hRayXY :
      HilbertSameRay Geo O X Y :=
    hilbert_sameRay_common_reference
      Geo
      O R X Y
      hRayX hRayY

  have hOXY :
      Geo.Between O X Y :=
    bookZero_51_lessThanBetween
      Geo
      O X Y
      hSegmentLess
      hRayXY

  simpa [X, Y] using hOXY


/--
Conversely, strict betweenness of canonical radial endpoints implies
strict comparison of their positive segment classes.
-/
theorem hilbertPositiveSegmentPointOnRay_less_of_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x y : HilbertPositiveSegmentClass Geo)
    (hBetween :
      Geo.Between
        O
        (hilbertPositiveSegmentPointOnRay
          (Geo := Geo)
          O R hOR x)
        (hilbertPositiveSegmentPointOnRay
          (Geo := Geo)
          O R hOR y)) :
    HilbertPositiveSegmentLess Geo x y := by

  let X :=
    hilbertPositiveSegmentPointOnRay
      (Geo := Geo)
      O R hOR x

  let Y :=
    hilbertPositiveSegmentPointOnRay
      (Geo := Geo)
      O R hOR y

  have hOX : Ne O X := by
    simpa [X] using
      hilbertPositiveSegmentPointOnRay_ne
        (Geo := Geo)
        O R hOR x

  have hOY : Ne O Y := by
    simpa [Y] using
      hilbertPositiveSegmentPointOnRay_ne
        (Geo := Geo)
        O R hOR y

  have hOXY :
      Geo.Between O X Y := by
    simpa [X, Y] using hBetween

  have hSegmentLess :
      HilbertSegmentLess
        Geo
        O X
        O Y :=
    hilbert_segmentLess_of_between
      Geo
      O X Y
      hOXY

  have hClassLess :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf
          Geo O X hOX)
        (hilbertPositiveSegmentClassOf
          Geo O Y hOY) :=
    (hilbertPositiveSegmentClassOf_less_iff
      Geo
      O X
      O Y
      hOX hOY).2
      hSegmentLess

  have hClassX :
      hilbertPositiveSegmentClassOf
          Geo O X hOX
        =
      x := by

    simpa [X] using
      hilbertPositiveSegmentPointOnRay_class
        (Geo := Geo)
        O R hOR x

  have hClassY :
      hilbertPositiveSegmentClassOf
          Geo O Y hOY
        =
      y := by

    simpa [Y] using
      hilbertPositiveSegmentPointOnRay_class
        (Geo := Geo)
        O R hOR y

  rw [hClassX, hClassY] at hClassLess

  exact hClassLess


/--
On one normalized ray, positive-segment strict order is exactly radial
betweenness.
-/
theorem hilbertPositiveSegmentPointOnRay_less_iff_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R : Geo.Point)
    (hOR : Ne O R)
    (x y : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess Geo x y
      <->
    Geo.Between
      O
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR x)
      (hilbertPositiveSegmentPointOnRay
        (Geo := Geo)
        O R hOR y) := by

  constructor

  · exact
      hilbertPositiveSegmentPointOnRay_between_of_less
        (Geo := Geo)
        O R hOR x y

  · exact
      hilbertPositiveSegmentPointOnRay_less_of_between
        (Geo := Geo)
        O R hOR x y


------------------------------------------------------------------------
-- XI.25 specialization: width classes on one carrier-plane ray
------------------------------------------------------------------------

/--
Canonical endpoint of an XI.25 width class on a fixed ray in `rho`.
-/
noncomputable def hilbert_XI25_widthPoint
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    PlanePoint Geo rho :=

  hilbertPositiveSegmentPointOnRay
    (Geo := PlaneGeo Geo rho)
    O R hOR x


/--
The normalized XI.25 width endpoint lies on the prescribed plane ray.
-/
theorem hilbert_XI25_widthPoint_sameRay
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertSameRay
      (PlaneGeo Geo rho)
      O R
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR x) := by

  exact
    hilbertPositiveSegmentPointOnRay_sameRay
      (Geo := PlaneGeo Geo rho)
      O R hOR x


/--
The normalized XI.25 width endpoint is distinct from the origin.
-/
theorem hilbert_XI25_widthPoint_ne
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    Ne
      O
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR x) := by

  exact
    hilbertPositiveSegmentPointOnRay_ne
      (Geo := PlaneGeo Geo rho)
      O R hOR x


/--
The radial segment to the normalized point represents exactly the
specified XI.25 width class.
-/
theorem hilbert_XI25_widthPoint_class
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    hilbertPositiveSegmentClassOf
        (PlaneGeo Geo rho)
        O
        (hilbert_XI25_widthPoint
          (Geo := Geo)
          rho O R hOR x)
        (hilbert_XI25_widthPoint_ne
          (Geo := Geo)
          rho O R hOR x)
      =
    x := by

  exact
    hilbertPositiveSegmentPointOnRay_class
      (Geo := PlaneGeo Geo rho)
      O R hOR x


/--
Strict width comparison is actual strict betweenness on the normalized
carrier-plane ray.
-/
theorem hilbert_XI25_widthPoint_between_of_less
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo rho) x y) :
    (PlaneGeo Geo rho).Between
      O
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR x)
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR y) := by

  exact
    hilbertPositiveSegmentPointOnRay_between_of_less
      (Geo := PlaneGeo Geo rho)
      O R hOR x y hxy


/--
The same strict width comparison viewed as ambient spatial
betweenness.
-/
theorem hilbert_XI25_widthPoint_between_of_less_ambient
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo rho) x y) :
    Geo.Between
      O.val
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR x).val
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR y).val := by

  have hPlane :
      (PlaneGeo Geo rho).Between
        O
        (hilbert_XI25_widthPoint
          (Geo := Geo)
          rho O R hOR x)
        (hilbert_XI25_widthPoint
          (Geo := Geo)
          rho O R hOR y) :=
    hilbert_XI25_widthPoint_between_of_less
      (Geo := Geo)
      rho O R hOR x y hxy

  exact
    (planeGeo_between
      (Geo := Geo)
      rho
      O
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR x)
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR y)).mp
      hPlane


/--
The normalized width endpoint map is injective.
-/
theorem hilbert_XI25_widthPoint_injective
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R) :
    Function.Injective
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR) := by

  exact
    hilbertPositiveSegmentPointOnRay_injective
      (Geo := PlaneGeo Geo rho)
      O R hOR


/--
For normalized XI.25 width endpoints, width order and plane
betweenness are equivalent.
-/
theorem hilbert_XI25_widthPoint_less_iff_between
    [H : HilbertIncidence Geo]
    [HilbertOrder Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (rho : SP.Plane)
    (O R : PlanePoint Geo rho)
    (hOR : Ne O R)
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) rho) :
    HilbertPositiveSegmentLess
        (PlaneGeo Geo rho) x y
      <->
    (PlaneGeo Geo rho).Between
      O
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR x)
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        rho O R hOR y) := by

  exact
    hilbertPositiveSegmentPointOnRay_less_iff_between
      (Geo := PlaneGeo Geo rho)
      O R hOR x y



------------------------------------------------------------------------
-- XI.25: synchronized realization on the four longitudinal edges
------------------------------------------------------------------------

/-!
The width normalization above lives on one chosen ray in `rho0`.
For XI.25 we need the same positive width on all four longitudinal
edges of one seed parallelepiped.

Starting from one nontrivial solid-cut witness `X`, we use the first
edge intervals

  A0--A1, B0--B1, C0--C1, D0--D1

as four reference rays.

For a width class `x` in `PlaneGeo rho0`:

* `B(x)` is the canonical normalized endpoint on ray `B0 B1`;
* `A(x), C(x), D(x)` are obtained by spatial segment construction,
  laying off a segment congruent to `B0 B(x)` on the corresponding
  three rays.

Thus all four radial segments have the same spatial length.

The key payoff is order synchronization.  If `x < y`, then Book Zero
normalization gives `B0-B(x)-B(y)`.  The spatial layoff-shorter lemma
then transports that order to the other three rays:

  A0-A(x)-A(y),
  C0-C(x)-C(y),
  D0-D(x)-D(y).

This is the precise four-edge order data required by
`HilbertXI25OrderedTwoSlabConfiguration`.
-/

/--
Generic spatial layoff data: copy segment `AB` onto ray `OR`.
-/
structure HilbertXI25SpaceLayoffData
    [H : HilbertIncidence Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B O R : Geo.Point)
    (hOR : Ne O R) where

  point : Geo.Point

  sameRay :
    HilbertSameRay Geo O R point

  congruent :
    Geo.Congruent O point A B


/--
Spatial layoff data exist by Hilbert III.1.
-/
theorem hilbert_XI25_spaceLayoffData_exists
    [H : HilbertIncidence Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B O R : Geo.Point)
    (hOR : Ne O R) :
    Nonempty
      (HilbertXI25SpaceLayoffData
        (Geo := Geo)
        A B O R hOR) := by

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        A B O R hOR
    with
    ⟨P, hRay, hCong⟩

  exact
    ⟨{
      point := P
      sameRay := hRay
      congruent := hCong
    }⟩


/--
Chosen spatial layoff data.
-/
noncomputable def hilbert_XI25_spaceLayoffData
    [H : HilbertIncidence Geo]
    [SP : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := SP)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := SP)]
    (A B O R : Geo.Point)
    (hOR : Ne O R) :
    HilbertXI25SpaceLayoffData
      (Geo := Geo)
      A B O R hOR :=

  Classical.choice
    (hilbert_XI25_spaceLayoffData_exists
      (Geo := Geo)
      A B O R hOR)


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


/--
`B0` as a point of the fixed carrier plane `rho0`.
-/
def B0rho
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    PlanePoint Geo X.rho0 :=

  ⟨X.B0, X.ordered.slab.B0_on.2.1⟩


/--
`B1` as a point of the fixed carrier plane `rho0`.
-/
def B1rho
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    PlanePoint Geo X.rho0 :=

  ⟨X.B1, X.ordered.slab.B1_on.2.1⟩


omit [HilbertOrder Geo] HSC in
/--
The reference ray `B0 B1` is nondegenerate in `PlaneGeo rho0`.
-/
theorem B0rho_ne_B1rho
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    Ne
      (X.B0rho (Geo := Geo))
      (X.B1rho (Geo := Geo)) := by

  intro hEq

  exact
    X.nonempty_B.1
      (congrArg Subtype.val hEq)


/--
Canonical endpoint representing width `x` on the longitudinal B-edge.
-/
noncomputable def widthPointB
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Point :=

  (hilbert_XI25_widthPoint
    (Geo := Geo)
    X.rho0
    (X.B0rho (Geo := Geo))
    (X.B1rho (Geo := Geo))
    (X.B0rho_ne_B1rho (Geo := Geo))
    x).val


/--
The normalized B-endpoint lies on the ambient ray `B0 B1`.
-/
theorem widthPointB_sameRay
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSameRay
      Geo X.B0 X.B1
      (X.widthPointB (Geo := Geo) x) := by

  let B0p :=
    X.B0rho (Geo := Geo)

  let B1p :=
    X.B1rho (Geo := Geo)

  let Bxp :=
    hilbert_XI25_widthPoint
      (Geo := Geo)
      X.rho0
      B0p B1p
      (X.B0rho_ne_B1rho
        (Geo := Geo))
      x

  have hPlane :
      HilbertSameRay
        (PlaneGeo Geo X.rho0)
        B0p B1p Bxp := by

    exact
      hilbert_XI25_widthPoint_sameRay
        (Geo := Geo)
        X.rho0
        B0p B1p
        (X.B0rho_ne_B1rho
          (Geo := Geo))
        x

  have hAmbient :=
    (planeGeo_sameRay_iff_ambient
      (Geo := Geo)
      X.rho0
      B0p B1p Bxp).mp
      hPlane

  simpa
    [B0p, B1p, Bxp,
     B0rho, B1rho, widthPointB]
    using hAmbient


/--
The normalized B-endpoint is different from `B0`.
-/
theorem widthPointB_ne_origin
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Ne X.B0
      (X.widthPointB (Geo := Geo) x) := by

  exact
    (X.widthPointB_sameRay
      (Geo := Geo) x).2.1.symm


/--
The normalized B-endpoint lies in `rho0`.
-/
theorem widthPointB_on_rho0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointB (Geo := Geo) x)
      X.rho0 := by

  change
    SP.OnPlane
      (hilbert_XI25_widthPoint
        (Geo := Geo)
        X.rho0
        (X.B0rho (Geo := Geo))
        (X.B1rho (Geo := Geo))
        (X.B0rho_ne_B1rho
          (Geo := Geo))
        x).val
      X.rho0

  exact
    (hilbert_XI25_widthPoint
      (Geo := Geo)
      X.rho0
      (X.B0rho (Geo := Geo))
      (X.B1rho (Geo := Geo))
      (X.B0rho_ne_B1rho
        (Geo := Geo))
      x).property


/--
The normalized B-endpoint also lies in `sigma0`, hence on the actual
longitudinal B-edge.
-/
theorem widthPointB_on_sigma0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointB (Geo := Geo) x)
      X.sigma0 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.sigma0
      X.B0 X.B1
      (X.widthPointB (Geo := Geo) x)
      X.nonempty_B.1
      X.ordered.slab.B0_on.2.2
      X.ordered.slab.B1_on.2.2
      (X.widthPointB_sameRay
        (Geo := Geo) x).2.2.1


/--
Chosen layoff of the B-width onto the A-edge.
-/
noncomputable def widthDataA
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertXI25SpaceLayoffData
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      X.A0 X.A1
      X.nonempty_A.1 :=

  hilbert_XI25_spaceLayoffData
    (Geo := Geo)
    X.B0
    (X.widthPointB (Geo := Geo) x)
    X.A0 X.A1
    X.nonempty_A.1


/--
Chosen layoff of the B-width onto the C-edge.
-/
noncomputable def widthDataC
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertXI25SpaceLayoffData
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      X.C0 X.C1
      X.nonempty_C.1 :=

  hilbert_XI25_spaceLayoffData
    (Geo := Geo)
    X.B0
    (X.widthPointB (Geo := Geo) x)
    X.C0 X.C1
    X.nonempty_C.1


/--
Chosen layoff of the B-width onto the D-edge.
-/
noncomputable def widthDataD
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertXI25SpaceLayoffData
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      X.D0 X.D1
      X.nonempty_D.1 :=

  hilbert_XI25_spaceLayoffData
    (Geo := Geo)
    X.B0
    (X.widthPointB (Geo := Geo) x)
    X.D0 X.D1
    X.nonempty_D.1


/--
Synchronized endpoint on the A-edge.
-/
noncomputable def widthPointA
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Point :=

  (X.widthDataA (Geo := Geo) x).point


/--
Synchronized endpoint on the C-edge.
-/
noncomputable def widthPointC
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Point :=

  (X.widthDataC (Geo := Geo) x).point


/--
Synchronized endpoint on the D-edge.
-/
noncomputable def widthPointD
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Point :=

  (X.widthDataD (Geo := Geo) x).point


/--
A-width is laid off on ray `A0 A1`.
-/
theorem widthPointA_sameRay
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSameRay
      Geo X.A0 X.A1
      (X.widthPointA (Geo := Geo) x) :=

  (X.widthDataA
    (Geo := Geo) x).sameRay


/--
C-width is laid off on ray `C0 C1`.
-/
theorem widthPointC_sameRay
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSameRay
      Geo X.C0 X.C1
      (X.widthPointC (Geo := Geo) x) :=

  (X.widthDataC
    (Geo := Geo) x).sameRay


/--
D-width is laid off on ray `D0 D1`.
-/
theorem widthPointD_sameRay
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSameRay
      Geo X.D0 X.D1
      (X.widthPointD (Geo := Geo) x) :=

  (X.widthDataD
    (Geo := Geo) x).sameRay


/--
The A radial segment is congruent to the master B radial segment.
-/
theorem widthPointA_congruent_B
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Congruent
      X.A0
      (X.widthPointA (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x) :=

  (X.widthDataA
    (Geo := Geo) x).congruent


/--
The C radial segment is congruent to the master B radial segment.
-/
theorem widthPointC_congruent_B
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Congruent
      X.C0
      (X.widthPointC (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x) :=

  (X.widthDataC
    (Geo := Geo) x).congruent


/--
The D radial segment is congruent to the master B radial segment.
-/
theorem widthPointD_congruent_B
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Geo.Congruent
      X.D0
      (X.widthPointD (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x) :=

  (X.widthDataD
    (Geo := Geo) x).congruent


/--
A-endpoint lies in side plane `rho0`.
-/
theorem widthPointA_on_rho0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointA (Geo := Geo) x)
      X.rho0 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.rho0
      X.A0 X.A1
      (X.widthPointA (Geo := Geo) x)
      X.nonempty_A.1
      X.ordered.slab.A0_on.2.1
      X.ordered.slab.A1_on.2.1
      (X.widthPointA_sameRay
        (Geo := Geo) x).2.2.1


/--
A-endpoint lies in side plane `sigma1`.
-/
theorem widthPointA_on_sigma1
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointA (Geo := Geo) x)
      X.sigma1 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.sigma1
      X.A0 X.A1
      (X.widthPointA (Geo := Geo) x)
      X.nonempty_A.1
      X.ordered.slab.A0_on.2.2
      X.ordered.slab.A1_on.2.2
      (X.widthPointA_sameRay
        (Geo := Geo) x).2.2.1


/--
C-endpoint lies in side plane `rho1`.
-/
theorem widthPointC_on_rho1
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointC (Geo := Geo) x)
      X.rho1 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.rho1
      X.C0 X.C1
      (X.widthPointC (Geo := Geo) x)
      X.nonempty_C.1
      X.ordered.slab.C0_on.2.1
      X.ordered.slab.C1_on.2.1
      (X.widthPointC_sameRay
        (Geo := Geo) x).2.2.1


/--
C-endpoint lies in side plane `sigma0`.
-/
theorem widthPointC_on_sigma0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointC (Geo := Geo) x)
      X.sigma0 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.sigma0
      X.C0 X.C1
      (X.widthPointC (Geo := Geo) x)
      X.nonempty_C.1
      X.ordered.slab.C0_on.2.2
      X.ordered.slab.C1_on.2.2
      (X.widthPointC_sameRay
        (Geo := Geo) x).2.2.1


/--
D-endpoint lies in side plane `rho1`.
-/
theorem widthPointD_on_rho1
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointD (Geo := Geo) x)
      X.rho1 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.rho1
      X.D0 X.D1
      (X.widthPointD (Geo := Geo) x)
      X.nonempty_D.1
      X.ordered.slab.D0_on.2.1
      X.ordered.slab.D1_on.2.1
      (X.widthPointD_sameRay
        (Geo := Geo) x).2.2.1


/--
D-endpoint lies in side plane `sigma1`.
-/
theorem widthPointD_on_sigma1
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointD (Geo := Geo) x)
      X.sigma1 := by

  exact
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.sigma1
      X.D0 X.D1
      (X.widthPointD (Geo := Geo) x)
      X.nonempty_D.1
      X.ordered.slab.D0_on.2.2
      X.ordered.slab.D1_on.2.2
      (X.widthPointD_sameRay
        (Geo := Geo) x).2.2.1


/--
Strict width comparison gives the required order on the B-edge.
-/
theorem widthPointB_between
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    Geo.Between
      X.B0
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) y) := by

  have h :=
    hilbert_XI25_widthPoint_between_of_less_ambient
      (Geo := Geo)
      X.rho0
      (X.B0rho (Geo := Geo))
      (X.B1rho (Geo := Geo))
      (X.B0rho_ne_B1rho
        (Geo := Geo))
      x y hxy

  simpa
    [B0rho, B1rho, widthPointB]
    using h


/--
Strict width comparison is transported to the A-edge.
-/
theorem widthPointA_between
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    Geo.Between
      X.A0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointA (Geo := Geo) y) := by

  exact
    hilbert_space_layoff_shorter_between_XI25
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) y)
      X.A0 X.A1
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointA (Geo := Geo) y)
      (X.widthPointB_between
        (Geo := Geo) x y hxy)
      (X.widthPointA_sameRay
        (Geo := Geo) x)
      (X.widthPointA_sameRay
        (Geo := Geo) y)
      (X.widthPointA_congruent_B
        (Geo := Geo) x)
      (X.widthPointA_congruent_B
        (Geo := Geo) y)


/--
Strict width comparison is transported to the C-edge.
-/
theorem widthPointC_between
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    Geo.Between
      X.C0
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) y) := by

  exact
    hilbert_space_layoff_shorter_between_XI25
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) y)
      X.C0 X.C1
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) y)
      (X.widthPointB_between
        (Geo := Geo) x y hxy)
      (X.widthPointC_sameRay
        (Geo := Geo) x)
      (X.widthPointC_sameRay
        (Geo := Geo) y)
      (X.widthPointC_congruent_B
        (Geo := Geo) x)
      (X.widthPointC_congruent_B
        (Geo := Geo) y)


/--
Strict width comparison is transported to the D-edge.
-/
theorem widthPointD_between
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    Geo.Between
      X.D0
      (X.widthPointD (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) y) := by

  exact
    hilbert_space_layoff_shorter_between_XI25
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) y)
      X.D0 X.D1
      (X.widthPointD (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) y)
      (X.widthPointB_between
        (Geo := Geo) x y hxy)
      (X.widthPointD_sameRay
        (Geo := Geo) x)
      (X.widthPointD_sameRay
        (Geo := Geo) y)
      (X.widthPointD_congruent_B
        (Geo := Geo) x)
      (X.widthPointD_congruent_B
        (Geo := Geo) y)


/--
Bundled four-edge order synchronization for two widths.
-/
theorem widthPoints_between_all
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    Geo.Between
        X.A0
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y)
    /\
    Geo.Between
        X.B0
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) y)
    /\
    Geo.Between
        X.C0
        (X.widthPointC (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) y)
    /\
    Geo.Between
        X.D0
        (X.widthPointD (Geo := Geo) x)
        (X.widthPointD (Geo := Geo) y) := by

  exact
    And.intro
      (X.widthPointA_between
        (Geo := Geo) x y hxy)
      (And.intro
        (X.widthPointB_between
          (Geo := Geo) x y hxy)
        (And.intro
          (X.widthPointC_between
            (Geo := Geo) x y hxy)
          (X.widthPointD_between
            (Geo := Geo) x y hxy)))


/--
All four synchronized endpoints remain on the two fixed pairs of side
planes of the seed parallelepiped.
-/
theorem widthPoints_side_incidence
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    (SP.OnPlane
        (X.widthPointA (Geo := Geo) x)
        X.rho0
      /\
     SP.OnPlane
        (X.widthPointA (Geo := Geo) x)
        X.sigma1)
    /\
    (SP.OnPlane
        (X.widthPointB (Geo := Geo) x)
        X.rho0
      /\
     SP.OnPlane
        (X.widthPointB (Geo := Geo) x)
        X.sigma0)
    /\
    (SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        X.rho1
      /\
     SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        X.sigma0)
    /\
    (SP.OnPlane
        (X.widthPointD (Geo := Geo) x)
        X.rho1
      /\
     SP.OnPlane
        (X.widthPointD (Geo := Geo) x)
        X.sigma1) := by

  exact
    And.intro
      (And.intro
        (X.widthPointA_on_rho0
          (Geo := Geo) x)
        (X.widthPointA_on_sigma1
          (Geo := Geo) x))
      (And.intro
        (And.intro
          (X.widthPointB_on_rho0
            (Geo := Geo) x)
          (X.widthPointB_on_sigma0
            (Geo := Geo) x))
        (And.intro
          (And.intro
            (X.widthPointC_on_rho1
              (Geo := Geo) x)
            (X.widthPointC_on_sigma0
              (Geo := Geo) x))
          (And.intro
            (X.widthPointD_on_rho1
              (Geo := Geo) x)
            (X.widthPointD_on_sigma1
              (Geo := Geo) x))))

end HilbertXI25SolidCutWitness



------------------------------------------------------------------------
-- XI.25: the section plane determined by a realized width
------------------------------------------------------------------------

/-!
The synchronized width endpoints constructed above lie on the four
longitudinal edges of the seed parallelepiped.

The next step is to recover the actual cross-section plane attached to
one width class.

The first three endpoints are noncollinear for a purely spatial reason:

* A(x), B(x) lie in `rho0`;
* C(x) lies in the opposite plane `rho1`;
* A(x) and B(x) are distinct because they lie respectively in the
  disjoint side planes `sigma1` and `sigma0`.

Hence if A(x),B(x),C(x) were collinear, line-in-plane closure would put
C(x) in `rho0`, contradicting `rho0 || rho1`.

Hilbert I.4 then produces the unique plane through A(x),B(x),C(x).
This is the canonical candidate `pi(x)` for the XI.25 cross-section.

At this stage we deliberately do not yet assert D(x) lies in `pi(x)`.
That will be the next geometric step, using XI.15 and XI.16 rather than
building coplanarity into the definition.
-/

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


omit HSE in
/--
The synchronized A- and B-endpoints are distinct.

They lie in the opposite side planes `sigma1` and `sigma0`,
respectively.
-/
theorem widthPointA_ne_widthPointB
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Ne
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x) := by

  intro hAB

  apply X.ordered.slab.sigma_parallel

  refine
    ⟨X.widthPointA (Geo := Geo) x,
     ?_,
     ?_⟩

  · rw [hAB]
    exact
      X.widthPointB_on_sigma0
        (Geo := Geo) x

  · exact
      X.widthPointA_on_sigma1
        (Geo := Geo) x


omit HSE in
/--
The first three synchronized width endpoints are noncollinear.
-/
theorem widthPoints_ABC_noncollinear
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Not
      (PrimCollinear
        Geo
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)) := by

  intro hABC

  have hC_rho0 :
      SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        X.rho0 :=

    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      X.rho0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) x)
      (X.widthPointA_on_rho0
        (Geo := Geo) x)
      (X.widthPointB_on_rho0
        (Geo := Geo) x)
      hABC

  apply X.ordered.slab.rho_parallel

  exact
    ⟨X.widthPointC (Geo := Geo) x,
     hC_rho0,
     X.widthPointC_on_rho1
       (Geo := Geo) x⟩


/--
First-class data for the unique plane through the three synchronized
endpoints A(x),B(x),C(x).
-/
structure HilbertXI25WidthSectionPlaneData
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) where

  plane : SP.Plane

  A_on :
    SP.OnPlane
      (X.widthPointA (Geo := Geo) x)
      plane

  B_on :
    SP.OnPlane
      (X.widthPointB (Geo := Geo) x)
      plane

  C_on :
    SP.OnPlane
      (X.widthPointC (Geo := Geo) x)
      plane

  unique :
    forall tau : SP.Plane,
      SP.OnPlane
          (X.widthPointA (Geo := Geo) x)
          tau ->
      SP.OnPlane
          (X.widthPointB (Geo := Geo) x)
          tau ->
      SP.OnPlane
          (X.widthPointC (Geo := Geo) x)
          tau ->
      tau = plane


omit HSE in
/--
The section-plane data exist by Hilbert I.4 and plane uniqueness.
-/
theorem widthSectionPlaneData_exists
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Nonempty
      (HilbertXI25WidthSectionPlaneData
        (Geo := Geo) X x) := by

  have hABC :=
    X.widthPoints_ABC_noncollinear
      (Geo := Geo) x

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        hABC
    with
    ⟨pi, hApi, hBpi, hCpi⟩

  refine
    ⟨{
      plane := pi
      A_on := hApi
      B_on := hBpi
      C_on := hCpi
      unique := ?_
    }⟩

  intro tau hAtau hBtau hCtau

  exact
    HilbertSpaceIncidence.plane_unique
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      hABC
      tau pi
      hAtau hBtau hCtau
      hApi hBpi hCpi


/--
Chosen section-plane data for a width class.
-/
noncomputable def widthSectionPlaneData
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertXI25WidthSectionPlaneData
      (Geo := Geo) X x :=

  Classical.choice
    (X.widthSectionPlaneData_exists
      (Geo := Geo) x)


/--
The canonical candidate cross-section plane attached to width `x`.
-/
noncomputable def widthSectionPlane
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.Plane :=

  (X.widthSectionPlaneData
    (Geo := Geo) x).plane


omit HSE in
/--
A(x) lies in the canonical section plane.
-/
theorem widthPointA_on_sectionPlane
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointA (Geo := Geo) x)
      (X.widthSectionPlane (Geo := Geo) x) :=

  (X.widthSectionPlaneData
    (Geo := Geo) x).A_on


omit HSE in
/--
B(x) lies in the canonical section plane.
-/
theorem widthPointB_on_sectionPlane
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointB (Geo := Geo) x)
      (X.widthSectionPlane (Geo := Geo) x) :=

  (X.widthSectionPlaneData
    (Geo := Geo) x).B_on


omit HSE in
/--
C(x) lies in the canonical section plane.
-/
theorem widthPointC_on_sectionPlane
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointC (Geo := Geo) x)
      (X.widthSectionPlane (Geo := Geo) x) :=

  (X.widthSectionPlaneData
    (Geo := Geo) x).C_on


omit HSE in
/--
The canonical section plane is uniquely determined by A(x),B(x),C(x).
-/
theorem widthSectionPlane_unique
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (tau : SP.Plane)
    (hAtau :
      SP.OnPlane
        (X.widthPointA (Geo := Geo) x)
        tau)
    (hBtau :
      SP.OnPlane
        (X.widthPointB (Geo := Geo) x)
        tau)
    (hCtau :
      SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        tau) :
    tau =
      X.widthSectionPlane (Geo := Geo) x :=

  (X.widthSectionPlaneData
    (Geo := Geo) x).unique
      tau hAtau hBtau hCtau


omit HSE in
/--
The canonical section plane is distinct from `rho0`.
-/
theorem widthSectionPlane_ne_rho0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Ne
      (X.widthSectionPlane (Geo := Geo) x)
      X.rho0 := by

  intro hEq

  have hC_rho0 :
      SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        X.rho0 := by

    rw [← hEq]

    exact
      X.widthPointC_on_sectionPlane
        (Geo := Geo) x

  apply X.ordered.slab.rho_parallel

  exact
    ⟨X.widthPointC (Geo := Geo) x,
     hC_rho0,
     X.widthPointC_on_rho1
       (Geo := Geo) x⟩


omit HSE in
/--
The canonical section plane is distinct from `rho1`.
-/
theorem widthSectionPlane_ne_rho1
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Ne
      (X.widthSectionPlane (Geo := Geo) x)
      X.rho1 := by

  intro hEq

  have hA_rho1 :
      SP.OnPlane
        (X.widthPointA (Geo := Geo) x)
        X.rho1 := by

    rw [← hEq]

    exact
      X.widthPointA_on_sectionPlane
        (Geo := Geo) x

  apply X.ordered.slab.rho_parallel

  exact
    ⟨X.widthPointA (Geo := Geo) x,
     X.widthPointA_on_rho0
       (Geo := Geo) x,
     hA_rho1⟩

end HilbertXI25SolidCutWitness



------------------------------------------------------------------------
-- XI.25: closing the fourth vertex of the width section
------------------------------------------------------------------------

/-!
The candidate section plane `widthSectionPlane x` was defined from
A(x), B(x), C(x).  We now prove that D(x) lies in the same plane.

The proof follows the spatial parallel architecture already developed
for XI.10, XI.16 and XI.24.

1. On `rho0`, the left face A0-B0-B1-A1 is a parallelogram.
   Rotate it so that the longitudinal sides are the directed equal
   segments A1-A0 and B1-B0.  Transport their first endpoints along
   the rays to A(x),B(x), then apply the directed I.33 theorem.  This
   gives a genuine spatial parallelism

       A(x)B(x) || A0B0.

2. On `rho1`, the same construction gives

       C(x)D(x) || C0D0.

3. The bottom face A0-B0-C0-D0 is a parallelogram, hence A0B0 and
   C0D0 are spatially parallel.  Two applications of XI.9 then give

       A(x)B(x) || C(x)D(x).

4. XI.16 applied to the parallel planes rho0,rho1 cut by the candidate
   section plane returns its two exact intersection lines.  The rho0
   intersection is identified with A(x)B(x) by line uniqueness.

5. The rho1 intersection and C(x)D(x) both pass through C(x), and both
   are spatially parallel to the same line A(x)B(x).  Their respective
   carrier planes therefore contain the same line A(x)B(x) and the same
   external point C(x), so the carrier planes coincide.  Hilbert Group IV
   inside that plane identifies the two rho1 lines.

Consequently D(x) belongs to the exact rho1-section line and hence to
`widthSectionPlane x`.

No plane parallel to the section plane is postulated or constructed.
-/

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


omit [HilbertOrder Geo] HSI HSO HSC HSE in
/--
Reverse the order of the two carrier lines in a spatial parallelism
witness.
-/
theorem hilbert_XI25_spaceLinesParallel_symm
    (l m : Geo.Line)
    (h :
      HilbertSpaceLinesParallel Geo l m) :
    HilbertSpaceLinesParallel Geo m l := by

  rcases h with
    ⟨pi, hlpi, hmpi, hDisjoint⟩

  refine
    ⟨pi, hmpi, hlpi, ?_⟩

  rintro ⟨P, hPm, hPl⟩

  exact
    hDisjoint
      ⟨P, hPl, hPm⟩


/--
On `rho0`, the realized cross-edge A(x)B(x) has the same directed
parallel class as the bottom edge A0B0.
-/
theorem width_rho0_cross_directed
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSpaceDirectedParallelSegments
      Geo
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      X.A0 X.B0 := by

  have hFace :
      IsParallelogram
        Geo X.A0 X.B0 X.B1 X.A1 :=
    X.leftXI24.face_rho0

  have hFaceRev :
      IsParallelogram
        Geo X.A1 X.A0 X.B0 X.B1 := by

    constructor

    · exact
        ParallelSymmetry
          Geo
          X.B0 X.B1
          X.A1 X.A0
          hFace.2

    · exact hFace.1

  have hDirSeed :
      HilbertSpaceDirectedParallelSegments
        Geo X.A1 X.A0 X.B1 X.B0 :=
    hilbert_XI24_parallelogram_directed_opposite_sides
      (Geo := Geo)
      X.rho0
      X.A1 X.A0 X.B0 X.B1
      X.ordered.slab.A1_on.2.1
      X.ordered.slab.A0_on.2.1
      X.ordered.slab.B0_on.2.1
      X.ordered.slab.B1_on.2.1
      hFaceRev

  have hDirRadial :
      HilbertSpaceDirectedParallelSegments
        Geo
        (X.widthPointA (Geo := Geo) x)
        X.A0
        (X.widthPointB (Geo := Geo) x)
        X.B0 :=
    hilbert_XI10_directedParallelSegments_transport_first_endpoints
      (Geo := Geo)
      X.A1 X.A0
      X.B1 X.B0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      hDirSeed
      (X.widthPointA_sameRay
        (Geo := Geo) x)
      (X.widthPointB_sameRay
        (Geo := Geo) x)

  have hCongRadial :
      Geo.Congruent
        (X.widthPointA (Geo := Geo) x)
        X.A0
        (X.widthPointB (Geo := Geo) x)
        X.B0 :=
    CongruentReverseBoth
      Geo
      X.A0
      (X.widthPointA (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointA_congruent_B
        (Geo := Geo) x)

  exact
    (hilbert_XI10_I33_directed_output
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      X.A0
      (X.widthPointB (Geo := Geo) x)
      X.B0
      hDirRadial
      hCongRadial).1


/--
On `rho1`, the realized cross-edge C(x)D(x) has the same directed
parallel class as the bottom edge C0D0.
-/
theorem width_rho1_cross_directed
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSpaceDirectedParallelSegments
      Geo
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) x)
      X.C0 X.D0 := by

  have hFace :
      IsParallelogram
        Geo X.D0 X.C0 X.C1 X.D1 :=
    X.leftXI24.face_rho1

  have hFaceRev :
      IsParallelogram
        Geo X.C1 X.C0 X.D0 X.D1 := by

    constructor

    · exact
        ParallelSwapSecondLine
          Geo
          X.C1 X.C0
          X.D1 X.D0
          (ParallelSwapFirstLine
            Geo
            X.C0 X.C1
            X.D1 X.D0
            hFace.2)

    · exact
        ParallelSwapSecondLine
          Geo
          X.C0 X.D0
          X.C1 X.D1
          (ParallelSwapFirstLine
            Geo
            X.D0 X.C0
            X.C1 X.D1
            hFace.1)

  have hDirSeed :
      HilbertSpaceDirectedParallelSegments
        Geo X.C1 X.C0 X.D1 X.D0 :=
    hilbert_XI24_parallelogram_directed_opposite_sides
      (Geo := Geo)
      X.rho1
      X.C1 X.C0 X.D0 X.D1
      X.ordered.slab.C1_on.2.1
      X.ordered.slab.C0_on.2.1
      X.ordered.slab.D0_on.2.1
      X.ordered.slab.D1_on.2.1
      hFaceRev

  have hDirRadial :
      HilbertSpaceDirectedParallelSegments
        Geo
        (X.widthPointC (Geo := Geo) x)
        X.C0
        (X.widthPointD (Geo := Geo) x)
        X.D0 :=
    hilbert_XI10_directedParallelSegments_transport_first_endpoints
      (Geo := Geo)
      X.C1 X.C0
      X.D1 X.D0
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) x)
      hDirSeed
      (X.widthPointC_sameRay
        (Geo := Geo) x)
      (X.widthPointD_sameRay
        (Geo := Geo) x)

  have hC0Cx :
      Ne X.C0
        (X.widthPointC (Geo := Geo) x) :=
    (X.widthPointC_sameRay
      (Geo := Geo) x).2.1.symm

  have hD0Dx :
      Ne X.D0
        (X.widthPointD (Geo := Geo) x) :=
    (X.widthPointD_sameRay
      (Geo := Geo) x).2.1.symm

  have hB_C :
      Geo.Congruent
        X.B0
        (X.widthPointB (Geo := Geo) x)
        X.C0
        (X.widthPointC (Geo := Geo) x) :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      X.C0
      (X.widthPointC (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      hC0Cx
      (X.widthPointC_congruent_B
        (Geo := Geo) x)

  have hB_D :
      Geo.Congruent
        X.B0
        (X.widthPointB (Geo := Geo) x)
        X.D0
        (X.widthPointD (Geo := Geo) x) :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      X.D0
      (X.widthPointD (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      hD0Dx
      (X.widthPointD_congruent_B
        (Geo := Geo) x)

  have hC0Cx_D0Dx :
      Geo.Congruent
        X.C0
        (X.widthPointC (Geo := Geo) x)
        X.D0
        (X.widthPointD (Geo := Geo) x) :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      X.C0
      (X.widthPointC (Geo := Geo) x)
      X.D0
      (X.widthPointD (Geo := Geo) x)
      hB_C
      hB_D

  have hCongRadial :
      Geo.Congruent
        (X.widthPointC (Geo := Geo) x)
        X.C0
        (X.widthPointD (Geo := Geo) x)
        X.D0 :=
    CongruentReverseBoth
      Geo
      X.C0
      (X.widthPointC (Geo := Geo) x)
      X.D0
      (X.widthPointD (Geo := Geo) x)
      hC0Cx_D0Dx

  exact
    (hilbert_XI10_I33_directed_output
      (Geo := Geo)
      (X.widthPointC (Geo := Geo) x)
      X.C0
      (X.widthPointD (Geo := Geo) x)
      X.D0
      hDirRadial
      hCongRadial).1


/--
The two opposite realized cross-edges A(x)B(x) and C(x)D(x) have
spatially parallel carrier lines.

The proof composes the two facewise directed-I.33 results through the
bottom face by two applications of Euclid XI.9.
-/
theorem width_opposite_cross_lines_parallel
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    exists lAB lCD : Geo.Line,
      H.OnLine
          (X.widthPointA (Geo := Geo) x) lAB
      /\
      H.OnLine
          (X.widthPointB (Geo := Geo) x) lAB
      /\
      H.OnLine
          (X.widthPointC (Geo := Geo) x) lCD
      /\
      H.OnLine
          (X.widthPointD (Geo := Geo) x) lCD
      /\
      HilbertSpaceLinesParallel Geo lAB lCD := by

  have hDirAB :=
    X.width_rho0_cross_directed
      (Geo := Geo) x

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) x)
        X.A0 X.B0
        hDirAB
    with
    ⟨_piAB, lAB, lAB0, _tAB,
     hAxAB, hBxAB,
     hA0AB0, hB0AB0,
     _hBxT, _hB0T,
     _hTpi, _hSameAB,
     hParallelAB_AB0⟩

  have hDirCD :=
    X.width_rho1_cross_directed
      (Geo := Geo) x

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointC (Geo := Geo) x)
        (X.widthPointD (Geo := Geo) x)
        X.C0 X.D0
        hDirCD
    with
    ⟨_piCD, lCD, lCD0, _tCD,
     hCxCD, hDxCD,
     hC0CD0, hD0CD0,
     _hDxT, _hD0T,
     _hTpiCD, _hSameCD,
     hParallelCD_CD0⟩

  have hFacePi0 :
      IsParallelogram
        Geo X.A0 X.B0 X.C0 X.D0 :=
    X.leftXI24.face_pi0

  have hDirBase :
      HilbertSpaceDirectedParallelSegments
        Geo X.A0 X.B0 X.D0 X.C0 :=
    hilbert_XI24_parallelogram_directed_opposite_sides
      (Geo := Geo)
      X.pi0
      X.A0 X.B0 X.C0 X.D0
      X.ordered.slab.A0_on.1
      X.ordered.slab.B0_on.1
      X.ordered.slab.C0_on.1
      X.ordered.slab.D0_on.1
      hFacePi0

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        X.A0 X.B0 X.D0 X.C0
        hDirBase
    with
    ⟨_piBase, lAB0', lDC0', _tBase,
     hA0AB0', hB0AB0',
     hD0DC0', hC0DC0',
     _hB0TBase, _hC0TBase,
     _hTpiBase, _hSameBase,
     hParallelBase'⟩

  have hA0B0 :
      Ne X.A0 X.B0 :=
    hFacePi0.1.1

  have hC0D0 :
      Ne X.C0 X.D0 :=
    hFacePi0.1.2.1

  have hAB0Eq :
      lAB0 = lAB0' :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      X.A0 X.B0
      hA0B0
      lAB0 lAB0'
      hA0AB0 hB0AB0
      hA0AB0' hB0AB0'

  have hCD0Eq :
      lCD0 = lDC0' :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      X.C0 X.D0
      hC0D0
      lCD0 lDC0'
      hC0CD0 hD0CD0
      hC0DC0' hD0DC0'

  have hParallelBase :
      HilbertSpaceLinesParallel
        Geo lAB0 lCD0 := by

    simpa [hAB0Eq, hCD0Eq]
      using hParallelBase'

  have hAB0rho0 :
      HilbertLineInPlane Geo lAB0 X.rho0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.A0 X.B0
      hA0B0
      lAB0 hA0AB0 hB0AB0
      X.rho0
      X.ordered.slab.A0_on.2.1
      X.ordered.slab.B0_on.2.1

  have hABrho0 :
      HilbertLineInPlane Geo lAB X.rho0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) x)
      lAB hAxAB hBxAB
      X.rho0
      (X.widthPointA_on_rho0
        (Geo := Geo) x)
      (X.widthPointB_on_rho0
        (Geo := Geo) x)

  have hCD0rho1 :
      HilbertLineInPlane Geo lCD0 X.rho1 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.C0 X.D0
      hC0D0
      lCD0 hC0CD0 hD0CD0
      X.rho1
      X.ordered.slab.C0_on.2.1
      X.ordered.slab.D0_on.2.1

  have hCDrho1 :
      HilbertLineInPlane Geo lCD X.rho1 := by

    have hCxDx :
        Ne
          (X.widthPointC (Geo := Geo) x)
          (X.widthPointD (Geo := Geo) x) := by

      have hNondeg :=
        hilbert_XI10_directedParallelSegments_nondegenerate
          (Geo := Geo)
          (X.widthPointC (Geo := Geo) x)
          (X.widthPointD (Geo := Geo) x)
          X.C0 X.D0
          hDirCD

      exact hNondeg.1

    exact
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        (X.widthPointC (Geo := Geo) x)
        (X.widthPointD (Geo := Geo) x)
        hCxDx
        lCD hCxCD hDxCD
        X.rho1
        (X.widthPointC_on_rho1
          (Geo := Geo) x)
        (X.widthPointD_on_rho1
          (Geo := Geo) x)

  have hParallelCD0_AB0 :
      HilbertSpaceLinesParallel
        Geo lCD0 lAB0 :=
    hilbert_XI25_spaceLinesParallel_symm
      (Geo := Geo)
      lAB0 lCD0
      hParallelBase

  have hNoCommon1 :
      Not
        (exists omega : SP.Plane,
          HilbertLineInPlane Geo lAB omega
          /\
          HilbertLineInPlane Geo lCD0 omega
          /\
          HilbertLineInPlane Geo lAB0 omega) := by

    rintro
      ⟨omega,
       hABomega,
       hCD0omega,
       hAB0omega⟩

    rcases hParallelAB_AB0 with
      ⟨_carrierAB,
       _hABcarrier,
       _hAB0carrier,
       hDisAB_AB0⟩

    have hAxNotAB0 :
        Not
          (H.OnLine
            (X.widthPointA (Geo := Geo) x)
            lAB0) := by

      intro hAxAB0

      exact
        hDisAB_AB0
          ⟨X.widthPointA (Geo := Geo) x,
           hAxAB,
           hAxAB0⟩

    have hAxomega :
        SP.OnPlane
          (X.widthPointA (Geo := Geo) x)
          omega :=
      hABomega
        (X.widthPointA (Geo := Geo) x)
        hAxAB

    have hOmegaRho0 :
        omega = X.rho0 :=
      hilbert_XI9_planes_eq_of_common_line_and_external_point
        (Geo := Geo)
        lAB0
        (X.widthPointA (Geo := Geo) x)
        hAxNotAB0
        omega X.rho0
        hAB0omega
        hAB0rho0
        hAxomega
        (X.widthPointA_on_rho0
          (Geo := Geo) x)

    have hC0omega :
        SP.OnPlane X.C0 omega :=
      hCD0omega X.C0 hC0CD0

    have hC0rho0 :
        SP.OnPlane X.C0 X.rho0 := by
      rw [← hOmegaRho0]
      exact hC0omega

    exact
      X.ordered.slab.rho_parallel
        ⟨X.C0,
         hC0rho0,
         X.ordered.slab.C0_on.2.1⟩

  have hParallelAB_CD0 :
      HilbertSpaceLinesParallel
        Geo lAB lCD0 :=
    euclid_proposition_11_9
      (Geo := Geo)
      lAB lCD0 lAB0
      hParallelAB_AB0
      hParallelCD0_AB0
      hNoCommon1

  have hNoCommon2 :
      Not
        (exists omega : SP.Plane,
          HilbertLineInPlane Geo lAB omega
          /\
          HilbertLineInPlane Geo lCD omega
          /\
          HilbertLineInPlane Geo lCD0 omega) := by

    rintro
      ⟨omega,
       hABomega,
       hCDomega,
       hCD0omega⟩

    rcases hParallelCD_CD0 with
      ⟨_carrierCD,
       _hCDcarrier,
       _hCD0carrier,
       hDisCD_CD0⟩

    have hCxNotCD0 :
        Not
          (H.OnLine
            (X.widthPointC (Geo := Geo) x)
            lCD0) := by

      intro hCxCD0

      exact
        hDisCD_CD0
          ⟨X.widthPointC (Geo := Geo) x,
           hCxCD,
           hCxCD0⟩

    have hCxomega :
        SP.OnPlane
          (X.widthPointC (Geo := Geo) x)
          omega :=
      hCDomega
        (X.widthPointC (Geo := Geo) x)
        hCxCD

    have hOmegaRho1 :
        omega = X.rho1 :=
      hilbert_XI9_planes_eq_of_common_line_and_external_point
        (Geo := Geo)
        lCD0
        (X.widthPointC (Geo := Geo) x)
        hCxNotCD0
        omega X.rho1
        hCD0omega
        hCD0rho1
        hCxomega
        (X.widthPointC_on_rho1
          (Geo := Geo) x)

    have hAxomega :
        SP.OnPlane
          (X.widthPointA (Geo := Geo) x)
          omega :=
      hABomega
        (X.widthPointA (Geo := Geo) x)
        hAxAB

    have hAxrho1 :
        SP.OnPlane
          (X.widthPointA (Geo := Geo) x)
          X.rho1 := by
      rw [← hOmegaRho1]
      exact hAxomega

    exact
      X.ordered.slab.rho_parallel
        ⟨X.widthPointA (Geo := Geo) x,
         X.widthPointA_on_rho0
           (Geo := Geo) x,
         hAxrho1⟩

  have hParallelAB_CD :
      HilbertSpaceLinesParallel
        Geo lAB lCD :=
    euclid_proposition_11_9
      (Geo := Geo)
      lAB lCD lCD0
      hParallelAB_CD0
      hParallelCD_CD0
      hNoCommon2

  exact
    ⟨lAB, lCD,
     hAxAB, hBxAB,
     hCxCD, hDxCD,
     hParallelAB_CD⟩


/--
The fourth synchronized endpoint D(x) lies in the canonical section
plane determined by A(x),B(x),C(x).
-/
theorem widthPointD_on_sectionPlane
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthPointD (Geo := Geo) x)
      (X.widthSectionPlane
        (Geo := Geo) x) := by

  rcases
      X.width_opposite_cross_lines_parallel
        (Geo := Geo) x
    with
    ⟨lAB, lCD,
     hAxAB, hBxAB,
     hCxCD, hDxCD,
     hParallelAB_CD⟩

  rcases
      euclid_proposition_11_16
        (Geo := Geo)
        X.rho0
        X.rho1
        (X.widthSectionPlane
          (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        X.ordered.slab.rho_parallel
        (X.widthPointA_on_rho0
          (Geo := Geo) x)
        (X.widthPointA_on_sectionPlane
          (Geo := Geo) x)
        (X.widthPointC_on_rho1
          (Geo := Geo) x)
        (X.widthPointC_on_sectionPlane
          (Geo := Geo) x)
    with
    ⟨lSec0, lSec1, hSec⟩

  have hAxSec0 :
      H.OnLine
        (X.widthPointA (Geo := Geo) x)
        lSec0 :=
    hSec.1

  have hCxSec1 :
      H.OnLine
        (X.widthPointC (Geo := Geo) x)
        lSec1 :=
    hSec.2.1

  have hMeet0 :=
    hSec.2.2.1

  have hMeet1 :=
    hSec.2.2.2.1

  have hParallelSec :
      HilbertSpaceLinesParallel
        Geo lSec0 lSec1 :=
    hSec.2.2.2.2

  have hBxSec0 :
      H.OnLine
        (X.widthPointB (Geo := Geo) x)
        lSec0 := by

    exact
      (hMeet0
        (X.widthPointB (Geo := Geo) x)).mp
        (And.intro
          (X.widthPointB_on_rho0
            (Geo := Geo) x)
          (X.widthPointB_on_sectionPlane
            (Geo := Geo) x))

  have hSec0Eq :
      lSec0 = lAB :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) x)
      lSec0 lAB
      hAxSec0 hBxSec0
      hAxAB hBxAB

  have hParallelAB_Sec1 :
      HilbertSpaceLinesParallel
        Geo lAB lSec1 := by
    rw [← hSec0Eq]
    exact hParallelSec

  rcases hParallelAB_CD with
    ⟨omegaCD,
     hABomegaCD,
     hCDomegaCD,
     hDisAB_CD⟩

  rcases hParallelAB_Sec1 with
    ⟨omegaSec,
     hABomegaSec,
     hSec1omegaSec,
     hDisAB_Sec1⟩

  have hCxNotAB :
      Not
        (H.OnLine
          (X.widthPointC (Geo := Geo) x)
          lAB) := by

    intro hCxAB

    exact
      hDisAB_CD
        ⟨X.widthPointC (Geo := Geo) x,
         hCxAB,
         hCxCD⟩

  have hCxOmegaCD :
      SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        omegaCD :=
    hCDomegaCD
      (X.widthPointC (Geo := Geo) x)
      hCxCD

  have hCxOmegaSec :
      SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        omegaSec :=
    hSec1omegaSec
      (X.widthPointC (Geo := Geo) x)
      hCxSec1

  have hOmegaEq :
      omegaCD = omegaSec :=
    hilbert_XI9_planes_eq_of_common_line_and_external_point
      (Geo := Geo)
      lAB
      (X.widthPointC (Geo := Geo) x)
      hCxNotAB
      omegaCD omegaSec
      hABomegaCD
      hABomegaSec
      hCxOmegaCD
      hCxOmegaSec

  have hSec1omegaCD :
      HilbertLineInPlane
        Geo lSec1 omegaCD := by
    rw [hOmegaEq]
    exact hSec1omegaSec

  have hDisCD_AB :
      HilbertLinesDisjoint Geo lCD lAB := by
    rintro ⟨P, hPCD, hPAB⟩
    exact
      hDisAB_CD
        ⟨P, hPAB, hPCD⟩

  have hDisSec1_AB :
      HilbertLinesDisjoint Geo lSec1 lAB := by
    rintro ⟨P, hPSec, hPAB⟩
    exact
      hDisAB_Sec1
        ⟨P, hPAB, hPSec⟩

  have hSec1EqCD :
      lSec1 = lCD := by

    have hCD_eq_Sec1 :
        lCD = lSec1 :=
      HilbertSpaceEuclidean.parallel_unique_in_plane
        (Geo := Geo)
        omegaCD
        lAB
        hABomegaCD
        (X.widthPointC (Geo := Geo) x)
        hCxOmegaCD
        hCxNotAB
        lCD lSec1
        hCDomegaCD
        hSec1omegaCD
        hCxCD
        hDisCD_AB
        hCxSec1
        hDisSec1_AB

    exact hCD_eq_Sec1.symm

  have hDxSec1 :
      H.OnLine
        (X.widthPointD (Geo := Geo) x)
        lSec1 := by
    rw [hSec1EqCD]
    exact hDxCD

  have hDInter :
      SP.OnPlane
          (X.widthPointD (Geo := Geo) x)
          X.rho1
      /\
      SP.OnPlane
          (X.widthPointD (Geo := Geo) x)
          (X.widthSectionPlane
            (Geo := Geo) x) :=
    (hMeet1
      (X.widthPointD (Geo := Geo) x)).mpr
      hDxSec1

  exact hDInter.2


/--
All four synchronized endpoints lie in the canonical section plane.
-/
theorem widthPoints_on_sectionPlane
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
        (X.widthPointA (Geo := Geo) x)
        (X.widthSectionPlane (Geo := Geo) x)
    /\
    SP.OnPlane
        (X.widthPointB (Geo := Geo) x)
        (X.widthSectionPlane (Geo := Geo) x)
    /\
    SP.OnPlane
        (X.widthPointC (Geo := Geo) x)
        (X.widthSectionPlane (Geo := Geo) x)
    /\
    SP.OnPlane
        (X.widthPointD (Geo := Geo) x)
        (X.widthSectionPlane (Geo := Geo) x) := by

  exact
    And.intro
      (X.widthPointA_on_sectionPlane
        (Geo := Geo) x)
      (And.intro
        (X.widthPointB_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointC_on_sectionPlane
            (Geo := Geo) x)
          (X.widthPointD_on_sectionPlane
            (Geo := Geo) x)))

end HilbertXI25SolidCutWitness



------------------------------------------------------------------------
-- XI.25: every realized width section is parallel to the base section
------------------------------------------------------------------------

/-!
The fourth vertex has now been closed, so each width class `x` gives a
genuine four-corner section plane `pi(x)`.

The remaining structural fact needed before assembling arbitrary cut
witnesses is

    pi(x) || pi0.

We prove it by Euclid XI.15.

Inside the candidate section plane we use the two intersecting cross
edges

    A(x)B(x),  B(x)C(x),

and inside the base plane `pi0` the corresponding edges

    A0B0,  B0C0.

The first parallel pair was already obtained in the previous module.
The second one is constructed here by the same directed-I.33 mechanism
inside the side face `sigma0`.

The XI.15 non-coplanarity hypothesis is not postulated.  If all four
carrier lines lay in one plane `omega`, then A(x),B(x),C(x) would force
`omega = pi(x)`, while A0,B0,C0 would force `omega = pi0`.  This
contradicts the fact that A(x), lying strictly on the ray A0A1 beyond
A0, cannot belong to `pi0`.
-/


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
On `sigma0`, the realized cross-edge B(x)C(x) has the same directed
parallel class as the bottom edge B0C0.
-/
theorem width_sigma0_cross_directed
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSpaceDirectedParallelSegments
      Geo
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      X.B0 X.C0 := by

  have hFace :
      IsParallelogram
        Geo X.C0 X.B0 X.B1 X.C1 :=
    X.leftXI24.face_sigma0

  have hFaceRev :
      IsParallelogram
        Geo X.B1 X.B0 X.C0 X.C1 := by

    constructor

    · exact
        ParallelSwapSecondLine
          Geo
          X.B1 X.B0
          X.C1 X.C0
          (ParallelSwapFirstLine
            Geo
            X.B0 X.B1
            X.C1 X.C0
            hFace.2)

    · exact
        ParallelSwapSecondLine
          Geo
          X.B0 X.C0
          X.B1 X.C1
          (ParallelSwapFirstLine
            Geo
            X.C0 X.B0
            X.B1 X.C1
            hFace.1)

  have hDirSeed :
      HilbertSpaceDirectedParallelSegments
        Geo X.B1 X.B0 X.C1 X.C0 :=
    hilbert_XI24_parallelogram_directed_opposite_sides
      (Geo := Geo)
      X.sigma0
      X.B1 X.B0 X.C0 X.C1
      X.ordered.slab.B1_on.2.2
      X.ordered.slab.B0_on.2.2
      X.ordered.slab.C0_on.2.2
      X.ordered.slab.C1_on.2.2
      hFaceRev

  have hDirRadial :
      HilbertSpaceDirectedParallelSegments
        Geo
        (X.widthPointB (Geo := Geo) x)
        X.B0
        (X.widthPointC (Geo := Geo) x)
        X.C0 :=
    hilbert_XI10_directedParallelSegments_transport_first_endpoints
      (Geo := Geo)
      X.B1 X.B0
      X.C1 X.C0
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      hDirSeed
      (X.widthPointB_sameRay
        (Geo := Geo) x)
      (X.widthPointC_sameRay
        (Geo := Geo) x)

  have hC0Cx :
      Ne X.C0
        (X.widthPointC (Geo := Geo) x) :=
    (X.widthPointC_sameRay
      (Geo := Geo) x).2.1.symm

  have hB0Bx_C0Cx :
      Geo.Congruent
        X.B0
        (X.widthPointB (Geo := Geo) x)
        X.C0
        (X.widthPointC (Geo := Geo) x) :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      X.C0
      (X.widthPointC (Geo := Geo) x)
      X.B0
      (X.widthPointB (Geo := Geo) x)
      hC0Cx
      (X.widthPointC_congruent_B
        (Geo := Geo) x)

  have hCongRadial :
      Geo.Congruent
        (X.widthPointB (Geo := Geo) x)
        X.B0
        (X.widthPointC (Geo := Geo) x)
        X.C0 :=
    CongruentReverseBoth
      Geo
      X.B0
      (X.widthPointB (Geo := Geo) x)
      X.C0
      (X.widthPointC (Geo := Geo) x)
      hB0Bx_C0Cx

  exact
    (hilbert_XI10_I33_directed_output
      (Geo := Geo)
      (X.widthPointB (Geo := Geo) x)
      X.B0
      (X.widthPointC (Geo := Geo) x)
      X.C0
      hDirRadial
      hCongRadial).1


omit HSE in
/--
A realized positive width endpoint A(x) cannot lie back in the base
plane `pi0`.
-/
theorem widthPointA_not_on_pi0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Not
      (SP.OnPlane
        (X.widthPointA (Geo := Geo) x)
        X.pi0) := by

  intro hAxPi0

  have hA0Ax :
      Ne X.A0
        (X.widthPointA (Geo := Geo) x) :=
    (X.widthPointA_sameRay
      (Geo := Geo) x).2.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        X.A0
        (X.widthPointA (Geo := Geo) x)
        hA0Ax
    with
    ⟨l, hA0l, hAxl⟩

  have hA0AxA1 :
      PrimCollinear
        Geo
        X.A0
        (X.widthPointA (Geo := Geo) x)
        X.A1 :=
    PrimCollinearRotate
      Geo
      X.A0 X.A1
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointA_sameRay
        (Geo := Geo) x).2.2.1

  have hA1l :
      H.OnLine X.A1 l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hA0Ax
      hA0l hAxl
      hA0AxA1

  have hlPi0 :
      HilbertLineInPlane Geo l X.pi0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.A0
      (X.widthPointA (Geo := Geo) x)
      hA0Ax
      l hA0l hAxl
      X.pi0
      X.ordered.slab.A0_on.1
      hAxPi0

  have hA1Pi0 :
      SP.OnPlane X.A1 X.pi0 :=
    hlPi0 X.A1 hA1l

  exact
    X.ordered.slab.pi01_parallel
      ⟨X.A1,
       hA1Pi0,
       X.ordered.slab.A1_on.1⟩


omit HSE in
/--
The realized width section plane is distinct from the original base
section `pi0`.
-/
theorem widthSectionPlane_ne_pi0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    Ne
      (X.widthSectionPlane (Geo := Geo) x)
      X.pi0 := by

  intro hEq

  apply
    X.widthPointA_not_on_pi0
      (Geo := Geo) x

  rw [← hEq]

  exact
    X.widthPointA_on_sectionPlane
      (Geo := Geo) x


/--
Every realized width section plane is parallel to the original base
plane `pi0`.
-/
theorem widthSectionPlane_parallel_pi0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertSpacePlanesParallelIncidence
      Geo
      (X.widthSectionPlane (Geo := Geo) x)
      X.pi0 := by

  have hDirAB :=
    X.width_rho0_cross_directed
      (Geo := Geo) x

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) x)
        X.A0 X.B0
        hDirAB
    with
    ⟨_omegaAB, lAB, lAB0, _tAB,
     hAxAB, hBxAB,
     hA0AB0, hB0AB0,
     _hBxTAB, _hB0TAB,
     _hTAB, _hSameAB,
     hParallelAB_AB0⟩

  have hDirBC :=
    X.width_sigma0_cross_directed
      (Geo := Geo) x

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        X.B0 X.C0
        hDirBC
    with
    ⟨_omegaBC, lBC, lBC0, _tBC,
     hBxBC, hCxBC,
     hB0BC0, hC0BC0,
     _hCxTBC, _hC0TBC,
     _hTBC, _hSameBC,
     hParallelBC_BC0⟩

  have hAB :
      Ne
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) x) :=
    X.widthPointA_ne_widthPointB
      (Geo := Geo) x

  have hBC :
      Ne
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x) :=
    (hilbert_XI10_directedParallelSegments_nondegenerate
      (Geo := Geo)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      X.B0 X.C0
      hDirBC).1

  have hFacePi0 :
      IsParallelogram
        Geo X.A0 X.B0 X.C0 X.D0 :=
    X.leftXI24.face_pi0

  have hA0B0 : Ne X.A0 X.B0 :=
    hFacePi0.1.1

  have hB0C0 : Ne X.B0 X.C0 :=
    hFacePi0.2.1

  have hABSection :
      HilbertLineInPlane
        Geo lAB
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      hAB
      lAB hAxAB hBxAB
      (X.widthSectionPlane
        (Geo := Geo) x)
      (X.widthPointA_on_sectionPlane
        (Geo := Geo) x)
      (X.widthPointB_on_sectionPlane
        (Geo := Geo) x)

  have hBCSection :
      HilbertLineInPlane
        Geo lBC
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      hBC
      lBC hBxBC hCxBC
      (X.widthSectionPlane
        (Geo := Geo) x)
      (X.widthPointB_on_sectionPlane
        (Geo := Geo) x)
      (X.widthPointC_on_sectionPlane
        (Geo := Geo) x)

  have hAB0Pi0 :
      HilbertLineInPlane Geo lAB0 X.pi0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.A0 X.B0 hA0B0
      lAB0 hA0AB0 hB0AB0
      X.pi0
      X.ordered.slab.A0_on.1
      X.ordered.slab.B0_on.1

  have hBC0Pi0 :
      HilbertLineInPlane Geo lBC0 X.pi0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.B0 X.C0 hB0C0
      lBC0 hB0BC0 hC0BC0
      X.pi0
      X.ordered.slab.B0_on.1
      X.ordered.slab.C0_on.1

  let l1 :
      PlaneLine Geo
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    ⟨lAB, hABSection⟩

  let l2 :
      PlaneLine Geo
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    ⟨lBC, hBCSection⟩

  let m1 : PlaneLine Geo X.pi0 :=
    ⟨lAB0, hAB0Pi0⟩

  let m2 : PlaneLine Geo X.pi0 :=
    ⟨lBC0, hBC0Pi0⟩

  let Bx :
      PlanePoint Geo
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    ⟨X.widthPointB (Geo := Geo) x,
     X.widthPointB_on_sectionPlane
       (Geo := Geo) x⟩

  have hl12raw : Ne lAB lBC := by
    intro hEq

    apply
      X.widthPoints_ABC_noncollinear
        (Geo := Geo) x

    exact
      ⟨lAB,
       hAxAB,
       hBxAB,
       by
         rw [hEq]
         exact hCxBC⟩

  have hl12 : Ne l1 l2 := by
    intro hEq
    apply hl12raw
    exact congrArg Subtype.val hEq

  have hBxL1 :
      H.OnLine Bx.1 l1.1 := by
    simpa [Bx, l1] using hBxAB

  have hBxL2 :
      H.OnLine Bx.1 l2.1 := by
    simpa [Bx, l2] using hBxBC

  have hABC0 :
      Not
        (PrimCollinear
          Geo X.A0 X.B0 X.C0) :=
    (parallelogram_vertices_noncollinear
      Geo
      X.A0 X.B0 X.C0 X.D0
      hFacePi0).2.1

  have hNoCommonRaw :
      Not
        (exists omega : SP.Plane,
          HilbertLineInPlane Geo lAB omega /\
          HilbertLineInPlane Geo lBC omega /\
          HilbertLineInPlane Geo lAB0 omega /\
          HilbertLineInPlane Geo lBC0 omega) := by

    rintro
      ⟨omega,
       hABomega,
       hBComega,
       hAB0omega,
       hBC0omega⟩

    have hAxOmega :
        SP.OnPlane
          (X.widthPointA (Geo := Geo) x)
          omega :=
      hABomega
        (X.widthPointA (Geo := Geo) x)
        hAxAB

    have hBxOmega :
        SP.OnPlane
          (X.widthPointB (Geo := Geo) x)
          omega :=
      hABomega
        (X.widthPointB (Geo := Geo) x)
        hBxAB

    have hCxOmega :
        SP.OnPlane
          (X.widthPointC (Geo := Geo) x)
          omega :=
      hBComega
        (X.widthPointC (Geo := Geo) x)
        hCxBC

    have hOmegaSection :
        omega =
          X.widthSectionPlane
            (Geo := Geo) x :=
      X.widthSectionPlane_unique
        (Geo := Geo)
        x omega
        hAxOmega hBxOmega hCxOmega

    have hA0Omega :
        SP.OnPlane X.A0 omega :=
      hAB0omega X.A0 hA0AB0

    have hB0Omega :
        SP.OnPlane X.B0 omega :=
      hAB0omega X.B0 hB0AB0

    have hC0Omega :
        SP.OnPlane X.C0 omega :=
      hBC0omega X.C0 hC0BC0

    have hOmegaPi0 :
        omega = X.pi0 :=
      HilbertSpaceIncidence.plane_unique
        (Geo := Geo)
        X.A0 X.B0 X.C0
        hABC0
        omega X.pi0
        hA0Omega hB0Omega hC0Omega
        X.ordered.slab.A0_on.1
        X.ordered.slab.B0_on.1
        X.ordered.slab.C0_on.1

    apply
      X.widthSectionPlane_ne_pi0
        (Geo := Geo) x

    exact
      hOmegaSection.symm.trans
        hOmegaPi0

  have hNoCommon :
      Not
        (exists omega : SP.Plane,
          HilbertLineInPlane Geo l1.1 omega /\
          HilbertLineInPlane Geo l2.1 omega /\
          HilbertLineInPlane Geo m1.1 omega /\
          HilbertLineInPlane Geo m2.1 omega) := by

    simpa [l1, l2, m1, m2]
      using hNoCommonRaw

  have hParallel :
      HilbertSpacePlanesParallel
        Geo
        (X.widthSectionPlane
          (Geo := Geo) x)
        X.pi0 :=
    euclid_proposition_11_15
      (Geo := Geo)
      (X.widthSectionPlane
        (Geo := Geo) x)
      X.pi0
      l1 l2
      m1 m2
      Bx
      hBxL1 hBxL2
      hl12
      (by
        simpa [l1, m1]
          using hParallelAB_AB0)
      (by
        simpa [l2, m2]
          using hParallelBC_BC0)
      hNoCommon

  simpa
    [HilbertSpacePlanesParallel,
     HilbertSpacePlanesParallelIncidence]
    using hParallel

end HilbertXI25SolidCutWitness



------------------------------------------------------------------------
-- XI.25: arbitrary ordered width pair gives a genuine solid cut
------------------------------------------------------------------------

/-!
We can now assemble the geometry needed by the strict-comparison part
of XI.25.

For two positive width classes `x < y` on the fixed carrier plane
`rho0`, the normalized construction supplies:

* four ordered points at width `x`;
* four ordered points at width `y`;
* section planes `pi(x)` and `pi(y)`;
* each section plane is parallel to the original base plane `pi0`.

The only remaining parallel-plane datum is

    pi(x) || pi(y).

It is obtained source-faithfully from XI.15.  In the side plane `rho0`,
the cross-lines A(x)B(x) and A(y)B(y) are both parallel to A0B0.
Hilbert Group IV inside `rho0` therefore makes them parallel to one
another.  The same argument in `sigma0` gives

    B(x)C(x) || B(y)C(y).

These two corresponding pairs meet respectively at B(x) and B(y), so
XI.15 gives the desired parallelism of the section planes.

With the three parallel section planes and the four synchronized
betweenness relations, we obtain an actual
`HilbertXI25OrderedTwoSlabConfiguration`, hence an actual
`HilbertXI25SolidCutWitness`.

This is the geometric bridge that the abstract `cut_of_less` field of
`HilbertXI25WidthRealization` was waiting for.
-/

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


omit [HilbertOrder Geo] H HSI HSO HSC HSE in
/--
Parallel-plane incidence is symmetric.
-/
theorem hilbert_XI25_planesParallelIncidence_symm
    (pi rho : SP.Plane)
    (h :
      HilbertSpacePlanesParallelIncidence
        Geo pi rho) :
    HilbertSpacePlanesParallelIncidence
      Geo rho pi := by

  rintro ⟨P, hPrho, hPpi⟩

  exact
    h ⟨P, hPpi, hPrho⟩


omit [HilbertOrder Geo] in
/--
Transitivity of spatial line parallelism inside one fixed ambient
plane, assuming the two target lines are distinct.

This is the plane-local Group IV argument underlying Euclid I.30.
-/
theorem hilbert_XI25_spaceLinesParallel_transitive_in_plane_distinct
    (pi : SP.Plane)
    (l m n : Geo.Line)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hmpi : HilbertLineInPlane Geo m pi)
    (hnpi : HilbertLineInPlane Geo n pi)
    (hln : HilbertSpaceLinesParallel Geo l n)
    (hmn : HilbertSpaceLinesParallel Geo m n)
    (hlm : Ne l m) :
    HilbertSpaceLinesParallel Geo l m := by

  rcases hln with
    ⟨_omegaL, _hlOmega, _hnOmegaL, hDisLN⟩

  rcases hmn with
    ⟨_omegaM, _hmOmega, _hnOmegaM, hDisMN⟩

  refine
    ⟨pi, hlpi, hmpi, ?_⟩

  rintro ⟨P, hPl, hPm⟩

  have hPpi :
      SP.OnPlane P pi :=
    hlpi P hPl

  have hPn :
      Not (H.OnLine P n) := by
    intro hPn
    exact
      hDisLN
        ⟨P, hPl, hPn⟩

  have hEq :
      l = m :=
    HilbertSpaceEuclidean.parallel_unique_in_plane
      (Geo := Geo)
      pi
      n
      hnpi
      P
      hPpi
      hPn
      l m
      hlpi hmpi
      hPl hDisLN
      hPm hDisMN

  exact hlm hEq


/--
Strictly ordered widths determine distinct section planes.
-/
theorem widthSectionPlanes_ne_of_less
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    Ne
      (X.widthSectionPlane (Geo := Geo) x)
      (X.widthSectionPlane (Geo := Geo) y) := by

  intro hEq

  have hAxy :
      Geo.Between
        X.A0
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y) :=
    X.widthPointA_between
      (Geo := Geo)
      x y hxy

  have hAdata :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      X.A0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointA (Geo := Geo) y)
      hAxy

  have hAxAy :
      Ne
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y) :=
    hAdata.2.1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y)
        hAxAy
    with
    ⟨lA, hAxlA, hAylA⟩

  have hAylA' :
      H.OnLine
        (X.widthPointA (Geo := Geo) y)
        lA :=
    hAylA

  have hA0AxAy :
      PrimCollinear
        Geo
        X.A0
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y) :=
    hAdata.2.2.2.1

  have hAxAyA0 :
      PrimCollinear
        Geo
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y)
        X.A0 :=
    PrimCollinearCycle
      Geo
      X.A0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointA (Geo := Geo) y)
      hA0AxAy

  have hA0lA :
      H.OnLine X.A0 lA :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAxAy
      hAxlA hAylA'
      hAxAyA0

  have hAypix :
      SP.OnPlane
        (X.widthPointA (Geo := Geo) y)
        (X.widthSectionPlane
          (Geo := Geo) x) := by
    rw [hEq]
    exact
      X.widthPointA_on_sectionPlane
        (Geo := Geo) y

  have hlApiX :
      HilbertLineInPlane
        Geo lA
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointA (Geo := Geo) y)
      hAxAy
      lA hAxlA hAylA'
      (X.widthSectionPlane
        (Geo := Geo) x)
      (X.widthPointA_on_sectionPlane
        (Geo := Geo) x)
      hAypix

  have hA0pix :
      SP.OnPlane
        X.A0
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    hlApiX X.A0 hA0lA

  exact
    (X.widthSectionPlane_parallel_pi0
      (Geo := Geo) x)
      ⟨X.A0,
       hA0pix,
       X.ordered.slab.A0_on.1⟩


/--
For `x < y`, the two realized section planes are parallel.
-/
theorem widthSectionPlanes_parallel_of_less
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertSpacePlanesParallelIncidence
      Geo
      (X.widthSectionPlane (Geo := Geo) x)
      (X.widthSectionPlane (Geo := Geo) y) := by

  --------------------------------------------------------------------
  -- A(x)B(x), A(y)B(y), and A0B0 inside rho0.
  --------------------------------------------------------------------

  have hDirABx :=
    X.width_rho0_cross_directed
      (Geo := Geo) x

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) x)
        X.A0 X.B0
        hDirABx
    with
    ⟨_omegaABx, lABx, lAB0x, _tABx,
     hAxABx, hBxABx,
     hA0AB0x, hB0AB0x,
     _hBxTABx, _hB0TABx,
     _hTABx, _hSameABx,
     hParallelABx_AB0x⟩

  have hDirABy :=
    X.width_rho0_cross_directed
      (Geo := Geo) y

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointA (Geo := Geo) y)
        (X.widthPointB (Geo := Geo) y)
        X.A0 X.B0
        hDirABy
    with
    ⟨_omegaABy, lABy, lAB0y, _tABy,
     hAyABy, hByABy,
     hA0AB0y, hB0AB0y,
     _hByTABy, _hB0TABy,
     _hTABy, _hSameABy,
     hParallelABy_AB0y⟩

  have hAB0 :
      Ne X.A0 X.B0 :=
    X.leftXI24.face_pi0.1.1

  have hAB0Eq :
      lAB0y = lAB0x :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      X.A0 X.B0 hAB0
      lAB0y lAB0x
      hA0AB0y hB0AB0y
      hA0AB0x hB0AB0x

  have hParallelABy_AB0x :
      HilbertSpaceLinesParallel
        Geo lABy lAB0x := by
    rw [← hAB0Eq]
    exact hParallelABy_AB0y

  have hABxRho0 :
      HilbertLineInPlane
        Geo lABx X.rho0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) x)
      lABx hAxABx hBxABx
      X.rho0
      (X.widthPointA_on_rho0
        (Geo := Geo) x)
      (X.widthPointB_on_rho0
        (Geo := Geo) x)

  have hAByRho0 :
      HilbertLineInPlane
        Geo lABy X.rho0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) y)
      (X.widthPointB (Geo := Geo) y)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) y)
      lABy hAyABy hByABy
      X.rho0
      (X.widthPointA_on_rho0
        (Geo := Geo) y)
      (X.widthPointB_on_rho0
        (Geo := Geo) y)

  have hAB0Rho0 :
      HilbertLineInPlane
        Geo lAB0x X.rho0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.A0 X.B0 hAB0
      lAB0x hA0AB0x hB0AB0x
      X.rho0
      X.ordered.slab.A0_on.2.1
      X.ordered.slab.B0_on.2.1

  have hABxNeABy :
      Ne lABx lABy := by

    intro hEq

    have hAxy :=
      X.widthPointA_between
        (Geo := Geo)
        x y hxy

    have hAdata :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X.A0
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y)
        hAxy

    have hAxAy :
        Ne
          (X.widthPointA (Geo := Geo) x)
          (X.widthPointA (Geo := Geo) y) :=
      hAdata.2.1

    have hAyABx :
        H.OnLine
          (X.widthPointA (Geo := Geo) y)
          lABx := by
      rw [hEq]
      exact hAyABy

    have hAxAyA0 :
        PrimCollinear
          Geo
          (X.widthPointA (Geo := Geo) x)
          (X.widthPointA (Geo := Geo) y)
          X.A0 :=
      PrimCollinearCycle
        Geo
        X.A0
        (X.widthPointA (Geo := Geo) x)
        (X.widthPointA (Geo := Geo) y)
        hAdata.2.2.2.1

    have hA0ABx :
        H.OnLine X.A0 lABx :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAxAy
        hAxABx hAyABx
        hAxAyA0

    rcases hParallelABx_AB0x with
      ⟨_omega,
       _hABxOmega,
       _hAB0Omega,
       hDis⟩

    exact
      hDis
        ⟨X.A0,
         hA0ABx,
         hA0AB0x⟩

  have hParallelABx_ABy :
      HilbertSpaceLinesParallel
        Geo lABx lABy :=
    hilbert_XI25_spaceLinesParallel_transitive_in_plane_distinct
      (Geo := Geo)
      X.rho0
      lABx lABy lAB0x
      hABxRho0
      hAByRho0
      hAB0Rho0
      hParallelABx_AB0x
      hParallelABy_AB0x
      hABxNeABy

  --------------------------------------------------------------------
  -- B(x)C(x), B(y)C(y), and B0C0 inside sigma0.
  --------------------------------------------------------------------

  have hDirBCx :=
    X.width_sigma0_cross_directed
      (Geo := Geo) x

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        X.B0 X.C0
        hDirBCx
    with
    ⟨_omegaBCx, lBCx, lBC0x, _tBCx,
     hBxBCx, hCxBCx,
     hB0BC0x, hC0BC0x,
     _hCxTBCx, _hC0TBCx,
     _hTBCx, _hSameBCx,
     hParallelBCx_BC0x⟩

  have hDirBCy :=
    X.width_sigma0_cross_directed
      (Geo := Geo) y

  rcases
      hilbert_XI10_directedParallelSegments_carriers
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) y)
        (X.widthPointC (Geo := Geo) y)
        X.B0 X.C0
        hDirBCy
    with
    ⟨_omegaBCy, lBCy, lBC0y, _tBCy,
     hByBCy, hCyBCy,
     hB0BC0y, hC0BC0y,
     _hCyTBCy, _hC0TBCy,
     _hTBCy, _hSameBCy,
     hParallelBCy_BC0y⟩

  have hBC0 :
      Ne X.B0 X.C0 :=
    X.leftXI24.face_pi0.2.1

  have hBC0Eq :
      lBC0y = lBC0x :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      X.B0 X.C0 hBC0
      lBC0y lBC0x
      hB0BC0y hC0BC0y
      hB0BC0x hC0BC0x

  have hParallelBCy_BC0x :
      HilbertSpaceLinesParallel
        Geo lBCy lBC0x := by
    rw [← hBC0Eq]
    exact hParallelBCy_BC0y

  have hBCxSigma0 :
      HilbertLineInPlane
        Geo lBCx X.sigma0 := by

    have hBCx :
        Ne
          (X.widthPointB (Geo := Geo) x)
          (X.widthPointC (Geo := Geo) x) :=
      (hilbert_XI10_directedParallelSegments_nondegenerate
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        X.B0 X.C0
        hDirBCx).1

    exact
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        hBCx
        lBCx hBxBCx hCxBCx
        X.sigma0
        (X.widthPointB_on_sigma0
          (Geo := Geo) x)
        (X.widthPointC_on_sigma0
          (Geo := Geo) x)

  have hBCySigma0 :
      HilbertLineInPlane
        Geo lBCy X.sigma0 := by

    have hBCy :
        Ne
          (X.widthPointB (Geo := Geo) y)
          (X.widthPointC (Geo := Geo) y) :=
      (hilbert_XI10_directedParallelSegments_nondegenerate
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) y)
        (X.widthPointC (Geo := Geo) y)
        X.B0 X.C0
        hDirBCy).1

    exact
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) y)
        (X.widthPointC (Geo := Geo) y)
        hBCy
        lBCy hByBCy hCyBCy
        X.sigma0
        (X.widthPointB_on_sigma0
          (Geo := Geo) y)
        (X.widthPointC_on_sigma0
          (Geo := Geo) y)

  have hBC0Sigma0 :
      HilbertLineInPlane
        Geo lBC0x X.sigma0 :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      X.B0 X.C0 hBC0
      lBC0x hB0BC0x hC0BC0x
      X.sigma0
      X.ordered.slab.B0_on.2.2
      X.ordered.slab.C0_on.2.2

  have hBCxNeBCy :
      Ne lBCx lBCy := by

    intro hEq

    have hBxy :=
      X.widthPointB_between
        (Geo := Geo)
        x y hxy

    have hBdata :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        X.B0
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) y)
        hBxy

    have hBxBy :
        Ne
          (X.widthPointB (Geo := Geo) x)
          (X.widthPointB (Geo := Geo) y) :=
      hBdata.2.1

    have hByBCx :
        H.OnLine
          (X.widthPointB (Geo := Geo) y)
          lBCx := by
      rw [hEq]
      exact hByBCy

    have hBxByB0 :
        PrimCollinear
          Geo
          (X.widthPointB (Geo := Geo) x)
          (X.widthPointB (Geo := Geo) y)
          X.B0 :=
      PrimCollinearCycle
        Geo
        X.B0
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointB (Geo := Geo) y)
        hBdata.2.2.2.1

    have hB0BCx :
        H.OnLine X.B0 lBCx :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hBxBy
        hBxBCx hByBCx
        hBxByB0

    rcases hParallelBCx_BC0x with
      ⟨_omega,
       _hBCxOmega,
       _hBC0Omega,
       hDis⟩

    exact
      hDis
        ⟨X.B0,
         hB0BCx,
         hB0BC0x⟩

  have hParallelBCx_BCy :
      HilbertSpaceLinesParallel
        Geo lBCx lBCy :=
    hilbert_XI25_spaceLinesParallel_transitive_in_plane_distinct
      (Geo := Geo)
      X.sigma0
      lBCx lBCy lBC0x
      hBCxSigma0
      hBCySigma0
      hBC0Sigma0
      hParallelBCx_BC0x
      hParallelBCy_BC0x
      hBCxNeBCy

  --------------------------------------------------------------------
  -- Put the two line pairs in their section planes and apply XI.15.
  --------------------------------------------------------------------

  have hABxSection :
      HilbertLineInPlane
        Geo lABx
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) x)
      lABx hAxABx hBxABx
      (X.widthSectionPlane
        (Geo := Geo) x)
      (X.widthPointA_on_sectionPlane
        (Geo := Geo) x)
      (X.widthPointB_on_sectionPlane
        (Geo := Geo) x)

  have hBCxSection :
      HilbertLineInPlane
        Geo lBCx
        (X.widthSectionPlane
          (Geo := Geo) x) := by

    have hBCx :
        Ne
          (X.widthPointB (Geo := Geo) x)
          (X.widthPointC (Geo := Geo) x) :=
      (hilbert_XI10_directedParallelSegments_nondegenerate
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        X.B0 X.C0
        hDirBCx).1

    exact
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) x)
        (X.widthPointC (Geo := Geo) x)
        hBCx
        lBCx hBxBCx hCxBCx
        (X.widthSectionPlane
          (Geo := Geo) x)
        (X.widthPointB_on_sectionPlane
          (Geo := Geo) x)
        (X.widthPointC_on_sectionPlane
          (Geo := Geo) x)

  have hABySection :
      HilbertLineInPlane
        Geo lABy
        (X.widthSectionPlane
          (Geo := Geo) y) :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      (X.widthPointA (Geo := Geo) y)
      (X.widthPointB (Geo := Geo) y)
      (X.widthPointA_ne_widthPointB
        (Geo := Geo) y)
      lABy hAyABy hByABy
      (X.widthSectionPlane
        (Geo := Geo) y)
      (X.widthPointA_on_sectionPlane
        (Geo := Geo) y)
      (X.widthPointB_on_sectionPlane
        (Geo := Geo) y)

  have hBCySection :
      HilbertLineInPlane
        Geo lBCy
        (X.widthSectionPlane
          (Geo := Geo) y) := by

    have hBCy :
        Ne
          (X.widthPointB (Geo := Geo) y)
          (X.widthPointC (Geo := Geo) y) :=
      (hilbert_XI10_directedParallelSegments_nondegenerate
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) y)
        (X.widthPointC (Geo := Geo) y)
        X.B0 X.C0
        hDirBCy).1

    exact
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        (X.widthPointB (Geo := Geo) y)
        (X.widthPointC (Geo := Geo) y)
        hBCy
        lBCy hByBCy hCyBCy
        (X.widthSectionPlane
          (Geo := Geo) y)
        (X.widthPointB_on_sectionPlane
          (Geo := Geo) y)
        (X.widthPointC_on_sectionPlane
          (Geo := Geo) y)

  let l1 :
      PlaneLine Geo
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    ⟨lABx, hABxSection⟩

  let l2 :
      PlaneLine Geo
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    ⟨lBCx, hBCxSection⟩

  let m1 :
      PlaneLine Geo
        (X.widthSectionPlane
          (Geo := Geo) y) :=
    ⟨lABy, hABySection⟩

  let m2 :
      PlaneLine Geo
        (X.widthSectionPlane
          (Geo := Geo) y) :=
    ⟨lBCy, hBCySection⟩

  let Bx :
      PlanePoint Geo
        (X.widthSectionPlane
          (Geo := Geo) x) :=
    ⟨X.widthPointB (Geo := Geo) x,
     X.widthPointB_on_sectionPlane
       (Geo := Geo) x⟩

  have hl12raw :
      Ne lABx lBCx := by

    intro hEq

    apply
      X.widthPoints_ABC_noncollinear
        (Geo := Geo) x

    exact
      ⟨lABx,
       hAxABx,
       hBxABx,
       by
         rw [hEq]
         exact hCxBCx⟩

  have hl12 :
      Ne l1 l2 := by

    intro hEq
    apply hl12raw
    exact congrArg Subtype.val hEq

  have hBxL1 :
      H.OnLine Bx.1 l1.1 := by
    simpa [Bx, l1] using hBxABx

  have hBxL2 :
      H.OnLine Bx.1 l2.1 := by
    simpa [Bx, l2] using hBxBCx

  have hNoCommon :
      Not
        (exists omega : SP.Plane,
          HilbertLineInPlane Geo l1.1 omega /\
          HilbertLineInPlane Geo l2.1 omega /\
          HilbertLineInPlane Geo m1.1 omega /\
          HilbertLineInPlane Geo m2.1 omega) := by

    rintro
      ⟨omega,
       hL1omega,
       hL2omega,
       hM1omega,
       hM2omega⟩

    have hAxOmega :
        SP.OnPlane
          (X.widthPointA (Geo := Geo) x)
          omega :=
      hL1omega
        (X.widthPointA (Geo := Geo) x)
        hAxABx

    have hBxOmega :
        SP.OnPlane
          (X.widthPointB (Geo := Geo) x)
          omega :=
      hL1omega
        (X.widthPointB (Geo := Geo) x)
        hBxABx

    have hCxOmega :
        SP.OnPlane
          (X.widthPointC (Geo := Geo) x)
          omega :=
      hL2omega
        (X.widthPointC (Geo := Geo) x)
        hCxBCx

    have hOmegaX :
        omega =
          X.widthSectionPlane
            (Geo := Geo) x :=
      X.widthSectionPlane_unique
        (Geo := Geo)
        x omega
        hAxOmega hBxOmega hCxOmega

    have hAyOmega :
        SP.OnPlane
          (X.widthPointA (Geo := Geo) y)
          omega :=
      hM1omega
        (X.widthPointA (Geo := Geo) y)
        hAyABy

    have hByOmega :
        SP.OnPlane
          (X.widthPointB (Geo := Geo) y)
          omega :=
      hM1omega
        (X.widthPointB (Geo := Geo) y)
        hByABy

    have hCyOmega :
        SP.OnPlane
          (X.widthPointC (Geo := Geo) y)
          omega :=
      hM2omega
        (X.widthPointC (Geo := Geo) y)
        hCyBCy

    have hOmegaY :
        omega =
          X.widthSectionPlane
            (Geo := Geo) y :=
      X.widthSectionPlane_unique
        (Geo := Geo)
        y omega
        hAyOmega hByOmega hCyOmega

    exact
      (X.widthSectionPlanes_ne_of_less
        (Geo := Geo)
        x y hxy)
        (hOmegaX.symm.trans hOmegaY)

  have hParallel :
      HilbertSpacePlanesParallel
        Geo
        (X.widthSectionPlane
          (Geo := Geo) x)
        (X.widthSectionPlane
          (Geo := Geo) y) :=
    euclid_proposition_11_15
      (Geo := Geo)
      (X.widthSectionPlane
        (Geo := Geo) x)
      (X.widthSectionPlane
        (Geo := Geo) y)
      l1 l2
      m1 m2
      Bx
      hBxL1 hBxL2
      hl12
      (by
        simpa [l1, m1]
          using hParallelABx_ABy)
      (by
        simpa [l2, m2]
          using hParallelBCx_BCy)
      hNoCommon

  simpa
    [HilbertSpacePlanesParallel,
     HilbertSpacePlanesParallelIncidence]
    using hParallel


/--
The original base section, followed by widths `x < y`, forms a full
ordered two-slab configuration.
-/
theorem orderedTwoSlabConfiguration_of_width_less
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25OrderedTwoSlabConfiguration
      (Geo := Geo)
      X.pi0
      (X.widthSectionPlane (Geo := Geo) x)
      (X.widthSectionPlane (Geo := Geo) y)
      X.rho0 X.rho1
      X.sigma0 X.sigma1
      X.A0 X.B0 X.C0 X.D0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) x)
      (X.widthPointA (Geo := Geo) y)
      (X.widthPointB (Geo := Geo) y)
      (X.widthPointC (Geo := Geo) y)
      (X.widthPointD (Geo := Geo) y) := by

  have hBetween :=
    X.widthPoints_between_all
      (Geo := Geo)
      x y hxy

  refine
    {
      slab := ?_
      between_A := hBetween.1
      between_B := hBetween.2.1
      between_C := hBetween.2.2.1
      between_D := hBetween.2.2.2
    }

  refine
    {
      pi01_parallel := ?_
      pi12_parallel := ?_
      pi02_parallel := ?_
      rho_parallel := X.ordered.slab.rho_parallel
      sigma_parallel := X.ordered.slab.sigma_parallel

      A0_on := X.ordered.slab.A0_on
      B0_on := X.ordered.slab.B0_on
      C0_on := X.ordered.slab.C0_on
      D0_on := X.ordered.slab.D0_on

      A1_on := ?_
      B1_on := ?_
      C1_on := ?_
      D1_on := ?_

      A2_on := ?_
      B2_on := ?_
      C2_on := ?_
      D2_on := ?_
    }

  · exact
      hilbert_XI25_planesParallelIncidence_symm
        (Geo := Geo)
        (X.widthSectionPlane
          (Geo := Geo) x)
        X.pi0
        (X.widthSectionPlane_parallel_pi0
          (Geo := Geo) x)

  · exact
      X.widthSectionPlanes_parallel_of_less
        (Geo := Geo)
        x y hxy

  · exact
      hilbert_XI25_planesParallelIncidence_symm
        (Geo := Geo)
        (X.widthSectionPlane
          (Geo := Geo) y)
        X.pi0
        (X.widthSectionPlane_parallel_pi0
          (Geo := Geo) y)

  · exact
      And.intro
        (X.widthPointA_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointA_on_rho0
            (Geo := Geo) x)
          (X.widthPointA_on_sigma1
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointB_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointB_on_rho0
            (Geo := Geo) x)
          (X.widthPointB_on_sigma0
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointC_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointC_on_rho1
            (Geo := Geo) x)
          (X.widthPointC_on_sigma0
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointD_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointD_on_rho1
            (Geo := Geo) x)
          (X.widthPointD_on_sigma1
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointA_on_sectionPlane
          (Geo := Geo) y)
        (And.intro
          (X.widthPointA_on_rho0
            (Geo := Geo) y)
          (X.widthPointA_on_sigma1
            (Geo := Geo) y))

  · exact
      And.intro
        (X.widthPointB_on_sectionPlane
          (Geo := Geo) y)
        (And.intro
          (X.widthPointB_on_rho0
            (Geo := Geo) y)
          (X.widthPointB_on_sigma0
            (Geo := Geo) y))

  · exact
      And.intro
        (X.widthPointC_on_sectionPlane
          (Geo := Geo) y)
        (And.intro
          (X.widthPointC_on_rho1
            (Geo := Geo) y)
          (X.widthPointC_on_sigma0
            (Geo := Geo) y))

  · exact
      And.intro
        (X.widthPointD_on_sectionPlane
          (Geo := Geo) y)
        (And.intro
          (X.widthPointD_on_rho1
            (Geo := Geo) y)
          (X.widthPointD_on_sigma1
            (Geo := Geo) y))


/--
Concrete solid-cut witness associated with a strict width comparison
`x < y`.

The left piece has width `x`; the right piece is the interval from
`x` to `y`; the whole solid has width `y`.
-/
noncomputable def solidCutWitness_of_width_less
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x y :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0)
    (hxy :
      HilbertPositiveSegmentLess
        (PlaneGeo Geo X.rho0) x y) :
    HilbertXI25SolidCutWitness
      (Geo := Geo) where

  pi0 := X.pi0
  pi1 :=
    X.widthSectionPlane
      (Geo := Geo) x
  pi2 :=
    X.widthSectionPlane
      (Geo := Geo) y

  rho0 := X.rho0
  rho1 := X.rho1

  sigma0 := X.sigma0
  sigma1 := X.sigma1

  A0 := X.A0
  B0 := X.B0
  C0 := X.C0
  D0 := X.D0

  A1 :=
    X.widthPointA
      (Geo := Geo) x
  B1 :=
    X.widthPointB
      (Geo := Geo) x
  C1 :=
    X.widthPointC
      (Geo := Geo) x
  D1 :=
    X.widthPointD
      (Geo := Geo) x

  A2 :=
    X.widthPointA
      (Geo := Geo) y
  B2 :=
    X.widthPointB
      (Geo := Geo) y
  C2 :=
    X.widthPointC
      (Geo := Geo) y
  D2 :=
    X.widthPointD
      (Geo := Geo) y

  ordered :=
    X.orderedTwoSlabConfiguration_of_width_less
      (Geo := Geo)
      x y hxy

end HilbertXI25SolidCutWitness



------------------------------------------------------------------------
-- XI.25: construct the full width realization from one seed cut
------------------------------------------------------------------------

/-!
The preceding modules have supplied all missing geometry.

A single nontrivial seed cut `X` determines a fixed longitudinal prism
direction and the fixed side planes `rho0,rho1,sigma0,sigma1`.

For every positive width class `x` in `rho0` we now have:

* synchronized endpoints A(x),B(x),C(x),D(x);
* their section plane `pi(x)`;
* `pi0 || pi(x)`;
* all eight required point-plane incidences.

Hence XI.24 applies directly to the slab from the original base
`pi0` to `pi(x)`.  This gives a canonical concrete solid
`widthSolid x`.  Its `rho0` face is `widthBase x`, whose canonical
edge B0--B(x) represents exactly the class `x`.

For `x < y`, the already constructed
`solidCutWitness_of_width_less x y` has exactly these same geometric
endpoints.  Therefore its left piece is XI.Def.10-equivalent to
`widthSolid x`, while its whole is XI.Def.10-equivalent to
`widthSolid y`; likewise for the corresponding `rho0` base faces.

This supplies the previously abstract `cut_of_less` field and closes
`HilbertXI25WidthRealization` from actual synthetic geometry.
-/

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
The slab from the original section `pi0` to the realized section
`pi(x)` is a genuine parallelepiped configuration.
-/
theorem widthParallelepipedConfiguration
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertParallelepipedConfiguration
      (Geo := Geo)
      X.pi0
      (X.widthSectionPlane (Geo := Geo) x)
      X.rho0 X.rho1
      X.sigma0 X.sigma1
      X.A0 X.B0 X.C0 X.D0
      (X.widthPointA (Geo := Geo) x)
      (X.widthPointB (Geo := Geo) x)
      (X.widthPointC (Geo := Geo) x)
      (X.widthPointD (Geo := Geo) x) := by

  refine
    {
      pi_parallel := ?_
      rho_parallel :=
        X.ordered.slab.rho_parallel
      sigma_parallel :=
        X.ordered.slab.sigma_parallel

      A_on := X.ordered.slab.A0_on
      B_on := X.ordered.slab.B0_on
      C_on := X.ordered.slab.C0_on
      D_on := X.ordered.slab.D0_on

      E_on := ?_
      F_on := ?_
      G_on := ?_
      H_on := ?_
    }

  · exact
      hilbert_XI25_planesParallelIncidence_symm
        (Geo := Geo)
        (X.widthSectionPlane
          (Geo := Geo) x)
        X.pi0
        (X.widthSectionPlane_parallel_pi0
          (Geo := Geo) x)

  · exact
      And.intro
        (X.widthPointA_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointA_on_rho0
            (Geo := Geo) x)
          (X.widthPointA_on_sigma1
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointB_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointB_on_rho0
            (Geo := Geo) x)
          (X.widthPointB_on_sigma0
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointC_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointC_on_rho1
            (Geo := Geo) x)
          (X.widthPointC_on_sigma0
            (Geo := Geo) x))

  · exact
      And.intro
        (X.widthPointD_on_sectionPlane
          (Geo := Geo) x)
        (And.intro
          (X.widthPointD_on_rho1
            (Geo := Geo) x)
          (X.widthPointD_on_sigma1
            (Geo := Geo) x))


/--
XI.24 data for the canonical solid of width `x`.
-/
theorem widthXI24
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
      (X.widthPointD (Geo := Geo) x) :=

  euclid_proposition_11_24
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


/--
Canonical concrete parallelepiped representing width `x`.
-/
noncomputable def widthSolid
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
    (X.widthXI24 (Geo := Geo) x)


/--
The canonical base corresponding to width `x` is the `rho0` face of
the canonical solid.
-/
noncomputable def widthBase
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    HilbertParallelogramFace Geo :=

  (X.widthSolid (Geo := Geo) x).rho0


/--
The canonical base has `B0` as its `.b` vertex.
-/
theorem widthBase_b
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    (X.widthBase (Geo := Geo) x).b = X.B0 := by

  rfl


/--
The canonical base has B(x) as its `.c` vertex.
-/
theorem widthBase_c
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    (X.widthBase (Geo := Geo) x).c =
      X.widthPointB (Geo := Geo) x := by

  rfl


/--
The `.b` vertex of the canonical base lies in the fixed carrier plane.
-/
theorem widthBase_b_on_rho0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthBase (Geo := Geo) x).b
      X.rho0 := by

  simpa [widthBase_b] using
    X.ordered.slab.B0_on.2.1


/--
The `.c` vertex of the canonical base lies in the fixed carrier plane.
-/
theorem widthBase_c_on_rho0
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    SP.OnPlane
      (X.widthBase (Geo := Geo) x).c
      X.rho0 := by

  simpa [widthBase_c] using
    X.widthPointB_on_rho0
      (Geo := Geo) x


/--
The canonical base edge represents exactly the prescribed width class.
-/
theorem widthBase_widthClass
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (x :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    hilbert_XI25_widthClass
        (Geo := Geo)
        X.rho0
        (X.widthBase (Geo := Geo) x).b
        (X.widthBase (Geo := Geo) x).c
        (X.widthBase_b_on_rho0
          (Geo := Geo) x)
        (X.widthBase_c_on_rho0
          (Geo := Geo) x)
        (hilbert_XI25_base_width_ne
          (Geo := Geo)
          (X.widthBase (Geo := Geo) x))
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
    ⟨X.B0,
     X.widthBase_b_on_rho0
       (Geo := Geo) x⟩

  let P1 : PlanePoint Geo X.rho0 :=
    ⟨X.widthPointB (Geo := Geo) x,
     X.widthBase_c_on_rho0
       (Geo := Geo) x⟩

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
    rw [← hO, ← hP]
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


/--
The canonical solid and the left piece of the cut generated by `x<y`
are XI.Def.10-equivalent.
-/
theorem widthSolid_equivalent_left_of_less
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
      (X.widthSolid (Geo := Geo) x)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).leftSolid
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25SolidEquivalent
        Geo
        (X.widthSolid (Geo := Geo) x)
        (X.widthSolid (Geo := Geo) x) :=
    hilbertXI25SolidEquivalent_refl_space
      (Geo := Geo)
      (X.widthSolid (Geo := Geo) x)

  simpa
    [widthSolid,
     widthXI24,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.leftSolid,
     HilbertXI25SolidCutWitness.leftXI24,
     hilbertXI24ParallelepipedFaces]
    using hRefl


/--
The canonical base and the left base of the cut generated by `x<y`
are equivalent.
-/
theorem widthBase_equivalent_left_of_less
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
      (X.widthBase (Geo := Geo) x)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).leftBase
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25BaseEquivalent
        Geo
        (X.widthBase (Geo := Geo) x)
        (X.widthBase (Geo := Geo) x) :=
    hilbertXI25BaseEquivalent_refl_space
      (Geo := Geo)
      (X.widthBase (Geo := Geo) x)

  simpa
    [widthBase,
     widthSolid,
     widthXI24,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.leftBase,
     HilbertXI25SolidCutWitness.leftSolid,
     HilbertXI25SolidCutWitness.leftXI24,
     hilbertXI24ParallelepipedFaces,
     HilbertXI25BaseEquivalent]
    using hRefl


/--
The canonical solid of width `y` and the whole solid of the cut
generated by `x<y` are XI.Def.10-equivalent.
-/
theorem widthSolid_equivalent_whole_of_less
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
      (X.widthSolid (Geo := Geo) y)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).wholeSolid
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25SolidEquivalent
        Geo
        (X.widthSolid (Geo := Geo) y)
        (X.widthSolid (Geo := Geo) y) :=
    hilbertXI25SolidEquivalent_refl_space
      (Geo := Geo)
      (X.widthSolid (Geo := Geo) y)

  simpa
    [widthSolid,
     widthXI24,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.wholeSolid,
     HilbertXI25SolidCutWitness.wholeXI24,
     hilbertXI24ParallelepipedFaces]
    using hRefl


/--
The canonical base of width `y` and the whole base of the cut
generated by `x<y` are equivalent.
-/
theorem widthBase_equivalent_whole_of_less
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
      (X.widthBase (Geo := Geo) y)
      ((X.solidCutWitness_of_width_less
        (Geo := Geo) x y hxy).wholeBase
          (Geo := Geo)) := by

  have hRefl :
      HilbertXI25BaseEquivalent
        Geo
        (X.widthBase (Geo := Geo) y)
        (X.widthBase (Geo := Geo) y) :=
    hilbertXI25BaseEquivalent_refl_space
      (Geo := Geo)
      (X.widthBase (Geo := Geo) y)

  simpa
    [widthBase,
     widthSolid,
     widthXI24,
     solidCutWitness_of_width_less,
     HilbertXI25SolidCutWitness.wholeBase,
     HilbertXI25SolidCutWitness.wholeSolid,
     HilbertXI25SolidCutWitness.wholeXI24,
     hilbertXI24ParallelepipedFaces,
     HilbertXI25BaseEquivalent]
    using hRefl


/--
Every strict width comparison is realized by one actual aligned proper
part witness between the canonical bases and canonical solids.
-/
theorem alignedProperPartWitness_of_width_less
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
      (X.widthBase (Geo := Geo) x)
      (X.widthSolid (Geo := Geo) x)
      (X.widthBase (Geo := Geo) y)
      (X.widthSolid (Geo := Geo) y) := by

  let cut :=
    X.solidCutWitness_of_width_less
      (Geo := Geo)
      x y hxy

  refine
    ⟨cut, ?_, ?_, ?_⟩

  · left

    exact
      And.intro
        (X.widthBase_equivalent_left_of_less
          (Geo := Geo)
          x y hxy)
        (X.widthSolid_equivalent_left_of_less
          (Geo := Geo)
          x y hxy)

  · exact
      X.widthBase_equivalent_whole_of_less
        (Geo := Geo)
        x y hxy

  · exact
      X.widthSolid_equivalent_whole_of_less
        (Geo := Geo)
        x y hxy


/--
A seed nontrivial cut canonically generates the full geometric
realization of every positive width in its carrier plane.
-/
noncomputable def toWidthRealization
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo)) :
    HilbertXI25WidthRealization
      (Geo := Geo) X.rho0 where

  baseRep :=
    X.widthBase
      (Geo := Geo)

  solidRep :=
    X.widthSolid
      (Geo := Geo)

  solid_rho0 := by
    intro x
    rfl

  base_b_on := by
    intro x
    exact
      X.widthBase_b_on_rho0
        (Geo := Geo) x

  base_c_on := by
    intro x
    exact
      X.widthBase_c_on_rho0
        (Geo := Geo) x

  width_spec := by
    intro x
    exact
      X.widthBase_widthClass
        (Geo := Geo) x

  cut_of_less := by
    intro x y hxy

    exact
      X.alignedProperPartWitness_of_width_less
        (Geo := Geo)
        x y hxy


/--
The faithful-family V.Def.5 result is now available directly from one
seed cut, with no abstract comparison field left to assume.
-/
theorem eudoxusProportion_from_seed_cut
    (X : HilbertXI25SolidCutWitness
      (Geo := Geo))
    (a b :
      HilbertXI25WidthClass
        (Geo := Geo) X.rho0) :
    EudoxusProportionBetween
      ((X.toWidthRealization
        (Geo := Geo)).toComparisonFaithfulFamily
          (Geo := Geo)).baseEudoxusMagnitude
      ((X.toWidthRealization
        (Geo := Geo)).toComparisonFaithfulFamily
          (Geo := Geo)).solidEudoxusMagnitude
      a b a b := by

  exact
    (X.toWidthRealization
      (Geo := Geo)).eudoxusProportion
        (Geo := Geo)
        a b

end HilbertXI25SolidCutWitness



end Geometry

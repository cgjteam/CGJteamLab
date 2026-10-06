import CGJteamLab.Proposition11_27
import CGJteamLab.Wyler.Proposition11_26

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.27 - Hilbert-Wyler route, test01

In dimension three, Wyler is used here as an incidence language/front end.

The metric, order, proportion, similarity, and Euclidean parallel-plane
machinery remain the already established Hilbert 3D core.  No alternative
metric theory is introduced.

The direct XI.27 theorem is already parametric in
`HilbertSpaceIncidence`.  Therefore the first test is deliberately minimal:
route the common incidence fields through `HilbertWylerAxioms`, retain the
genuinely 3D residual Hilbert incidence fields, and reuse the complete
production proof.
-/

/--
XI.27 with the common spatial incidence fields explicitly routed through
the Hilbert-Wyler package.

This is the 3D Hilbert-Wyler formulation: Wyler supplies the incidence
language, while the established Hilbert order, congruence, proportion,
similarity, and Euclidean parallel structure are reused unchanged.
-/
theorem euclid_proposition_11_27_wyler_core
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    [W : HilbertWylerAxioms Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)
    (A0 B0 : Geo.Point)
    (hA0B0 : Ne A0 B0) :
    exists K J : Geo.Point,
    exists tpi0 tpi1 trho0 trho1 tsigma0 tsigma1 : S.Plane,
    exists TD TE TG TH : Geo.Point,
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        tpi0 tpi1 trho0 trho1 tsigma0 tsigma1
        B0 A0 K TD TE J TG TH /\
      HilbertXI9SimilarParallelepiped
        (HilbertSpaceFaceCornerSimilarFace
          (Geo := Geo))
        (hilbertXI27FaceCorners
          (Geo := Geo)
          A B C D E F G Hpt)
        (hilbertXI27FaceCorners
          (Geo := Geo)
          B0 A0 K TD TE J TG TH) := by

  let HSIw : HilbertSpaceIncidence Geo :=
    hilbertSpaceIncidence_routed_through_wyler
      (Geo := Geo) HSI W

  exact
    euclid_proposition_11_27
      (Geo := Geo)
      (HSI := HSIw)
      (HSO := HSO)
      (HSC := HSC)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg
      A0 B0
      hA0B0


/--
Hilbert 3D public corollary.

The Hilbert-Wyler incidence package is derived from the existing Hilbert
three-space by `hilbertWylerAxioms_of_hilbert3D`, so XI.27 acquires no new
public geometric assumption.
-/
theorem euclid_proposition_11_27_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi0 pi1 rho0 rho1 sigma0 sigma1 : S.Plane)
    (A B C D E F G Hpt : Geo.Point)
    (hCfg :
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        pi0 pi1 rho0 rho1 sigma0 sigma1
        A B C D E F G Hpt)
    (A0 B0 : Geo.Point)
    (hA0B0 : Ne A0 B0) :
    exists K J : Geo.Point,
    exists tpi0 tpi1 trho0 trho1 tsigma0 tsigma1 : S.Plane,
    exists TD TE TG TH : Geo.Point,
      HilbertParallelepipedConfiguration
        (Geo := Geo)
        tpi0 tpi1 trho0 trho1 tsigma0 tsigma1
        B0 A0 K TD TE J TG TH /\
      HilbertXI9SimilarParallelepiped
        (HilbertSpaceFaceCornerSimilarFace
          (Geo := Geo))
        (hilbertXI27FaceCorners
          (Geo := Geo)
          A B C D E F G Hpt)
        (hilbertXI27FaceCorners
          (Geo := Geo)
          B0 A0 K TD TE J TG TH) := by

  let W : HilbertWylerAxioms Geo :=
    hilbertWylerAxioms_of_hilbert3D
      (Geo := Geo)

  exact
    euclid_proposition_11_27_wyler_core
      (Geo := Geo)
      (W := W)
      pi0 pi1 rho0 rho1 sigma0 sigma1
      A B C D E F G Hpt
      hCfg
      A0 B0
      hA0B0

end Geometry

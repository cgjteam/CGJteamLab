import CGJteamLab.HilbertWylerE4Local3D
import CGJteamLab.Coxeter.E4Incidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Compatibility bridge for local 3D incidence in E4 hyperplanes

The historical Coxeter E4 development expects the class

    Hilbert4DHyperplaneLocal3DIncidence.

Under the Hilbert-Wyler foundation this class is no longer an independent
axiom. It is reconstructed from

    HilbertWylerAxioms + E4Dimension.

No new axiom is introduced.
-/

@[instance_reducible]
local instance hilbertWylerE4Primitive_local3DCompatibility
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  hilbertWylerE4Primitive (Geo := Geo)


local instance hilbertWylerDimensionFreeIncidence_local3DCompatibility
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo] :
    HilbertDimensionFreeIncidence Geo :=
  hilbertDimensionFreeIncidence_of_hilbertWyler
    (Geo := Geo)


local instance hilbertWylerOldHyperplaneIncidenceCore_local
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  hilbertWyler_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance hilbertWylerAmbientIncidence_local3DCompatibility
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


/--
The historical local-3D hyperplane incidence class is a theorem of

    HilbertWylerAxioms + E4Dimension.

Thus its three fields are derived:

* plane closure inside a hyperplane;
* local Hilbert I.7;
* existence of four noncoplanar points in every hyperplane.
-/
theorem hilbertWyler_e4_implies_oldHyperplaneLocal3DIncidence
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo where

  plane_in_hyperplane := by
    intro A B C hABC
      pi hApi hBpi hCpi
      Sigma hASigma hBSigma hCSigma
      X hXpi

    exact
      e4Hyperplane_plane_in
        (Geo := Geo)
        Sigma
        A B C
        hASigma hBSigma hCSigma
        hABC
        pi
        hApi hBpi hCpi
        X hXpi

  plane_second_common_point_in_hyperplane := by
    intro Sigma
      pi tau
      hPiSigma hTauSigma
      hPiTau
      P hPpi hPtau

    exact
      hilbertWyler_e4_plane_second_common_point_in_hyperplane
        (Geo := Geo)
        Sigma
        pi tau
        hPiSigma hTauSigma
        hPiTau
        P
        hPpi hPtau

  four_noncoplanar_on_hyperplane := by
    intro Sigma

    exact
      hilbertWyler_e4_four_noncoplanar_on_hyperplane
        (Geo := Geo)
        Sigma

end Geometry

-- SalasE4Local3DCompatibility FIX1 - 2026-09-11
import CGJteamLab.SalasE4Local3D
import CGJteamLab.Coxeter.E4Incidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Compatibility bridge for local 3D incidence in E4 hyperplanes

The historical Coxeter E4 development expects the class

    Hilbert4DHyperplaneLocal3DIncidence.

Under the new foundation this class is no longer an independent axiom.
It is reconstructed from

    SalasIncidence + E4Dimension.

The intermediate historical interfaces are installed only locally in
this module.  No new axiom is introduced.
-/

@[instance_reducible]
local instance salasE4Primitive_local3DCompatibility
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasDimensionFreeIncidence_local3DCompatibility
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasOldHyperplaneIncidenceCore_local
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


/--
The historical local-3D hyperplane incidence class is a theorem of

    SalasIncidence + E4Dimension.

Thus its three fields are derived:

* plane closure inside a hyperplane;
* local Hilbert I.7;
* existence of four noncoplanar points in every hyperplane.
-/
theorem salas_e4_implies_oldHyperplaneLocal3DIncidence
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
      salas_e4_plane_second_common_point_in_hyperplane
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
      salas_e4_four_noncoplanar_on_hyperplane
        (Geo := Geo)
        Sigma

end Geometry

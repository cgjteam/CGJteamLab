import CGJteamLab.E4HyperplaneCore
import CGJteamLab.HilbertWylerCompatibility
import CGJteamLab.Coxeter.E4Incidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Compatibility bridge from derived Hilbert-Wyler E4 hyperplanes
# to the old E4 API

The current Coxeter E4 development was written against the historical
interfaces

    Hilbert4DPrimitive
    Hilbert4DHyperplaneIncidenceCore.

The new foundation does not assume primitive hyperplanes. Instead,
hyperplanes are derived as proper generated 3-flats from

    HilbertWylerAxioms + E4Dimension.

This module provides a one-way compatibility bridge:

    HilbertWylerAxioms + E4Dimension
        -> derived E4Hyperplane
        -> old Hilbert4DPrimitive interface
        -> old Hilbert4DHyperplaneIncidenceCore interface.

No new axiom is introduced here.
-/

/--
The old E4 primitive signature realized by derived E4 hyperplanes.

The inherited plane structure is exactly the already available ambient
`HilbertSpacePrimitive`. The old primitive hyperplane type is interpreted
as `E4Hyperplane Geo`.
-/
@[instance_reducible]
def hilbertWylerE4Primitive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo where

  toHilbertSpacePrimitive := S

  Hyperplane :=
    E4Hyperplane Geo

  OnHyperplane :=
    fun P Sigma =>
      E4OnHyperplane Geo P Sigma


/--
Under the derived realization, old hyperplane membership is exactly
`E4OnHyperplane`.
-/
theorem hilbertWylerE4Primitive_onHyperplane_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (P : Geo.Point)
    (Sigma : E4Hyperplane Geo) :
    (hilbertWylerE4Primitive (Geo := Geo)).OnHyperplane P Sigma <->
      E4OnHyperplane Geo P Sigma := by

  rfl


/--
Local typeclass view of the derived E4 primitive.

This is deliberately local to this module because the historical E4 API
states auxiliary notions through typeclass inference on
`Hilbert4DPrimitive`.
-/
local instance hilbertWylerE4Primitive_local
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  hilbertWylerE4Primitive (Geo := Geo)


/--
Local typeclass view of the old dimension-free compatibility package.

This is not a new assumption. It is constructed from
`HilbertWylerAxioms` by the compatibility theorem.
-/
local instance hilbertWylerDimensionFreeIncidence_local
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo] :
    HilbertDimensionFreeIncidence Geo :=
  hilbertDimensionFreeIncidence_of_hilbertWyler
    (Geo := Geo)


/--
The complete historical E4 hyperplane-incidence core is a theorem of

    HilbertWylerAxioms + E4Dimension

when the old primitive signature is interpreted by
`hilbertWylerE4Primitive` and the old dimension-free package is
interpreted by `hilbertDimensionFreeIncidence_of_hilbertWyler`.
-/
theorem hilbertWyler_e4_implies_oldHyperplaneIncidenceCore
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo] :
    @Hilbert4DHyperplaneIncidenceCore
      Geo
      H
      HP
      (hilbertWylerE4Primitive (Geo := Geo))
      (hilbertDimensionFreeIncidence_of_hilbertWyler
        (Geo := Geo)) where

  hyperplane_through := by
    intro A B C D hNoncoplanar
    exact
      hilbertWyler_e4_hyperplane_through_noncoplanar4
        (Geo := Geo)
        A B C D
        hNoncoplanar

  point_on_each_hyperplane := by
    intro Sigma
    exact
      e4Hyperplane_point_exists
        (Geo := Geo)
        Sigma

  hyperplane_unique := by
    intro A B C D hNoncoplanar
      Sigma Tau
      hASigma hBSigma hCSigma hDSigma
      hATau hBTau hCTau hDTau

    exact
      hilbertWyler_e4_hyperplane_unique_noncoplanar4
        (Geo := Geo)
        A B C D
        hNoncoplanar
        Sigma Tau
        hASigma hBSigma hCSigma hDSigma
        hATau hBTau hCTau hDTau

  line_in_hyperplane := by
    intro A B hAB l hAl hBl
      Sigma hASigma hBSigma
      X hXl

    exact
      e4Hyperplane_line_in
        (Geo := Geo)
        Sigma
        A B
        hASigma hBSigma
        hAB
        l
        hAl hBl
        X hXl

  five_nonhyperplanar := by
    rcases
        e4Dimension_exists_five_nonhyperplanar
          (Geo := Geo) with
      ⟨A, B, C, D, E, hFive⟩

    refine
      ⟨A, B, C, D, E, ?_⟩

    intro hOldHyperplanar

    rcases hOldHyperplanar with
      ⟨Sigma,
       hASigma,
       hBSigma,
       hCSigma,
       hDSigma,
       hESigma⟩

    exact
      hFive
        ⟨Sigma,
         hASigma,
         hBSigma,
         hCSigma,
         hDSigma,
         hESigma⟩

end Geometry

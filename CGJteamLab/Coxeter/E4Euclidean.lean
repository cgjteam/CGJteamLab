import CGJteamLab.Coxeter.E4Congruence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hierarchy repair: Group IV

Test49 recovered the complete local Group III structure in every fixed
E4 hyperplane without using the old ambient 3D typeclasses.

The last Hilbert layer needed by the current Euclidean API is Group IV.

As with Pasch, the parallel axiom is intrinsically plane-local.  The
mathematical content is dimension-independent, but the old
`HilbertSpaceEuclidean Geo` signature depends on the old ambient
`HilbertSpaceIncidence Geo`, `HilbertSpaceOrder Geo`, and
`HilbertSpaceCongruence Geo`.

This file introduces the corrected E4 ambient Group IV interface and
reconstructs the old `HilbertSpaceEuclidean` API locally inside each
hyperplane.
-/

/--
Hilbert Group IV for genuine ambient E4.

The axiom is explicitly restricted to one ambient 2-plane.
-/
class Hilbert4DAmbientEuclidean
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo] : Prop where

  parallel_unique_in_plane :
    forall pi : Q.toHilbertSpacePrimitive.Plane,
      forall l : Geo.Line,
        HilbertLineInPlane Geo l pi ->
        forall A : Geo.Point,
          Q.toHilbertSpacePrimitive.OnPlane A pi ->
          Not (H.OnLine A l) ->
          forall b c : Geo.Line,
            HilbertLineInPlane Geo b pi ->
            HilbertLineInPlane Geo c pi ->
            H.OnLine A b ->
            HilbertLinesDisjoint Geo b l ->
            H.OnLine A c ->
            HilbertLinesDisjoint Geo c l ->
            b = c

/--
Two local lines meet iff their ambient carrier lines meet.
-/
theorem hyperplaneGeo4_linesMeet_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (l m : HyperplaneLine4 Geo Sigma) :
    HilbertLinesMeet
        (HyperplaneGeo4 Geo Sigma) l m <->
      HilbertLinesMeet
        Geo l.1 m.1 := by

  constructor

  · rintro ⟨P, hPl, hPm⟩
    exact ⟨P.1, hPl, hPm⟩

  · rintro ⟨P, hPl, hPm⟩

    have hPSigma :
        Q.OnHyperplane P Sigma :=
      l.2 P hPl

    exact
      ⟨⟨P, hPSigma⟩, hPl, hPm⟩

/--
Local line disjointness is exactly ambient carrier-line disjointness.
-/
theorem hyperplaneGeo4_linesDisjoint_iff_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (l m : HyperplaneLine4 Geo Sigma) :
    HilbertLinesDisjoint
        (HyperplaneGeo4 Geo Sigma) l m <->
      HilbertLinesDisjoint
        Geo l.1 m.1 := by

  unfold HilbertLinesDisjoint

  rw [
    hyperplaneGeo4_linesMeet_iff_ambient_corrected
      (Geo := Geo) Sigma l m
  ]

/--
Every fixed E4 hyperplane inherits the complete old spatial Euclidean
parallel API from the corrected E4 ambient Group IV interface.

No old ambient 3D typeclass is assumed.
-/
instance hyperplaneGeo4HilbertSpaceEuclidean_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [H4E : Hilbert4DAmbientEuclidean Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceEuclidean
      (HyperplaneGeo4 Geo Sigma) where

  parallel_unique_in_plane := by
    intro pi l hlpi A
      hApi hAl
      b c hbpi hcpi
      hAb hbl
      hAc hcl

    have hlpiAmbient :
        HilbertLineInPlane Geo l.1 pi.1 :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Sigma l pi hlpi

    have hbpiAmbient :
        HilbertLineInPlane Geo b.1 pi.1 :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Sigma b pi hbpi

    have hcpiAmbient :
        HilbertLineInPlane Geo c.1 pi.1 :=
      hyperplaneGeo4_lineInPlane_to_ambient_corrected
        (Geo := Geo)
        Sigma c pi hcpi

    have hblAmbient :
        HilbertLinesDisjoint Geo b.1 l.1 :=
      (hyperplaneGeo4_linesDisjoint_iff_ambient_corrected
        (Geo := Geo)
        Sigma b l).mp hbl

    have hclAmbient :
        HilbertLinesDisjoint Geo c.1 l.1 :=
      (hyperplaneGeo4_linesDisjoint_iff_ambient_corrected
        (Geo := Geo)
        Sigma c l).mp hcl

    have hbc :
        b.1 = c.1 :=
      Hilbert4DAmbientEuclidean.parallel_unique_in_plane
        (Geo := Geo)
        pi.1
        l.1
        hlpiAmbient
        A.1
        hApi
        hAl
        b.1 c.1
        hbpiAmbient
        hcpiAmbient
        hAb
        hblAmbient
        hAc
        hclAmbient

    exact Subtype.ext hbc

/--
Critical sanity check: the entire old 3D Hilbert package is available
inside every fixed E4 hyperplane, while the ambient E4 space uses only
the corrected E4 hierarchy.
-/
example
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceEuclidean
      (HyperplaneGeo4 Geo Sigma) := by

  infer_instance

end Geometry

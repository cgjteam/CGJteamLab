import CGJteamLab.Wyler.HilbertWylerPlanes

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler perpendicular planes

Synthetic plane-plane perpendicularity for the Wyler path.

The definition follows Euclid XI.Def.4 rather than replacing it by the
modern equivalent statement "one plane contains a normal to the other".
That distinction is essential for Proposition XI.18: otherwise XI.18
would become true by definition and its geometric content would vanish.

The relation is intentionally directed.  Symmetry, if needed later,
should be proved as a theorem.
-/

/--
`rho` is perpendicular to `pi` along the common section line `s` when:

* `s` lies in both planes;
* `s` is exactly their common point set;
* every line `g` of `rho` perpendicular to `s` at a point `F` is
  perpendicular to the whole plane `pi` at `F`.

This is the direct synthetic content of Euclid XI.Def.4.
-/
def HilbertSpacePlanesPerpendicularAlong
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (rho pi : S.Plane)
    (s : Geo.Line) : Prop :=
  HilbertLineInPlane Geo s rho /\
  HilbertLineInPlane Geo s pi /\
  (forall X : Geo.Point,
    (S.OnPlane X rho /\ S.OnPlane X pi) <->
      H.OnLine X s) /\
  forall (g : Geo.Line) (F : Geo.Point),
    HilbertLineInPlane Geo g rho ->
    HilbertLinesPerpendicularAt Geo g s F ->
    HilbertLinePerpendicularPlaneAt Geo g pi F

/--
Two distinct planes are perpendicular when they have a common section
line satisfying Euclid XI.Def.4.

The order of arguments is significant: `rho` is the plane in which the
lines perpendicular to the common section are tested, while `pi` is the
plane to which those lines must be perpendicular.
-/
def HilbertSpacePlanesPerpendicular
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (rho pi : S.Plane) : Prop :=
  Ne rho pi /\
  exists s : Geo.Line,
    HilbertSpacePlanesPerpendicularAlong Geo rho pi s

/-- Perpendicular planes are distinct. -/
theorem hilbertSpacePlanesPerpendicular_ne
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {rho pi : S.Plane}
    (h : HilbertSpacePlanesPerpendicular Geo rho pi) :
    Ne rho pi := by
  exact h.1

/-- A perpendicular pair has a section line witnessing XI.Def.4. -/
theorem hilbertSpacePlanesPerpendicular_exists_section
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {rho pi : S.Plane}
    (h : HilbertSpacePlanesPerpendicular Geo rho pi) :
    exists s : Geo.Line,
      HilbertSpacePlanesPerpendicularAlong Geo rho pi s := by
  exact h.2

/-- The witnessing section lies in the first plane. -/
theorem hilbertSpacePlanesPerpendicularAlong_section_in_left
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {rho pi : S.Plane}
    {s : Geo.Line}
    (h : HilbertSpacePlanesPerpendicularAlong Geo rho pi s) :
    HilbertLineInPlane Geo s rho := by
  exact h.1

/-- The witnessing section lies in the second plane. -/
theorem hilbertSpacePlanesPerpendicularAlong_section_in_right
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {rho pi : S.Plane}
    {s : Geo.Line}
    (h : HilbertSpacePlanesPerpendicularAlong Geo rho pi s) :
    HilbertLineInPlane Geo s pi := by
  exact h.2.1

/-- The witnessing section is exactly the intersection of the two planes. -/
theorem hilbertSpacePlanesPerpendicularAlong_section_exact
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {rho pi : S.Plane}
    {s : Geo.Line}
    (h : HilbertSpacePlanesPerpendicularAlong Geo rho pi s) :
    forall X : Geo.Point,
      (S.OnPlane X rho /\ S.OnPlane X pi) <->
        H.OnLine X s := by
  exact h.2.2.1

/--
The operative XI.Def.4 elimination rule.

A line in the first plane, perpendicular to the common section, is
perpendicular to the second plane.
-/
theorem hilbertSpacePlanesPerpendicularAlong_line_perpendicular_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {rho pi : S.Plane}
    {s g : Geo.Line}
    {F : Geo.Point}
    (h : HilbertSpacePlanesPerpendicularAlong Geo rho pi s)
    (hgrho : HilbertLineInPlane Geo g rho)
    (hPerp : HilbertLinesPerpendicularAt Geo g s F) :
    HilbertLinePerpendicularPlaneAt Geo g pi F := by
  exact h.2.2.2 g F hgrho hPerp

end Geometry

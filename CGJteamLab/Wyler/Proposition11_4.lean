import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.4.

If a line `l` is perpendicular at `O` to two distinct lines `m,n`
of the plane `pi`, then `l` is perpendicular to the whole plane `pi`.

The Wyler metric decomposition is explicit:

  l perp m at O  ->  l != m and O lies on l,m,
  l perp n at O  ->  l != n and O lies on l,n,

and these normalized incidence/nondegeneracy data are passed to the
synthetic metric core proving perpendicularity to the plane.
-/
theorem euclid_proposition_11_4
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (m n : PlaneLine Geo pi)
    (l : Geo.Line)
    (O : PlanePoint Geo pi)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m.1 O.1)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n.1 O.1) :
    HilbertLinePerpendicularPlaneAt Geo l pi O.1 := by

  /-
  The two line-line perpendicularities are nondegenerate.
  -/
  have hlm : Ne l m.1 :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l m.1 O.1
      hPerpM

  have hln : Ne l n.1 :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l n.1 O.1
      hPerpN

  /-
  Extract the common-point incidence carried by the two
  perpendicularity objects.
  -/
  have hOl : H.OnLine O.1 l :=
    hPerpM.1

  have hOm : H.OnLine O.1 m.1 :=
    hPerpM.2.1

  have hOn : H.OnLine O.1 n.1 :=
    hPerpN.2.1

  /-
  The reusable synthetic metric engine now has exactly the data it needs:

      m != n,
      l != m,
      l != n,
      O in l,m,n,
      l perp m at O,
      l perp n at O.

  It concludes that l is perpendicular to the whole plane pi at O.
  -/
  exact
    hilbert_XI4_line_perpendicular_plane_core
      (Geo := Geo)
      pi m n l O
      hmn
      hlm hln
      hOl hOm hOn
      hPerpM hPerpN

end Geometry

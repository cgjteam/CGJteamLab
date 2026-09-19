import CGJteamLab.Hilbert3DInterface
import CGJteamLab.HilbertAngleSumComparison

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A proper trihedral configuration with vertex `O` and three rays
`OA`, `OB`, `OC`.

The three face angles are required to be proper, and the four points
`O, A, B, C` are not contained in one plane.

This is the neutral Hilbert 3D language intended for Euclid XI.20.
It contains no numerical angle measure.
-/
def HilbertTrihedralConfiguration
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point) : Prop :=
  Not (PrimCollinear Geo A O B) /\
  Not (PrimCollinear Geo B O C) /\
  Not (PrimCollinear Geo C O A) /\
  Not
    (exists pi : S.Plane,
      S.OnPlane O pi /\
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi)


/--
The three cyclic inequalities asserted by Euclid XI.20 for the
trihedral configuration `O; A, B, C`.

They are written in the cyclic form

    AOB + BOC > AOC,
    BOC + COA > BOA,
    COA + AOB > COB.
-/
def HilbertTrihedralAngleInequalities
    [HilbertIncidence Geo]
    (O A B C : Geo.Point) : Prop :=
  HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      B O C
      A O C
  /\
  HilbertTwoAnglesGreaterThanAngle
      Geo
      B O C
      C O A
      B O A
  /\
  HilbertTwoAnglesGreaterThanAngle
      Geo
      C O A
      A O B
      C O B


------------------------------------------------------------------------
-- Accessors for the trihedral configuration
------------------------------------------------------------------------

theorem hilbertTrihedralConfiguration_face_AB
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not (PrimCollinear Geo A O B) :=
  h.1


theorem hilbertTrihedralConfiguration_face_BC
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not (PrimCollinear Geo B O C) :=
  h.2.1


theorem hilbertTrihedralConfiguration_face_CA
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not (PrimCollinear Geo C O A) :=
  h.2.2.1


theorem hilbertTrihedralConfiguration_not_coplanar
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not
      (exists pi : S.Plane,
        S.OnPlane O pi /\
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi) :=
  h.2.2.2


end Geometry

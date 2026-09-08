import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.3.

If two distinct planes have a common point, then their intersection is a
straight line.

Wyler form:

  carrier(pi) inter carrier(rho) = carrier(l).

The classical pointwise statement is recovered directly from this meet
identity.
-/
theorem euclid_proposition_11_3
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo l rho /\
      forall X : Geo.Point,
        (S.OnPlane X pi /\ S.OnPlane X rho) <->
        H.OnLine X l := by

  cases
      hilbertPlaneCarrier3D_inter_eq_lineCarrier
        (Geo := Geo)
        pi rho hneq
        A hApi hArho with
  | intro l hData =>
      have hAl : H.OnLine A l :=
        hData.1

      have hlpi :
          HilbertLineInPlane Geo l pi :=
        hData.2.1

      have hlrho :
          HilbertLineInPlane Geo l rho :=
        hData.2.2.1

      have hMeet :
          Set.inter
              (HilbertPlaneCarrier3D Geo pi)
              (HilbertPlaneCarrier3D Geo rho) =
            HilbertLineCarrier3D Geo l :=
        hData.2.2.2

      have hPointwise :
          forall X : Geo.Point,
            (S.OnPlane X pi /\ S.OnPlane X rho) <->
            H.OnLine X l := by
        intro X
        change
          Set.inter
              (HilbertPlaneCarrier3D Geo pi)
              (HilbertPlaneCarrier3D Geo rho) X <->
            HilbertLineCarrier3D Geo l X
        rw [hMeet]

      exact
        Exists.intro l
          (And.intro hAl
            (And.intro hlpi
              (And.intro hlrho hPointwise)))

end Geometry

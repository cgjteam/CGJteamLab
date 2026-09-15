import CGJteamLab.Wyler.Proposition11_20
import CGJteamLab.HilbertThreeAnglesFourRight

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.21 -- Hilbert-Wyler route

The three plane angles containing a proper trihedral solid angle are
together less than four right angles.

This proof is independent of the Hilbert-space proof in
`CGJteamLab.Proposition11_21`.

It uses the same neutral target

    HilbertTrihedralAnglesLessThanFourRightAngles

from `HilbertThreeAnglesFourRight.lean`, but reconstructs the spatial
step from the Hilbert-Wyler incidence core.

The proof needs only:

* planar Hilbert order and congruence;
* two ray extensions;
* the Wyler proof of XI.20;
* vertical angles;
* `HilbertWylerAxioms.line_in_plane`.

It does not use Wyler I.7, Smith I.5, exchange, or an ambient dimension
bound.
-/

/--
Local compatibility adapter exposing the plane-incidence parent already
contained in `HilbertCongruence`.

This introduces no new axiom and does not alter the global typeclass
graph.
-/
local instance hilbertPlaneIncidence_of_hilbertCongruence_XI21
    [H : HilbertIncidence Geo]
    [HC : HilbertCongruence Geo] :
    HilbertPlaneIncidence Geo :=
  HC.toHilbertOrder.toHilbertPlaneIncidence


/--
Construct the two opposite rays used by the complement representation:

    C - A - X,
    D - A - Y.
-/
theorem hilbert_XI21_supplement_rays_exist_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo A B C D) :
    exists X Y : Geo.Point,
      Geo.Between C A X /\
      Geo.Between D A Y := by

  have hBAC :
      Not (PrimCollinear Geo B A C) :=
    hTri.1

  have hCAD :
      Not (PrimCollinear Geo C A D) :=
    hTri.2.1

  have hCA : Ne C A :=
    hilbert_noncollinear_ne_first
      Geo C A B
      (by
        intro h
        exact
          hBAC
            (PrimCollinearSymm
              Geo C A B h))

  have hDA : Ne D A :=
    hilbert_noncollinear_ne_first
      Geo D A C
      (by
        intro h
        exact
          hCAD
            (PrimCollinearSymm
              Geo D A C h))

  rcases
      HilbertOrder.between_extension
        C A hCA
    with
    ⟨X, hCAX⟩

  rcases
      HilbertOrder.between_extension
        D A hDA
    with
    ⟨Y, hDAY⟩

  exact
    ⟨X,
      Y,
      hCAX,
      hDAY⟩


/--
Replacing ray AC by its opposite ray AX preserves the proper trihedral
configuration in the Hilbert-Wyler route.

The only ambient incidence step is:

    A,X lie in pi
    C,A,X are collinear
    ---------------------
    C lies in pi.

This uses only the common Hilbert-Wyler `line_in_plane` clause.
-/
theorem hilbert_XI21_trihedral_opposite_middle_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    [W : HilbertWylerAxioms Geo]
    (A B C D X : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo A B C D)
    (hCAX :
      Geo.Between C A X) :
    HilbertTrihedralConfiguration
      Geo A B X D := by

  have hCAXdata :=
    HilbertOrder.between_incidence
      C A X hCAX

  have hAX : Ne A X :=
    hCAXdata.2.1

  have hCAXcol :
      PrimCollinear Geo C A X :=
    hCAXdata.2.2.2.1

  have hAXC :
      PrimCollinear Geo A X C :=
    PrimCollinearCycle
      Geo C A X hCAXcol

  have hBAX :
      Not (PrimCollinear Geo B A X) := by
    intro hBAXcol

    have hBACcol :
        PrimCollinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo
        B A X C
        hAX
        hBAXcol
        hAXC

    exact hTri.1 hBACcol

  have hXAD :
      Not (PrimCollinear Geo X A D) := by
    intro hXADcol

    have hAXD :
        PrimCollinear Geo A X D :=
      PrimCollinearSwap
        Geo X A D hXADcol

    have hCADcol :
        PrimCollinear Geo C A D :=
      hilbert_primCollinear_trans
        Geo
        C A X D
        hAX
        hCAXcol
        hAXD

    exact hTri.2.1 hCADcol

  have hDAB :
      Not (PrimCollinear Geo D A B) :=
    hTri.2.2.1

  have hNoncoplanar :
      Not
        (exists pi : S.Plane,
          S.OnPlane A pi /\
          S.OnPlane B pi /\
          S.OnPlane X pi /\
          S.OnPlane D pi) := by

    intro hCop

    rcases hCop with
      ⟨pi,
        hApi,
        hBpi,
        hXpi,
        hDpi⟩

    rcases
        HilbertPlaneIncidence.line_through
          A X hAX
      with
      ⟨l,
        hAl,
        hXl⟩

    have hCl :
        HilbertIncidence.OnLine C l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAX
        hAl
        hXl
        hAXC

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      W.line_in_plane
        A X hAX
        l hAl hXl
        pi hApi hXpi

    have hCpi :
        S.OnPlane C pi :=
      hlpi C hCl

    exact
      hTri.2.2.2
        ⟨pi,
          hApi,
          hBpi,
          hCpi,
          hDpi⟩

  exact
    ⟨hBAX,
      hXAD,
      hDAB,
      hNoncoplanar⟩


/--
Reorder A;B,X,D as A;D,X,B.

This is purely structural and uses no ambient incidence axiom.
-/
theorem hilbert_XI21_trihedral_reorder_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (A B X D : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo A B X D) :
    HilbertTrihedralConfiguration
      Geo A D X B := by

  have hDAX :
      Not (PrimCollinear Geo D A X) := by
    intro hcol
    exact
      h.2.1
        (PrimCollinearSymm
          Geo D A X hcol)

  have hXAB :
      Not (PrimCollinear Geo X A B) := by
    intro hcol
    exact
      h.1
        (PrimCollinearSymm
          Geo X A B hcol)

  have hBAD :
      Not (PrimCollinear Geo B A D) := by
    intro hcol
    exact
      h.2.2.1
        (PrimCollinearSymm
          Geo B A D hcol)

  have hNoncoplanar :
      Not
        (exists pi : S.Plane,
          S.OnPlane A pi /\
          S.OnPlane D pi /\
          S.OnPlane X pi /\
          S.OnPlane B pi) := by

    intro hCop

    rcases hCop with
      ⟨pi,
        hApi,
        hDpi,
        hXpi,
        hBpi⟩

    exact
      h.2.2.2
        ⟨pi,
          hApi,
          hBpi,
          hXpi,
          hDpi⟩

  exact
    ⟨hDAX,
      hXAB,
      hBAD,
      hNoncoplanar⟩


/--
For C-A-X and D-A-Y, the angles DAX and CAY are vertical and hence
congruent.
-/
theorem hilbert_XI21_vertical_DAX_CAY_wyler
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C D X Y : Geo.Point)
    (hDAX :
      Not (PrimCollinear Geo D A X))
    (hCAX :
      Geo.Between C A X)
    (hDAY :
      Geo.Between D A Y) :
    Geo.AngleCongruent
      D A X
      C A Y := by

  have hXAC :
      Geo.Between X A C :=
    (HilbertOrder.between_incidence
      C A X hCAX).2.2.2.2

  have hRaw :
      Geo.AngleCongruent
        D A X
        Y A C :=
    VerticalAngles
      Geo
      D A X
      Y C
      hDAY
      hXAC
      hDAX

  exact
    (Geo.angle_congruent_reverse_second
      D A X
      Y A C).mp
      hRaw


/--
The unoriented angles XAB and BAX are congruent.
-/
theorem hilbert_XI21_angle_XAB_BAX_wyler
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B X : Geo.Point)
    (hXAB :
      Not (PrimCollinear Geo X A B)) :
    Geo.AngleCongruent
      X A B
      B A X := by

  unfold Geometry.Geo.AngleCongruent
  rw [Geo.angle_swap X A B]

  exact
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      B A X
      (by
        intro h
        exact
          hXAB
            (PrimCollinearSymm
              Geo B A X h))


/--
The direct complement comparison for XI.21 in the Hilbert-Wyler route:

    angle CAY + angle BAX > angle DAB.
-/
theorem hilbert_XI21_direct_comparison_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    [W : HilbertWylerAxioms Geo]
    (A B C D X Y : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo A B C D)
    (hCAX :
      Geo.Between C A X)
    (hDAY :
      Geo.Between D A Y) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      C A Y
      B A X
      D A B := by

  have hTriBX :
      HilbertTrihedralConfiguration
        Geo A B X D :=
    hilbert_XI21_trihedral_opposite_middle_wyler
      Geo
      A B C D X
      hTri
      hCAX

  have hTriDXB :
      HilbertTrihedralConfiguration
        Geo A D X B :=
    hilbert_XI21_trihedral_reorder_wyler
      Geo
      A B X D
      hTriBX

  have hXI20 :
      HilbertTrihedralAngleInequalities
        Geo A D X B :=
    euclid_proposition_11_20_wyler
      Geo
      A D X B
      hTriDXB

  have hRaw :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        D A X
        X A B
        D A B :=
    hXI20.1

  have hCAY :
      Not (PrimCollinear Geo C A Y) := by
    intro hCAYcol

    have hDAYdata :=
      HilbertOrder.between_incidence
        D A Y hDAY

    have hAY : Ne A Y :=
      hDAYdata.2.1

    have hDAYcol :
        PrimCollinear Geo D A Y :=
      hDAYdata.2.2.2.1

    have hAYD :
        PrimCollinear Geo A Y D :=
      PrimCollinearCycle
        Geo D A Y hDAYcol

    have hCADcol :
        PrimCollinear Geo C A D :=
      hilbert_primCollinear_trans
        Geo
        C A Y D
        hAY
        hCAYcol
        hAYD

    exact hTri.2.1 hCADcol

  have hDAX_CAY :
      Geo.AngleCongruent
        D A X
        C A Y :=
    hilbert_XI21_vertical_DAX_CAY_wyler
      Geo
      A C D X Y
      hTriDXB.1
      hCAX
      hDAY

  have hFirstTransport :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C A Y
        X A B
        D A B :=
    hilbertTwoAnglesGreaterThanAngle_transport_first
      Geo
      D A X
      C A Y
      X A B
      D A B
      hRaw
      hCAY
      hDAX_CAY

  have hBAX :
      Not (PrimCollinear Geo B A X) :=
    hTriBX.1

  have hXAB_BAX :
      Geo.AngleCongruent
        X A B
        B A X :=
    hilbert_XI21_angle_XAB_BAX_wyler
      Geo
      A B X
      hTriDXB.2.1

  exact
    hilbertTwoAnglesGreaterThanAngle_transport_second
      Geo
      C A Y
      X A B
      B A X
      D A B
      hFirstTransport
      hBAX
      hXAB_BAX


/--
Euclid XI.21 in Hilbert-Wyler form.

The three plane angles containing a proper trihedral solid angle are
together less than four right angles.
-/
theorem euclid_proposition_11_21_wyler
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertCongruence Geo]
    [W : HilbertWylerAxioms Geo]
    (A B C D : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo A B C D) :
    HilbertTrihedralAnglesLessThanFourRightAngles
      Geo A B C D := by

  rcases
      hilbert_XI21_supplement_rays_exist_wyler
        Geo
        A B C D
        hTri
    with
    ⟨X,
      Y,
      hCAX,
      hDAY⟩

  have hCompare :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C A Y
        B A X
        D A B :=
    hilbert_XI21_direct_comparison_wyler
      Geo
      A B C D X Y
      hTri
      hCAX
      hDAY

  have hBAC :
      Not (PrimCollinear Geo B A C) :=
    hTri.1

  have hCAD :
      Not (PrimCollinear Geo C A D) :=
    hTri.2.1

  have hDAB :
      Not (PrimCollinear Geo D A B) :=
    hTri.2.2.1

  unfold HilbertTrihedralAnglesLessThanFourRightAngles

  exact
    hilbertThreeAnglesLessThanFourRightAngles_intro
      Geo
      C A D
      B A C
      D A B
      Y X
      hCAD
      hBAC
      hDAB
      hDAY
      hCAX
      hCompare

end Geometry

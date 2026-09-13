import CGJteamLab.HilbertSpaceIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler incidence axioms

This module is the proposed dimension-free replacement for the
three-dimensional spatial incidence part of Hilbert's Group I.

The existing point-line and plane signatures are retained:

* `HilbertIncidence`;
* `HilbertPlaneIncidence`;
* `HilbertSpacePrimitive`.

The class below contains only the common point-line-plane incidence
clauses needed beyond dimension three together with Wyler I.7.

In particular, it does NOT assume:

* Hilbert I.7 in its three-dimensional form;
* Hilbert I.8;
* Smith I.5;
* Mac Lane-Steinitz exchange;
* any ambient dimension bound.

Smith I.5 and exchange belong to `HilbertWylerTheory`, where they are
derived from Wyler I.7.
-/

/--
Dimension-free Hilbert-Wyler spatial incidence.

The first five fields are the common incidence core corresponding to the
parts of Hilbert I.1-I.6 used by the current point-line-plane API.
The last field is the higher-dimensional replacement for Hilbert I.7.
-/
class HilbertWylerAxioms
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop where

  /-- Every ambient line contains two distinct points. -/
  two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        H.OnLine A l /\
        H.OnLine B l

  /-- Every primitive plane contains three noncollinear points. -/
  three_noncollinear_on_plane :
    forall pi : S.Plane,
      exists A B C : Geo.Point,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi /\
        Not (PrimCollinear Geo A B C)

  /-- Three noncollinear points lie in a plane. -/
  plane_through :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      exists pi : S.Plane,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi

  /-- Three noncollinear points determine their plane uniquely. -/
  plane_unique :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      forall pi rho : S.Plane,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        S.OnPlane A rho ->
        S.OnPlane B rho ->
        S.OnPlane C rho ->
        pi = rho

  /--
  If a plane contains two distinct points of a line, it contains the
  whole line.
  -/
  line_in_plane :
    forall A B : Geo.Point,
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall pi : S.Plane,
          S.OnPlane A pi ->
          S.OnPlane B pi ->
          HilbertLineInPlane Geo l pi

  /--
  Wyler I.7, exact intersection-line form.

  Let `a` and `b` be distinct lines in a plane `pi`, and let `P` be
  outside `pi`.  If `alpha` contains `a` and `P`, while `beta` contains
  `b` and `P`, then `alpha` and `beta` intersect in exactly one line
  carrier.

  This is the genuinely new dimension-free spatial incidence clause.
  -/
  wyler_i7_intersection_line :
    forall pi : S.Plane,
      forall a b : Geo.Line,
        Ne a b ->
        HilbertLineInPlane Geo a pi ->
        HilbertLineInPlane Geo b pi ->
        forall P : Geo.Point,
          Not (S.OnPlane P pi) ->
          forall alpha beta : S.Plane,
            HilbertLineInPlane Geo a alpha ->
            S.OnPlane P alpha ->
            HilbertLineInPlane Geo b beta ->
            S.OnPlane P beta ->
            exists m : Geo.Line,
              forall X : Geo.Point,
                H.OnLine X m <->
                  S.OnPlane X alpha /\ S.OnPlane X beta

end Geometry

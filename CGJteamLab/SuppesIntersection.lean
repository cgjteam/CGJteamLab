import CGJteamLab.SuppesInterface

/-!
# Moler-Suppes Pythagorean Constructive Geometry

This module formalizes the constructive operations and axioms used in:

Nancy Moler and Patrick Suppes,
"Quantifier-free axioms for constructive plane geometry",
Compositio Mathematica 20 (1968), 143-152.

The primitive operations are:

* S(x,y,u,v): segment construction,
* I(x,y,u,v): line intersection.

The structure also contains the three distinguished points
alpha, beta, gamma used in the dimension and nondegeneracy axioms.

This theory is kept separate from the midpoint/doubling theory
of Suppes (2000). Compatibility between the two theories is
handled in SuppesPCGCompatibility.lean.
-/

namespace Geometry
namespace Suppes

universe u

/-!
## Primitive PCG structure
-/

/--
Primitive structure of Moler-Suppes Pythagorean Constructive Geometry.
-/
class SuppesPCG (Point : Type u) where

  /--
  S(x,y,u,v): primitive segment-construction operation.
  -/
  segmentConstruction :
    Point -> Point -> Point -> Point -> Point

  /--
  I(x,y,u,v): primitive line-intersection operation.
  -/
  intersection :
    Point -> Point -> Point -> Point -> Point

  /-- Distinguished point alpha. -/
  alpha : Point

  /-- Distinguished point beta. -/
  beta : Point

  /-- Distinguished point gamma. -/
  gamma : Point


variable {Point : Type u}
variable [SuppesPCG Point]


/-!
## Defined relations
-/

/--
Moler-Suppes 1968, Definition 1: betweenness.
-/
def PCGBetween
    (X Y Z : Point) : Prop :=
  (X ≠ Z ->
      SuppesPCG.segmentConstruction
        (Point := Point) X Y X Z = Y ∧
      SuppesPCG.segmentConstruction
        (Point := Point) Z Y Z X = Y) ∧
  (X = Z -> X = Y)


/--
Moler-Suppes 1968, Definition 2: collinearity.
-/
def PCGCollinear
    (X Y Z : Point) : Prop :=
  SuppesPCG.segmentConstruction
      (Point := Point) X Y X Z = Y ∨
  SuppesPCG.segmentConstruction
      (Point := Point) Z Y Z X = Y ∨
  X = Z


/--
Moler-Suppes 1968, Definition 3:
noncollinearity condition for four points.
-/
def PCGNoncollinear4
    (X Y U V : Point) : Prop :=
  ¬ PCGCollinear X Y U ∧
  ¬ PCGCollinear Y U V ∧
  ¬ PCGCollinear X U V ∧
  ¬ PCGCollinear X Y V


/-!
## Axioms 1-11: segment construction and betweenness
-/

/--
Moler-Suppes 1968, Axiom 1:
lower-dimension axiom.
-/
axiom lower_dimension :
    SuppesPCG.segmentConstruction
        (Point := Point)
        SuppesPCG.beta
        SuppesPCG.alpha
        SuppesPCG.beta
        SuppesPCG.gamma
      ≠ SuppesPCG.alpha ∧
    SuppesPCG.segmentConstruction
        (Point := Point)
        SuppesPCG.gamma
        SuppesPCG.beta
        SuppesPCG.gamma
        SuppesPCG.alpha
      ≠ SuppesPCG.beta ∧
    SuppesPCG.segmentConstruction
        (Point := Point)
        SuppesPCG.alpha
        SuppesPCG.gamma
        SuppesPCG.alpha
        SuppesPCG.beta
      ≠ SuppesPCG.gamma


/--
Moler-Suppes 1968, Axiom 2:
nondegeneracy axiom.
-/
axiom segment_nondegenerate :
    SuppesPCG.segmentConstruction
        (Point := Point)
        SuppesPCG.alpha
        SuppesPCG.beta
        SuppesPCG.beta
        SuppesPCG.gamma
      ≠ SuppesPCG.gamma


/--
Moler-Suppes 1968, Axiom 3:
reflexivity of segment construction.
-/
axiom segment_reflexive
    (X Y : Point) :
    SuppesPCG.segmentConstruction
      (Point := Point) X Y Y X = X


/--
Moler-Suppes 1968, Axiom 4:
identity axiom for segment construction.
-/
axiom segment_identity
    (X U V : Point) :
    SuppesPCG.segmentConstruction
      (Point := Point) X X U V = U


/--
Moler-Suppes 1968, Axiom 5:
transitivity axiom for segment construction.
-/
axiom segment_transitivity
    (X Y W T Z U V : Point)
    (h :
      SuppesPCG.segmentConstruction
        (Point := Point) X Y W T = Z) :
    SuppesPCG.segmentConstruction
        (Point := Point) X Y U V =
    SuppesPCG.segmentConstruction
        (Point := Point) W Z U V


/--
Moler-Suppes 1968, Axiom 6:
direction axiom.
-/
axiom segment_direction
    (X Y U V Z : Point)
    (h :
      SuppesPCG.segmentConstruction
        (Point := Point) X Y U V = Z) :
    SuppesPCG.segmentConstruction
        (Point := Point) V Z V U = Z ∨
    SuppesPCG.segmentConstruction
        (Point := Point) Z V Z U = V


/--
Moler-Suppes 1968, Axiom 7:
distance axiom.
-/
axiom segment_distance
    (U V W Z : Point)
    (hBetween : PCGBetween U V W)
    (hConstruction :
      SuppesPCG.segmentConstruction
        (Point := Point) U W V U = Z) :
    SuppesPCG.segmentConstruction
      (Point := Point) Z U Z V = W


/--
Moler-Suppes 1968, Axiom 8:
connectivity axiom.
-/
axiom segment_connectivity
    (U V Z W : Point)
    (hUV : U ≠ V)
    (hZ :
      SuppesPCG.segmentConstruction
        (Point := Point) U V U Z = V)
    (hW :
      SuppesPCG.segmentConstruction
        (Point := Point) U V U W = V) :
    SuppesPCG.segmentConstruction
      (Point := Point) U Z U W = Z


/--
Moler-Suppes 1968, Axiom 9:
first transitivity axiom for betweenness.
-/
axiom between_transitivity_first
    (U V W Z : Point)
    (hUVZ : PCGBetween U V Z)
    (hVWZ : PCGBetween V W Z) :
    PCGBetween U V W


/--
Moler-Suppes 1968, Axiom 10:
second transitivity axiom for betweenness.
-/
axiom between_transitivity_second
    (U V W Z : Point)
    (hVW : V ≠ W)
    (hUVW : PCGBetween U V W)
    (hVWZ : PCGBetween V W Z) :
    PCGBetween U V Z


/--
Moler-Suppes 1968, Axiom 11:
five-segment axiom.
-/
axiom five_segment
    (U V W X Y Z T S0 : Point)
    (hUV : U ≠ V)
    (hXYZ : PCGBetween X Y Z)
    (hUVW : PCGBetween U V W)
    (h1 :
      SuppesPCG.segmentConstruction
        (Point := Point) U V X Y = Y)
    (h2 :
      SuppesPCG.segmentConstruction
        (Point := Point) W V Z Y = Y)
    (h3 :
      SuppesPCG.segmentConstruction
        (Point := Point) U T X S0 = S0)
    (h4 :
      SuppesPCG.segmentConstruction
        (Point := Point) V T Y S0 = S0) :
    SuppesPCG.segmentConstruction
      (Point := Point) W T Z S0 = S0


/-!
## Axioms 12-14: line intersection
-/

/--
Moler-Suppes 1968, Axiom 12:
I(x,y,u,v) = I(u,v,x,y).
-/
axiom intersection_comm_lines
    (X Y U V : Point) :
    SuppesPCG.intersection
        (Point := Point) X Y U V =
    SuppesPCG.intersection
        (Point := Point) U V X Y


/--
Moler-Suppes 1968, Axiom 13:
I(x,y,u,v) = I(x,y,v,u).
-/
axiom intersection_swap_second
    (X Y U V : Point) :
    SuppesPCG.intersection
        (Point := Point) X Y U V =
    SuppesPCG.intersection
        (Point := Point) X Y V U


/--
Moler-Suppes 1968, Axiom 14:
collinearity axiom for line intersection.
-/
axiom intersection_collinearity
    (X Y U V W : Point)
    (hXY : X ≠ Y)
    (hI :
      SuppesPCG.intersection
        (Point := Point) X Y U V = W)
    (hLine :
      SuppesPCG.segmentConstruction
          (Point := Point) X Y X W = Y ∨
      SuppesPCG.segmentConstruction
          (Point := Point) Y W Y X = W) :
    SuppesPCG.segmentConstruction
        (Point := Point) U V U W = V ∨
    SuppesPCG.segmentConstruction
        (Point := Point) V W V U = W


/-!
## Axiom 15: Pasch
-/

/--
Moler-Suppes 1968, Axiom 15:
Pasch's axiom.
-/
axiom pcg_pasch
    (X Y Z T : Point)
    (hTZ : T ≠ Z)
    (hXT :
      PCGBetween
        X
        T
        (SuppesPCG.intersection
          (Point := Point) X T Y Z))
    (hYZ :
      PCGBetween
        Y
        (SuppesPCG.intersection
          (Point := Point) X T Y Z)
        Z) :
    PCGBetween
      X
      (SuppesPCG.intersection
        (Point := Point) X Y Z T)
      Y


/-!
## Axiom 16: regular line intersection
-/

/--
Moler-Suppes 1968, Axiom 16:
regular line intersection.
-/
axiom regular_line_intersection
    (X Y U V W : Point)
    (hUV : U ≠ V)
    (hXYW : PCGCollinear X W Y)
    (hUWV : PCGCollinear U W V)
    (hDistinct :
      ¬ PCGCollinear X Y U ∨
      ¬ PCGCollinear X Y V) :
    SuppesPCG.intersection
      (Point := Point) X Y U V = W


/-!
## Axiom 17: Euclid
-/

/--
Moler-Suppes 1968, Axiom 17:
Euclid's axiom.

Under the stated nondegeneracy and directional conditions,
the constructed intersection I(X,Y,U,V) lies on line XY.
-/
axiom euclid_intersection_collinear
    (X Y U V : Point)
    (hNL :
      PCGNoncollinear4 X Y U V)
    (hBetween :
      PCGBetween
        X
        (SuppesPCG.intersection
          (Point := Point)
          X
          (SuppesPCG.segmentConstruction
            (Point := Point) X Y U V)
          Y
          U)
        (SuppesPCG.segmentConstruction
          (Point := Point) X Y U V))
    (hDir :
      SuppesPCG.segmentConstruction
          (Point := Point)
          Y
          (SuppesPCG.segmentConstruction
            (Point := Point) X Y U V)
          X
          U
        ≠ U) :
    PCGCollinear
      X
      Y
      (SuppesPCG.intersection
        (Point := Point) X Y U V)


end Suppes
end Geometry

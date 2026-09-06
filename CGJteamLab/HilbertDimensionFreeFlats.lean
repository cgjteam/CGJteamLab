import CGJteamLab.HilbertDimensionFreeIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Dimension-free Smith flats and generated span

A Smith flat is a set of points closed under:

1. the whole line through any two distinct points already in the set;
2. the whole plane through any three noncollinear points already in the set.

The generated Smith span of a set is the intersection of all Smith flats
containing it.

This module is dimension-free and purely incidence-theoretic.
-/

/--
A dimension-free Smith flat.
-/
def SmithFlat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point) : Prop :=
  (forall A B : Geo.Point,
      F A ->
      F B ->
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall X : Geo.Point,
          H.OnLine X l ->
          F X) /\
  (forall A B C : Geo.Point,
      F A ->
      F B ->
      F C ->
      Not (PrimCollinear Geo A B C) ->
      forall pi : S.Plane,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        forall X : Geo.Point,
          S.OnPlane X pi ->
          F X)


/--
The Smith span of X is the intersection of all Smith flats containing X.
-/
def SmithSpan
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point) : Set Geo.Point :=
  fun P =>
    forall F : Set Geo.Point,
      SmithFlat Geo F ->
      Set.Subset X F ->
      F P


/--
The universal point set is a Smith flat.
-/
theorem smithFlat_univ
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    SmithFlat Geo (Set.univ : Set Geo.Point) := by

  constructor

  · intro A B hA hB hAB l hAl hBl X hXl
    trivial

  · intro A B C hA hB hC hABC pi hApi hBpi hCpi X hXpi
    trivial


/--
Every generator belongs to its Smith span.
-/
theorem smithSpan_extensive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point) :
    Set.Subset X (SmithSpan Geo X) := by

  intro P hPX F hFlat hXF
  exact hXF hPX


/--
The Smith span is contained in every Smith flat containing the generators.
-/
theorem smithSpan_least
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (hXF : Set.Subset X F) :
    Set.Subset (SmithSpan Geo X) F := by

  intro P hP
  exact hP F hFlat hXF


/--
The generated Smith span is itself a Smith flat.
-/
theorem smithSpan_flat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point) :
    SmithFlat Geo (SmithSpan Geo X) := by

  constructor

  · intro A B hA hB hAB l hAl hBl P hPl F hFlat hXF

    exact
      hFlat.1
        A B
        (hA F hFlat hXF)
        (hB F hFlat hXF)
        hAB
        l hAl hBl
        P hPl

  · intro A B C hA hB hC hABC pi hApi hBpi hCpi P hPpi F hFlat hXF

    exact
      hFlat.2
        A B C
        (hA F hFlat hXF)
        (hB F hFlat hXF)
        (hC F hFlat hXF)
        hABC
        pi hApi hBpi hCpi
        P hPpi


/--
Carrier set of one primitive ambient plane.
-/
def SmithPlaneCarrier
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane) : Set Geo.Point :=
  fun P => S.OnPlane P pi


/--
Every primitive ambient plane is a Smith flat.
-/
theorem smithPlaneCarrier_flat
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    (pi : S.Plane) :
    SmithFlat Geo (SmithPlaneCarrier Geo pi) := by

  constructor

  · intro A B hApi hBpi hAB l hAl hBl X hXl

    have hlpi : HilbertLineInPlane Geo l pi :=
      HilbertDimensionFreeIncidence.line_in_plane
        (Geo := Geo)
        A B hAB
        l hAl hBl
        pi hApi hBpi

    exact hlpi X hXl

  · intro A B C hApi hBpi hCpi hABC
      rho hArho hBrho hCrho X hXrho

    have hrhoPi : rho = pi :=
      HilbertDimensionFreeIncidence.plane_unique
        (Geo := Geo)
        A B C hABC
        rho pi
        hArho hBrho hCrho
        hApi hBpi hCpi

    rw [hrhoPi] at hXrho
    exact hXrho


/--
The set consisting of exactly three named points.
-/
def SmithPointTriple
    (A B C : Geo.Point) : Set Geo.Point :=
  fun X =>
    X = A \/ X = B \/ X = C


/--
The Smith span of three noncollinear points is exactly the primitive plane
through them.

This is the basic bridge between Smith flats and the existing primitive
plane language.
-/
theorem smithSpan_three_noncollinear_eq_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (pi : S.Plane)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hCpi : S.OnPlane C pi) :
    SmithSpan Geo (SmithPointTriple Geo A B C) =
      SmithPlaneCarrier Geo pi := by

  apply Set.ext
  intro X
  constructor

  · intro hX

    have hFlatPi : SmithFlat Geo (SmithPlaneCarrier Geo pi) :=
      smithPlaneCarrier_flat
        (Geo := Geo) pi

    have hTriplePi :
        Set.Subset
          (SmithPointTriple Geo A B C)
          (SmithPlaneCarrier Geo pi) := by
      intro Y hY
      rcases hY with hYA | hYB | hYC
      · subst Y
        exact hApi
      · subst Y
        exact hBpi
      · subst Y
        exact hCpi

    exact
      hX
        (SmithPlaneCarrier Geo pi)
        hFlatPi
        hTriplePi

  · intro hXpi F hFlat hTripleF

    have hAF : F A := by
      apply hTripleF
      exact Or.inl rfl

    have hBF : F B := by
      apply hTripleF
      exact Or.inr (Or.inl rfl)

    have hCF : F C := by
      apply hTripleF
      exact Or.inr (Or.inr rfl)

    exact
      hFlat.2
        A B C
        hAF hBF hCF
        hABC
        pi hApi hBpi hCpi
        X hXpi

end Geometry

import CGJteamLab.Wyler.Hilbert3DFlats

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert 3D Wyler calculus

General 3D flat calculus built directly on the Hilbert spatial incidence
interface.

This module is intended as the reusable incidence layer for applications
such as Euclid Book XI.  It does not import any Euclid proposition and it
does not use the dimension-free incidence development.

The current API has been extracted from the first concrete tests on
Euclid XI.1-XI.4:

* monotonicity and fixed-point laws for span;
* exact span of two distinct points;
* exact span of three noncollinear points;
* four noncoplanar points generate the whole space;
* join of two point sets;
* two distinct intersecting lines join to their plane;
* two distinct planes with a common point meet in a line;
* a join equation recovers containment of its generators.
-/

/-!
## Basic span calculus
-/

/--
Monotonicity of the 3D span operator.
-/
theorem hilbertSpan3D_mono
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {X Y : Set Geo.Point}
    (hXY : Set.Subset X Y) :
    Set.Subset (HilbertSpan3D Geo X) (HilbertSpan3D Geo Y) := by
  intro P hPX F hFlat hYF
  exact hPX F hFlat (fun Q hQX => hYF (hXY hQX))


/--
A flat is fixed by the 3D span operator.
-/
theorem hilbertSpan3D_eq_self_of_flat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point)
    (hFlat : HilbertFlat3D Geo F) :
    HilbertSpan3D Geo F = F := by
  apply Set.ext
  intro P
  constructor

  next =>
    intro hP
    exact hP F hFlat (fun Q hQ => hQ)

  next =>
    intro hP
    exact hilbertSpan3D_extensive
      (Geo := Geo) F hP


/-!
## Exact finite spans
-/

/--
If `A` and `B` are distinct points of an ambient Hilbert line `l`,
then their 3D span is exactly the carrier of `l`.
-/
theorem hilbertSpan3D_pair_eq_lineCarrier
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (A B : Geo.Point)
    (l : Geo.Line)
    (hAB : Ne A B)
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l) :
    HilbertSpan3D Geo ({A, B} : Set Geo.Point) =
      HilbertLineCarrier3D Geo l := by
  apply Set.ext
  intro P
  constructor

  next =>
    intro hP
    exact
      hP
        (HilbertLineCarrier3D Geo l)
        (hilbertLineCarrier3D_flat (Geo := Geo) l)
        (by
          intro Q hQ
          change H.OnLine Q l
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
          rcases hQ with hQA | hQB
          next =>
            subst Q
            exact hAl
          next =>
            subst Q
            exact hBl)

  next =>
    intro hPl F hFlat hPairF

    have hFA : F A := by
      apply hPairF
      simp

    have hFB : F B := by
      apply hPairF
      simp

    exact
      hFlat.1
        A B
        hFA hFB hAB
        l hAl hBl
        P hPl


/--
If `A`, `B`, `C` are noncollinear points of an ambient Hilbert plane
`pi`, then their 3D span is exactly the carrier of `pi`.
-/
theorem hilbertSpan3D_triple_eq_planeCarrier
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (A B C : Geo.Point)
    (pi : S.Plane)
    (hABC : Not (PrimCollinear Geo A B C))
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hCpi : S.OnPlane C pi) :
    HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) =
      HilbertPlaneCarrier3D Geo pi := by
  apply Set.ext
  intro P
  constructor

  next =>
    intro hP
    exact
      hP
        (HilbertPlaneCarrier3D Geo pi)
        (hilbertPlaneCarrier3D_flat (Geo := Geo) pi)
        (by
          intro Q hQ
          change S.OnPlane Q pi
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
          rcases hQ with hQA | hQB | hQC
          next =>
            subst Q
            exact hApi
          next =>
            subst Q
            exact hBpi
          next =>
            subst Q
            exact hCpi)

  next =>
    intro hPpi F hFlat hTripleF

    have hFA : F A := by
      apply hTripleF
      simp

    have hFB : F B := by
      apply hTripleF
      simp

    have hFC : F C := by
      apply hTripleF
      simp

    exact
      hFlat.2
        A B C
        hFA hFB hFC
        hABC
        pi hApi hBpi hCpi
        P hPpi


/--
If `A`, `B`, `C` are noncollinear in a plane `pi` and `D` lies
outside `pi`, then the four points generate the whole 3D space.
-/
theorem hilbertSpan3D_four_noncoplanar_eq_univ
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (A B C D : Geo.Point)
    (pi : S.Plane)
    (hABC : Not (PrimCollinear Geo A B C))
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi)
    (hCpi : S.OnPlane C pi)
    (hDpi : Not (S.OnPlane D pi)) :
    HilbertSpan3D Geo ({A, B, C, D} : Set Geo.Point) =
      (Set.univ : Set Geo.Point) := by
  apply Set.ext
  intro X
  constructor

  next =>
    intro _hX
    trivial

  next =>
    intro _hXuniv F hFlat hFourF

    have hFA : F A := by
      apply hFourF
      simp

    have hFB : F B := by
      apply hFourF
      simp

    have hFC : F C := by
      apply hFourF
      simp

    have hFD : F D := by
      apply hFourF
      simp

    have hPiF :
        forall Y : Geo.Point,
          S.OnPlane Y pi ->
          F Y := by
      intro Y hYpi
      exact
        hFlat.2
          A B C
          hFA hFB hFC
          hABC
          pi hApi hBpi hCpi
          Y hYpi

    by_cases hXD : X = D

    next =>
      subst X
      exact hFD

    next =>
      have hDX : Ne D X := by
        intro hDXeq
        exact hXD hDXeq.symm

      rcases
          HilbertPlaneIncidence.line_through
            D X hDX with
        ⟨m, hDm, hXm⟩

      have hExternal :
          exists R : Geo.Point,
            S.OnPlane R pi /\
            Not (H.OnLine R m) := by
        by_cases hAm : H.OnLine A m

        next =>
          by_cases hBm : H.OnLine B m

          next =>
            have hCm : Not (H.OnLine C m) := by
              intro hCm
              exact hABC
                (PrimCollinear.mk
                  (Geo := Geo)
                  hAm hBm hCm)
            exact ⟨C, hCpi, hCm⟩

          next =>
            exact ⟨B, hBpi, hBm⟩

        next =>
          exact ⟨A, hApi, hAm⟩

      rcases hExternal with
        ⟨R, hRpi, hRm⟩

      rcases
          hilbert_plane_through_line_and_external_point
            (Geo := Geo) m R hRm with
        ⟨rho, hmrho, hRrho, _hRhoUnique⟩

      have hrhopi : Ne rho pi := by
        intro hrhopiEq
        have hDrho : S.OnPlane D rho :=
          hmrho D hDm
        have hDpi' : S.OnPlane D pi := by
          rw [← hrhopiEq]
          exact hDrho
        exact hDpi hDpi'

      rcases
          hilbert_plane_intersection_line
            (Geo := Geo)
            rho pi
            hrhopi
            R
            hRrho hRpi with
        ⟨l, _hRl, hlrho, hlpi, _hIntersection⟩

      rcases
          HilbertSpaceIncidence.two_points_on_each_line
            (Geo := Geo) l with
        ⟨P, Q, hPQ, hPl, hQl⟩

      have hPpi : S.OnPlane P pi :=
        hlpi P hPl

      have hQpi : S.OnPlane Q pi :=
        hlpi Q hQl

      have hPrho : S.OnPlane P rho :=
        hlrho P hPl

      have hQrho : S.OnPlane Q rho :=
        hlrho Q hQl

      have hFP : F P :=
        hPiF P hPpi

      have hFQ : F Q :=
        hPiF Q hQpi

      have hDl : Not (H.OnLine D l) := by
        intro hDl
        have hDpi' : S.OnPlane D pi :=
          hlpi D hDl
        exact hDpi hDpi'

      have hPQD :
          Not (PrimCollinear Geo P Q D) := by
        intro hCol
        have hDonL : H.OnLine D l :=
          hilbert_on_line_of_primCollinear_with_two_on_line
            (Geo := Geo)
            hPQ hPl hQl hCol
        exact hDl hDonL

      have hDrho : S.OnPlane D rho :=
        hmrho D hDm

      have hXrho : S.OnPlane X rho :=
        hmrho X hXm

      exact
        hFlat.2
          P Q D
          hFP hFQ hFD
          hPQD
          rho hPrho hQrho hDrho
          X hXrho


/-!
## Join
-/

/--
Join of two point sets in Hilbert 3D.
-/
def HilbertJoin3D
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X Y : Set Geo.Point) : Set Geo.Point :=
  HilbertSpan3D Geo (Set.union X Y)


/--
The left generator is contained in the join.
-/
theorem hilbertJoin3D_left
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X Y : Set Geo.Point) :
    Set.Subset X (HilbertJoin3D Geo X Y) := by
  intro P hPX
  apply hilbertSpan3D_extensive
    (Geo := Geo)
    (Set.union X Y)
  exact Or.inl hPX


/--
The right generator is contained in the join.
-/
theorem hilbertJoin3D_right
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X Y : Set Geo.Point) :
    Set.Subset Y (HilbertJoin3D Geo X Y) := by
  intro P hPY
  apply hilbertSpan3D_extensive
    (Geo := Geo)
    (Set.union X Y)
  exact Or.inr hPY


/--
The join is contained in every flat containing both generators.
-/
theorem hilbertJoin3D_least
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X Y F : Set Geo.Point)
    (hFlat : HilbertFlat3D Geo F)
    (hXF : Set.Subset X F)
    (hYF : Set.Subset Y F) :
    Set.Subset (HilbertJoin3D Geo X Y) F := by
  apply hilbertSpan3D_least
    (Geo := Geo)
    (Set.union X Y)
    F
    hFlat
  intro P hP
  cases hP with
  | inl hPX =>
      exact hXF hPX
  | inr hPY =>
      exact hYF hPY


/--
If a join is known extensionally to equal `F`, then both generators
are contained in `F`.

This is the generic containment step extracted from the XI.4 test.
-/
theorem hilbertJoin3D_generators_subset_of_eq
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X Y F : Set Geo.Point)
    (hJoin : HilbertJoin3D Geo X Y = F) :
    Set.Subset X F /\ Set.Subset Y F := by
  constructor

  next =>
    intro P hPX
    have hPJoin :
        HilbertJoin3D Geo X Y P :=
      hilbertJoin3D_left
        (Geo := Geo) X Y hPX
    rw [hJoin] at hPJoin
    exact hPJoin

  next =>
    intro P hPY
    have hPJoin :
        HilbertJoin3D Geo X Y P :=
      hilbertJoin3D_right
        (Geo := Geo) X Y hPY
    rw [hJoin] at hPJoin
    exact hPJoin


/--
Two distinct intersecting lines generate their unique plane.
-/
theorem hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (P : Geo.Point)
    (hlm : Ne l m)
    (hPl : H.OnLine P l)
    (hPm : H.OnLine P m) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo m pi /\
      HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo l)
        (HilbertLineCarrier3D Geo m) =
      HilbertPlaneCarrier3D Geo pi := by

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        l m hlm P hPl hPm with
    ⟨pi, hlpi, hmpi, _hUnique⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) l P with
    ⟨A, hAP, hAl⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) m P with
    ⟨B, hBP, hBm⟩

  have hAPB : Not (PrimCollinear Geo A P B) := by
    intro hCol
    rcases hCol with ⟨n, hAn, hPn, hBn⟩

    have hln : l = n :=
      HilbertPlaneIncidence.line_unique
        A P hAP
        l n
        hAl hPl
        hAn hPn

    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        B P hBP
        m n
        hBm hPm
        hBn hPn

    exact hlm (hln.trans hmn.symm)

  have hApi : S.OnPlane A pi :=
    hlpi A hAl

  have hPpi : S.OnPlane P pi :=
    hlpi P hPl

  have hBpi : S.OnPlane B pi :=
    hmpi B hBm

  have hTripleSpan :
      HilbertSpan3D Geo ({A, P, B} : Set Geo.Point) =
        HilbertPlaneCarrier3D Geo pi :=
    hilbertSpan3D_triple_eq_planeCarrier
      (Geo := Geo)
      A P B pi
      hAPB
      hApi hPpi hBpi

  have hTripleSubsetUnion :
      Set.Subset
        ({A, P, B} : Set Geo.Point)
        (Set.union
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)) := by
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with hXA | hXP | hXB

    next =>
      subst X
      exact Or.inl hAl

    next =>
      subst X
      exact Or.inl hPl

    next =>
      subst X
      exact Or.inr hBm

  have hPlaneSubsetJoin :
      Set.Subset
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)) := by

    have hMono :
        Set.Subset
          (HilbertSpan3D Geo ({A, P, B} : Set Geo.Point))
          (HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            (HilbertLineCarrier3D Geo m)) := by
      exact
        hilbertSpan3D_mono
          (Geo := Geo)
          hTripleSubsetUnion

    rw [hTripleSpan] at hMono
    exact hMono

  have hJoinSubsetPlane :
      Set.Subset
        (HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m))
        (HilbertPlaneCarrier3D Geo pi) :=
    hilbertJoin3D_least
      (Geo := Geo)
      (HilbertLineCarrier3D Geo l)
      (HilbertLineCarrier3D Geo m)
      (HilbertPlaneCarrier3D Geo pi)
      (hilbertPlaneCarrier3D_flat (Geo := Geo) pi)
      hlpi
      hmpi

  have hJoinEq :
      HilbertJoin3D Geo
        (HilbertLineCarrier3D Geo l)
        (HilbertLineCarrier3D Geo m) =
      HilbertPlaneCarrier3D Geo pi := by
    apply Set.Subset.antisymm
    exact hJoinSubsetPlane
    exact hPlaneSubsetJoin

  exact
    ⟨pi, hlpi, hmpi, hJoinEq⟩




/--
Two distinct ambient lines contained in the same Hilbert plane generate
the whole plane.

This strictly generalizes the intersecting-lines join theorem: the two
lines may intersect or be parallel.
-/
theorem hilbertJoin3D_two_distinct_coplanar_lines_eq_planeCarrier
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (l m : Geo.Line)
    (hlm : Ne l m)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hmpi : HilbertLineInPlane Geo m pi) :
    HilbertJoin3D Geo
      (HilbertLineCarrier3D Geo l)
      (HilbertLineCarrier3D Geo m) =
    HilbertPlaneCarrier3D Geo pi := by

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) l with
    ⟨A, B, hAB, hAl, hBl⟩

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) m with
    ⟨C0, D0, hC0D0, hC0m, hD0m⟩

  have hExternal :
      exists C : Geo.Point,
        H.OnLine C m /\
        Not (H.OnLine C l) := by

    by_cases hC0l : H.OnLine C0 l

    next =>
      by_cases hD0l : H.OnLine D0 l

      next =>
        have hml : m = l :=
          HilbertPlaneIncidence.line_unique
            C0 D0 hC0D0
            m l
            hC0m hD0m
            hC0l hD0l

        exact False.elim (hlm hml.symm)

      next =>
        exact ⟨D0, hD0m, hD0l⟩

    next =>
      exact ⟨C0, hC0m, hC0l⟩

  rcases hExternal with
    ⟨C, hCm, hCl⟩

  have hABC :
      Not (PrimCollinear Geo A B C) := by
    intro hCol

    have hCl' : H.OnLine C l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAB hAl hBl hCol

    exact hCl hCl'

  have hApi : S.OnPlane A pi :=
    hlpi A hAl

  have hBpi : S.OnPlane B pi :=
    hlpi B hBl

  have hCpi : S.OnPlane C pi :=
    hmpi C hCm

  have hTripleSpan :
      HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) =
        HilbertPlaneCarrier3D Geo pi :=
    hilbertSpan3D_triple_eq_planeCarrier
      (Geo := Geo)
      A B C pi
      hABC
      hApi hBpi hCpi

  have hTripleSubsetUnion :
      Set.Subset
        ({A, B, C} : Set Geo.Point)
        (Set.union
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)) := by
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with hXA | hXB | hXC

    next =>
      subst X
      exact Or.inl hAl

    next =>
      subst X
      exact Or.inl hBl

    next =>
      subst X
      exact Or.inr hCm

  have hPlaneSubsetJoin :
      Set.Subset
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)) := by

    have hMono :
        Set.Subset
          (HilbertSpan3D Geo ({A, B, C} : Set Geo.Point))
          (HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            (HilbertLineCarrier3D Geo m)) :=
      hilbertSpan3D_mono
        (Geo := Geo)
        hTripleSubsetUnion

    rw [hTripleSpan] at hMono
    exact hMono

  have hJoinSubsetPlane :
      Set.Subset
        (HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m))
        (HilbertPlaneCarrier3D Geo pi) :=
    hilbertJoin3D_least
      (Geo := Geo)
      (HilbertLineCarrier3D Geo l)
      (HilbertLineCarrier3D Geo m)
      (HilbertPlaneCarrier3D Geo pi)
      (hilbertPlaneCarrier3D_flat
        (Geo := Geo) pi)
      hlpi
      hmpi

  apply Set.Subset.antisymm
  exact hJoinSubsetPlane
  exact hPlaneSubsetJoin




/--
A line and a point outside it generate every Hilbert plane containing
them.

In carrier language:

  join(carrier(l), {P}) = carrier(pi).

This is the basic rank-raising generator rule from line to plane.
-/
theorem hilbertJoin3D_line_external_point_eq_planeCarrier
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (P : Geo.Point)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hPpi : S.OnPlane P pi)
    (hPl : Not (H.OnLine P l)) :
    HilbertJoin3D Geo
      (HilbertLineCarrier3D Geo l)
      ({P} : Set Geo.Point) =
    HilbertPlaneCarrier3D Geo pi := by

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) l with
    ⟨A, B, hAB, hAl, hBl⟩

  have hABP :
      Not (PrimCollinear Geo A B P) := by
    intro hCol

    have hPl' : H.OnLine P l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAB hAl hBl hCol

    exact hPl hPl'

  have hApi : S.OnPlane A pi :=
    hlpi A hAl

  have hBpi : S.OnPlane B pi :=
    hlpi B hBl

  have hTripleSpan :
      HilbertSpan3D Geo ({A, B, P} : Set Geo.Point) =
        HilbertPlaneCarrier3D Geo pi :=
    hilbertSpan3D_triple_eq_planeCarrier
      (Geo := Geo)
      A B P pi
      hABP
      hApi hBpi hPpi

  have hTripleSubsetJoinGenerators :
      Set.Subset
        ({A, B, P} : Set Geo.Point)
        (Set.union
          (HilbertLineCarrier3D Geo l)
          ({P} : Set Geo.Point)) := by
    intro X hX
    simp only
      [Set.mem_insert_iff,
       Set.mem_singleton_iff] at hX

    rcases hX with hXA | hXB | hXP

    next =>
      subst X
      exact Or.inl hAl

    next =>
      subst X
      exact Or.inl hBl

    next =>
      subst X
      exact Or.inr (by simp)

  have hPlaneSubsetJoin :
      Set.Subset
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          ({P} : Set Geo.Point)) := by

    have hMono :
        Set.Subset
          (HilbertSpan3D Geo ({A, B, P} : Set Geo.Point))
          (HilbertJoin3D Geo
            (HilbertLineCarrier3D Geo l)
            ({P} : Set Geo.Point)) :=
      hilbertSpan3D_mono
        (Geo := Geo)
        hTripleSubsetJoinGenerators

    rw [hTripleSpan] at hMono
    exact hMono

  have hPointSubsetPlane :
      Set.Subset
        ({P} : Set Geo.Point)
        (HilbertPlaneCarrier3D Geo pi) := by
    intro X hXP
    simp only [Set.mem_singleton_iff] at hXP
    subst X
    exact hPpi

  have hJoinSubsetPlane :
      Set.Subset
        (HilbertJoin3D Geo
          (HilbertLineCarrier3D Geo l)
          ({P} : Set Geo.Point))
        (HilbertPlaneCarrier3D Geo pi) :=
    hilbertJoin3D_least
      (Geo := Geo)
      (HilbertLineCarrier3D Geo l)
      ({P} : Set Geo.Point)
      (HilbertPlaneCarrier3D Geo pi)
      (hilbertPlaneCarrier3D_flat
        (Geo := Geo) pi)
      hlpi
      hPointSubsetPlane

  apply Set.Subset.antisymm
  exact hJoinSubsetPlane
  exact hPlaneSubsetJoin




/--
A plane and one point outside it generate the whole ambient 3-space.

This is the rank-raising generator rule from dimension 2 to dimension 3.
-/
theorem hilbertJoin3D_plane_external_point_eq_univ
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (P : Geo.Point)
    (hPpi : Not (S.OnPlane P pi)) :
    HilbertJoin3D Geo
      (HilbertPlaneCarrier3D Geo pi)
      ({P} : Set Geo.Point) =
    (Set.univ : Set Geo.Point) := by

  rcases
      hilbert_three_noncollinear_on_plane
        (Geo := Geo) pi with
    ⟨A, B, C, hApi, hBpi, hCpi, hABC⟩

  have hFour :
      HilbertSpan3D Geo
        ({A, B, C, P} : Set Geo.Point) =
      (Set.univ : Set Geo.Point) :=
    hilbertSpan3D_four_noncoplanar_eq_univ
      (Geo := Geo)
      A B C P
      pi
      hABC
      hApi hBpi hCpi
      hPpi

  have hFourSubsetGenerators :
      Set.Subset
        ({A, B, C, P} : Set Geo.Point)
        (Set.union
          (HilbertPlaneCarrier3D Geo pi)
          ({P} : Set Geo.Point)) := by
    intro X hX

    simp only
      [Set.mem_insert_iff,
       Set.mem_singleton_iff] at hX

    rcases hX with hXA | hXB | hXC | hXP

    next =>
      subst X
      exact Or.inl hApi

    next =>
      subst X
      exact Or.inl hBpi

    next =>
      subst X
      exact Or.inl hCpi

    next =>
      subst X
      exact Or.inr (by simp)

  have hUnivSubsetJoin :
      Set.Subset
        (Set.univ : Set Geo.Point)
        (HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          ({P} : Set Geo.Point)) := by

    have hMono :
        Set.Subset
          (HilbertSpan3D Geo
            ({A, B, C, P} : Set Geo.Point))
          (HilbertJoin3D Geo
            (HilbertPlaneCarrier3D Geo pi)
            ({P} : Set Geo.Point)) :=
      hilbertSpan3D_mono
        (Geo := Geo)
        hFourSubsetGenerators

    rw [hFour] at hMono
    exact hMono

  apply Set.Subset.antisymm

  next =>
    intro X _hX
    trivial

  next =>
    exact hUnivSubsetJoin


/--
Two distinct ambient planes generate the whole 3-space.
-/
theorem hilbertJoin3D_two_distinct_planes_eq_univ
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hpiRho : Ne pi rho) :
    HilbertJoin3D Geo
      (HilbertPlaneCarrier3D Geo pi)
      (HilbertPlaneCarrier3D Geo rho) =
    (Set.univ : Set Geo.Point) := by

  rcases
      hilbert_three_noncollinear_on_plane
        (Geo := Geo) rho with
    ⟨A, B, C, hArho, hBrho, hCrho, hABC⟩

  have hExternal :
      exists P : Geo.Point,
        S.OnPlane P rho /\
        Not (S.OnPlane P pi) := by

    by_cases hApi : S.OnPlane A pi

    next =>
      by_cases hBpi : S.OnPlane B pi

      next =>
        by_cases hCpi : S.OnPlane C pi

        next =>
          have hEq : rho = pi :=
            HilbertSpaceIncidence.plane_unique
              (Geo := Geo)
              A B C hABC
              rho pi
              hArho hBrho hCrho
              hApi hBpi hCpi

          exact False.elim (hpiRho hEq.symm)

        next =>
          exact ⟨C, hCrho, hCpi⟩

      next =>
        exact ⟨B, hBrho, hBpi⟩

    next =>
      exact ⟨A, hArho, hApi⟩

  rcases hExternal with
    ⟨P, hPrho, hPpi⟩

  have hPlanePointJoin :
      HilbertJoin3D Geo
        (HilbertPlaneCarrier3D Geo pi)
        ({P} : Set Geo.Point) =
      (Set.univ : Set Geo.Point) :=
    hilbertJoin3D_plane_external_point_eq_univ
      (Geo := Geo)
      pi P hPpi

  have hGeneratorSubset :
      Set.Subset
        (Set.union
          (HilbertPlaneCarrier3D Geo pi)
          ({P} : Set Geo.Point))
        (Set.union
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho)) := by
    intro X hX

    rcases hX with hXpi | hXP

    next =>
      exact Or.inl hXpi

    next =>
      have hXP' : X = P := by
        simpa using hXP
      subst X
      exact Or.inr hPrho

  have hUnivSubsetJoin :
      Set.Subset
        (Set.univ : Set Geo.Point)
        (HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho)) := by

    have hMono :=
      hilbertSpan3D_mono
        (Geo := Geo)
        hGeneratorSubset

    change
      Set.Subset
        (HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          ({P} : Set Geo.Point))
        (HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho))
      at hMono

    rw [hPlanePointJoin] at hMono
    exact hMono

  apply Set.Subset.antisymm

  next =>
    intro X _hX
    trivial

  next =>
    exact hUnivSubsetJoin


/-!
## Meet of planes
-/

/--
Two distinct planes with a common point meet in exactly one line.
The conclusion is equality of flat carriers.
-/
theorem hilbertPlaneCarrier3D_inter_eq_lineCarrier
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo l rho /\
      Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      HilbertLineCarrier3D Geo l := by

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        pi rho hneq
        A hApi hArho with
    ⟨l, hAl, hlpi, hlrho, hIff⟩

  have hCarrierEq :
      Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      HilbertLineCarrier3D Geo l := by
    apply Set.ext
    intro X
    change
      (S.OnPlane X pi /\ S.OnPlane X rho) <->
      H.OnLine X l
    exact hIff X

  exact
    ⟨l, hAl, hlpi, hlrho, hCarrierEq⟩


/--
Two distinct planes either have empty intersection or intersect in a
line carrier.

This is the complete incidence normal form for the meet of two distinct
planes in ambient 3-space.
-/
theorem hilbertPlaneCarrier3D_inter_eq_empty_or_lineCarrier
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho) :
    Set.inter
        (HilbertPlaneCarrier3D Geo pi)
        (HilbertPlaneCarrier3D Geo rho) =
      (fun _ => False : Set Geo.Point) \/
    exists l : Geo.Line,
      Set.inter
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho) =
        HilbertLineCarrier3D Geo l := by

  by_cases hCommon :
      exists A : Geo.Point,
        S.OnPlane A pi /\
        S.OnPlane A rho

  next =>
    cases hCommon with
    | intro A hAData =>
        have hApi := hAData.1
        have hArho := hAData.2

        cases
            hilbertPlaneCarrier3D_inter_eq_lineCarrier
              (Geo := Geo)
              pi rho hneq
              A hApi hArho with
        | intro l hLData =>
            have hMeet := hLData.2.2.2
            exact Or.inr (Exists.intro l hMeet)

  next =>
    left
    apply Set.ext
    intro X
    constructor

    next =>
      intro hX

      have hFalse : False :=
        hCommon
          (Exists.intro X
            (And.intro hX.1 hX.2))

      exact False.elim hFalse

    next =>
      intro hX
      exact False.elim hX


/--
If `l` and `m` are distinct ambient lines, then `m` contains a point
which does not lie on `l`.
-/
theorem hilbert_point_on_second_line_off_first
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (hlm : Ne l m) :
    exists P : Geo.Point,
      H.OnLine P m /\
      Not (H.OnLine P l) := by

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) m with
    ⟨A, B, hAB, hAm, hBm⟩

  by_cases hAl : H.OnLine A l
  · by_cases hBl : H.OnLine B l
    · have hml : m = l :=
        HilbertPlaneIncidence.line_unique
          A B hAB
          m l
          hAm hBm
          hAl hBl
      exact False.elim (hlm hml.symm)
    · exact ⟨B, hBm, hBl⟩
  · exact ⟨A, hAm, hAl⟩


/--
Two noncollinear triples which are not all contained in one ambient
plane generate the whole Hilbert three-space.
-/
theorem hilbertSpan3D_six_points_eq_univ_of_two_noncoplanar_triples
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (A B C D E F : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hDEF : Not (PrimCollinear Geo D E F))
    (hNoCommonPlane :
      Not (exists omega : S.Plane,
        S.OnPlane A omega /\
        S.OnPlane B omega /\
        S.OnPlane C omega /\
        S.OnPlane D omega /\
        S.OnPlane E omega /\
        S.OnPlane F omega)) :
    HilbertSpan3D Geo
        ({A, B, C, D, E, F} : Set Geo.Point) =
      (Set.univ : Set Geo.Point) := by

  cases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B C hABC with
  | intro alpha hAlpha =>

      have hAalpha : S.OnPlane A alpha :=
        hAlpha.1

      have hBalpha : S.OnPlane B alpha :=
        hAlpha.2.1

      have hCalpha : S.OnPlane C alpha :=
        hAlpha.2.2

      cases
          HilbertSpaceIncidence.plane_through
            (Geo := Geo)
            D E F hDEF with
      | intro theta hTheta =>

          have hDtheta : S.OnPlane D theta :=
            hTheta.1

          have hEtheta : S.OnPlane E theta :=
            hTheta.2.1

          have hFtheta : S.OnPlane F theta :=
            hTheta.2.2

          have hAlphaTheta : Ne alpha theta := by
            intro hEq

            have hDalpha : S.OnPlane D alpha := by
              rw [hEq]
              exact hDtheta

            have hEalpha : S.OnPlane E alpha := by
              rw [hEq]
              exact hEtheta

            have hFalpha : S.OnPlane F alpha := by
              rw [hEq]
              exact hFtheta

            exact
              hNoCommonPlane
                (Exists.intro alpha
                  (And.intro hAalpha
                    (And.intro hBalpha
                      (And.intro hCalpha
                        (And.intro hDalpha
                          (And.intro hEalpha hFalpha))))))

          have hSpanABC :
              HilbertSpan3D Geo
                  ({A, B, C} : Set Geo.Point) =
                HilbertPlaneCarrier3D Geo alpha :=
            hilbertSpan3D_triple_eq_planeCarrier
              (Geo := Geo)
              A B C alpha
              hABC
              hAalpha hBalpha hCalpha

          have hSpanDEF :
              HilbertSpan3D Geo
                  ({D, E, F} : Set Geo.Point) =
                HilbertPlaneCarrier3D Geo theta :=
            hilbertSpan3D_triple_eq_planeCarrier
              (Geo := Geo)
              D E F theta
              hDEF
              hDtheta hEtheta hFtheta

          have hJoin :
              HilbertJoin3D Geo
                  (HilbertPlaneCarrier3D Geo alpha)
                  (HilbertPlaneCarrier3D Geo theta) =
                (Set.univ : Set Geo.Point) :=
            hilbertJoin3D_two_distinct_planes_eq_univ
              (Geo := Geo)
              alpha theta
              hAlphaTheta

          have hABCSubsetSix :
              Set.Subset
                ({A, B, C} : Set Geo.Point)
                ({A, B, C, D, E, F} : Set Geo.Point) := by
            intro X hX

            simp only
              [Set.mem_insert_iff,
               Set.mem_singleton_iff] at hX

            rcases hX with hXA | hXB | hXC

            next =>
              subst X
              simp

            next =>
              subst X
              simp

            next =>
              subst X
              simp

          have hDEFSubsetSix :
              Set.Subset
                ({D, E, F} : Set Geo.Point)
                ({A, B, C, D, E, F} : Set Geo.Point) := by
            intro X hX

            simp only
              [Set.mem_insert_iff,
               Set.mem_singleton_iff] at hX

            rcases hX with hXD | hXE | hXF

            next =>
              subst X
              simp

            next =>
              subst X
              simp

            next =>
              subst X
              simp

          have hAlphaSubsetSixSpan :
              Set.Subset
                (HilbertPlaneCarrier3D Geo alpha)
                (HilbertSpan3D Geo
                  ({A, B, C, D, E, F} : Set Geo.Point)) := by

            have hMono :=
              hilbertSpan3D_mono
                (Geo := Geo)
                hABCSubsetSix

            rw [hSpanABC] at hMono
            exact hMono

          have hThetaSubsetSixSpan :
              Set.Subset
                (HilbertPlaneCarrier3D Geo theta)
                (HilbertSpan3D Geo
                  ({A, B, C, D, E, F} : Set Geo.Point)) := by

            have hMono :=
              hilbertSpan3D_mono
                (Geo := Geo)
                hDEFSubsetSix

            rw [hSpanDEF] at hMono
            exact hMono

          have hJoinSubsetSixSpan :
              Set.Subset
                (HilbertJoin3D Geo
                  (HilbertPlaneCarrier3D Geo alpha)
                  (HilbertPlaneCarrier3D Geo theta))
                (HilbertSpan3D Geo
                  ({A, B, C, D, E, F} : Set Geo.Point)) :=
            hilbertJoin3D_least
              (Geo := Geo)
              (HilbertPlaneCarrier3D Geo alpha)
              (HilbertPlaneCarrier3D Geo theta)
              (HilbertSpan3D Geo
                ({A, B, C, D, E, F} : Set Geo.Point))
              (hilbertSpan3D_flat
                (Geo := Geo)
                ({A, B, C, D, E, F} : Set Geo.Point))
              hAlphaSubsetSixSpan
              hThetaSubsetSixSpan

          rw [hJoin] at hJoinSubsetSixSpan

          apply Set.Subset.antisymm

          next =>
            intro X _hX
            trivial

          next =>
            exact hJoinSubsetSixSpan


end Geometry

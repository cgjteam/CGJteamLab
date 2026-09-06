import CGJteamLab.HilbertDimensionFreeCone

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Smith I5 implies full Steinitz exchange

This is the final production layer of the dimension-free Smith/Wyler
incidence development.

The preceding modules established:

    Smith I5
      -> Wyler I.7 / LP4
      -> local Veblen-Young P3
      -> Wyler plane-cone flatness
      -> Wyler one-point generation.

This module converts one-point generation into generated-flat exchange,
handles the empty and singleton base-flat degeneracies, and concludes the
full Steinitz exchange law for `SmithSpan`.

No exchange axiom or global exchange instance is assumed.
-/

/--
Wyler's one-point generation formula yields generated-flat exchange when
the base flat contains two distinct points.
-/
theorem wylerOnePointGenerationFormula_implies_exchange_of_two_points
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (hGen : WylerOnePointGenerationFormula Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A B : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A))
    (hBOut : Not (F B))
    (hBinFA :
      SmithSpan Geo (SmithAdjoinPoint Geo F A) B) :
    SmithSpan Geo (SmithAdjoinPoint Geo F B) =
      SmithSpan Geo (SmithAdjoinPoint Geo F A) := by

  have hGenA :
      SmithSpan Geo (SmithAdjoinPoint Geo F A) =
        WylerPlaneCone Geo F P A :=
    hGen
      F hFlat
      P R
      hPF hRF hPR
      A hAOut

  have hGenB :
      SmithSpan Geo (SmithAdjoinPoint Geo F B) =
        WylerPlaneCone Geo F P B :=
    hGen
      F hFlat
      P R
      hPF hRF hPR
      B hBOut

  have hBinConeA :
      WylerPlaneCone Geo F P A B := by
    rw [← hGenA]
    exact hBinFA

  have hAinConeB :
      WylerPlaneCone Geo F P B A :=
    wylerPlaneCone_swap_apex
      (Geo := Geo)
      F P A B
      hBinConeA

  have hAinFB :
      SmithSpan Geo (SmithAdjoinPoint Geo F B) A := by
    rw [hGenB]
    exact hAinConeB

  apply Set.Subset.antisymm

  · apply
      smithSpan_least
        (Geo := Geo)
        (SmithAdjoinPoint Geo F B)
        (SmithSpan Geo (SmithAdjoinPoint Geo F A))
        (smithSpan_flat
          (Geo := Geo)
          (SmithAdjoinPoint Geo F A))

    intro X hX
    rcases hX with hXB | hXF

    · subst X
      exact hBinFA

    · apply
        smithSpan_extensive
          (Geo := Geo)
          (SmithAdjoinPoint Geo F A)

      exact Or.inr hXF

  · apply
      smithSpan_least
        (Geo := Geo)
        (SmithAdjoinPoint Geo F A)
        (SmithSpan Geo (SmithAdjoinPoint Geo F B))
        (smithSpan_flat
          (Geo := Geo)
          (SmithAdjoinPoint Geo F B))

    intro X hX
    rcases hX with hXA | hXF

    · subst X
      exact hAinFB

    · apply
        smithSpan_extensive
          (Geo := Geo)
          (SmithAdjoinPoint Geo F B)

      exact Or.inr hXF


/--
Generated-flat exchange restricted to base flats containing two distinct
points.
-/
def WylerGeneratedFlatExchangeOfTwoPoints
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    (exists P R : Geo.Point,
      F P /\ F R /\ Ne P R) ->
    forall A B : Geo.Point,
      Not (F A) ->
      Not (F B) ->
      SmithSpan Geo (SmithAdjoinPoint Geo F A) B ->
      SmithSpan Geo (SmithAdjoinPoint Geo F B) =
        SmithSpan Geo (SmithAdjoinPoint Geo F A)


/--
One-point generation implies exchange for every nondegenerate base flat.
-/
theorem wylerOnePointGenerationFormula_implies_exchange_nontrivial
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (hGen : WylerOnePointGenerationFormula Geo) :
    WylerGeneratedFlatExchangeOfTwoPoints Geo := by

  intro F hFlat hTwo A B hAOut hBOut hBinFA

  rcases hTwo with
    ⟨P, R, hPF, hRF, hPR⟩

  exact
    wylerOnePointGenerationFormula_implies_exchange_of_two_points
      (Geo := Geo)
      hGen
      F hFlat
      P R A B
      hPF hRF hPR
      hAOut hBOut
      hBinFA


/--
Smith I5 alone implies full flatness of every Wyler plane cone.
-/
theorem smithI5_implies_wylerPlaneConeFlatness
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hI5 : SmithI5Statement Geo) :
    WylerPlaneConeFlatness Geo := by

  have hP3 :
      WylerLocalP3AtPoint Geo :=
    smithI5_implies_localP3
      (Geo := Geo)
      hI5

  exact
    wylerLocalP3_and_SmithI5_implies_coneFlatness
      (Geo := Geo)
      hP3 hI5


/--
Smith I5 alone implies Wyler's one-point generation formula.
-/
theorem smithI5_implies_wylerOnePointGenerationFormula
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hI5 : SmithI5Statement Geo) :
    WylerOnePointGenerationFormula Geo := by

  have hP3 :
      WylerLocalP3AtPoint Geo :=
    smithI5_implies_localP3
      (Geo := Geo)
      hI5

  exact
    wylerLocalP3_and_SmithI5_implies_onePointGenerationFormula
      (Geo := Geo)
      hP3 hI5


/--
Smith I5 alone implies generated-flat exchange for every base flat
containing two distinct points.
-/
theorem smithI5_implies_exchange_nontrivial
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hI5 : SmithI5Statement Geo) :
    WylerGeneratedFlatExchangeOfTwoPoints Geo := by

  have hGen :
      WylerOnePointGenerationFormula Geo :=
    smithI5_implies_wylerOnePointGenerationFormula
      (Geo := Geo)
      hI5

  exact
    wylerOnePointGenerationFormula_implies_exchange_nontrivial
      (Geo := Geo)
      hGen


/--
Carrier consisting of one point.
-/
def SmithSingletonCarrier
    (A : Geo.Point) : Set Geo.Point :=
  fun X => X = A


/--
A singleton is a Smith flat.
-/
theorem smithSingletonCarrier_flat
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (A : Geo.Point) :
    SmithFlat Geo (SmithSingletonCarrier Geo A) := by

  constructor

  · intro X Y hXA hYA hXY
    subst X
    subst Y
    exact False.elim (hXY rfl)

  · intro X Y Z hXA hYA hZA hXYZ
    subst X
    subst Y
    subst Z

    rcases
        hilbert_line_through_point
          Geo A with
      ⟨l, hAl⟩

    exact
      False.elim
        (hXYZ
          ⟨l,
           hAl,
           hAl,
           hAl⟩)


/--
Carrier of one ambient line.
-/
def SmithLineCarrier
    [H : HilbertIncidence Geo]
    (l : Geo.Line) : Set Geo.Point :=
  fun X => H.OnLine X l


/--
The carrier of every ambient line is a Smith flat.
-/
theorem smithLineCarrier_flat
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l : Geo.Line) :
    SmithFlat Geo (SmithLineCarrier Geo l) := by

  constructor

  · intro A B hAl hBl hAB m hAm hBm X hXm

    have hml : m = l :=
      HilbertPlaneIncidence.line_unique
        A B hAB
        m l
        hAm hBm
        hAl hBl

    rw [← hml]
    exact hXm

  · intro A B C hAl hBl hCl hABC

    exact
      False.elim
        (hABC
          ⟨l,
           hAl,
           hBl,
           hCl⟩)


/--
Exchange for nondegenerate base flats implies full Wyler generated-flat
exchange.  The remaining base flats are empty or singletons.
-/
theorem exchange_nontrivial_implies_wylerGeneratedFlatExchange
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (hNontrivial : WylerGeneratedFlatExchangeOfTwoPoints Geo) :
    WylerGeneratedFlatExchange Geo := by

  intro F hFlat A B hAOut hBOut hBinFA

  by_cases hTwo :
      exists P R : Geo.Point,
        F P /\ F R /\ Ne P R

  · exact
      hNontrivial
        F hFlat hTwo
        A B
        hAOut hBOut
        hBinFA

  · by_cases hPoint :
      exists R : Geo.Point, F R

    · rcases hPoint with
        ⟨R, hRF⟩

      have hRA : Ne R A := by
        intro hRA
        subst A
        exact hAOut hRF

      rcases
          HilbertPlaneIncidence.line_through
            (Geo := Geo)
            R A hRA with
        ⟨l, hRl, hAl⟩

      have hFOnL :
          forall T : Geo.Point,
            F T ->
            H.OnLine T l := by

        intro T hTF

        have hTR : T = R := by
          by_contra hTR

          exact
            hTwo
              ⟨T, R,
               hTF,
               hRF,
               hTR⟩

        subst T
        exact hRl

      have hAdjoinFASubLine :
          Set.Subset
            (SmithAdjoinPoint Geo F A)
            (SmithLineCarrier Geo l) := by

        intro T hT
        rcases hT with hTA | hTF

        · subst T
          exact hAl

        · exact hFOnL T hTF

      have hBl : H.OnLine B l :=
        hBinFA
          (SmithLineCarrier Geo l)
          (smithLineCarrier_flat
            (Geo := Geo)
            l)
          hAdjoinFASubLine

      have hRB : Ne R B := by
        intro hRB
        subst B
        exact hBOut hRF

      have hRInFB :
          SmithSpan Geo
            (SmithAdjoinPoint Geo F B) R :=
        smithSpan_extensive
          (Geo := Geo)
          (SmithAdjoinPoint Geo F B)
          (Or.inr hRF)

      have hBInFB :
          SmithSpan Geo
            (SmithAdjoinPoint Geo F B) B :=
        smithSpan_extensive
          (Geo := Geo)
          (SmithAdjoinPoint Geo F B)
          (Or.inl rfl)

      have hAInFB :
          SmithSpan Geo
            (SmithAdjoinPoint Geo F B) A :=
        (smithSpan_flat
          (Geo := Geo)
          (SmithAdjoinPoint Geo F B)).1
            R B
            hRInFB hBInFB
            hRB
            l hRl hBl
            A hAl

      apply Set.Subset.antisymm

      · apply
          smithSpan_least
            (Geo := Geo)
            (SmithAdjoinPoint Geo F B)
            (SmithSpan Geo
              (SmithAdjoinPoint Geo F A))
            (smithSpan_flat
              (Geo := Geo)
              (SmithAdjoinPoint Geo F A))

        intro T hT
        rcases hT with hTB | hTF

        · subst T
          exact hBinFA

        · exact
            smithSpan_extensive
              (Geo := Geo)
              (SmithAdjoinPoint Geo F A)
              (Or.inr hTF)

      · apply
          smithSpan_least
            (Geo := Geo)
            (SmithAdjoinPoint Geo F A)
            (SmithSpan Geo
              (SmithAdjoinPoint Geo F B))
            (smithSpan_flat
              (Geo := Geo)
              (SmithAdjoinPoint Geo F B))

        intro T hT
        rcases hT with hTA | hTF

        · subst T
          exact hAInFB

        · exact
            smithSpan_extensive
              (Geo := Geo)
              (SmithAdjoinPoint Geo F B)
              (Or.inr hTF)

    · have hAdjoinFASubSingleton :
          Set.Subset
            (SmithAdjoinPoint Geo F A)
            (SmithSingletonCarrier Geo A) := by

        intro T hT
        rcases hT with hTA | hTF

        · exact hTA

        · exact
            False.elim
              (hPoint
                ⟨T, hTF⟩)

      have hBA : B = A :=
        hBinFA
          (SmithSingletonCarrier Geo A)
          (smithSingletonCarrier_flat
            (Geo := Geo)
            A)
          hAdjoinFASubSingleton

      subst B
      rfl


/--
Smith I5 alone implies full Wyler generated-flat exchange.
-/
theorem smithI5_implies_wylerGeneratedFlatExchange
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hI5 : SmithI5Statement Geo) :
    WylerGeneratedFlatExchange Geo := by

  have hNontrivial :
      WylerGeneratedFlatExchangeOfTwoPoints Geo :=
    smithI5_implies_exchange_nontrivial
      (Geo := Geo)
      hI5

  exact
    exchange_nontrivial_implies_wylerGeneratedFlatExchange
      (Geo := Geo)
      hNontrivial


/--
Smith I5 alone implies the full Steinitz exchange law for Smith span.
-/
theorem smithI5_implies_smithSpanExchange
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hI5 : SmithI5Statement Geo) :
    SmithSpanExchange Geo := by

  have hWyler :
      WylerGeneratedFlatExchange Geo :=
    smithI5_implies_wylerGeneratedFlatExchange
      (Geo := Geo)
      hI5

  exact
    wylerGeneratedFlatExchange_implies_smithSpanExchange
      (Geo := Geo)
      hWyler


/--
Final production theorem: the dimension-free Hilbert/Smith incidence
package implies the full Steinitz exchange law for `SmithSpan`.

No independent exchange axiom is assumed.
-/
theorem dimensionFreeIncidence_implies_smithSpanExchange
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo] :
    SmithSpanExchange Geo := by

  exact
    @smithI5_implies_smithSpanExchange
      Geo
      H
      (inferInstance : HilbertPlaneIncidence Geo)
      S
      (smithIncidenceCore_of_dimensionFree
        (Geo := Geo))
      D.smith_i5

end Geometry

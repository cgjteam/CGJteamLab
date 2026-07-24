import CGJteamLab.SuppesIntersection
import CGJteamLab.MidsegmentParallelSuppes
import CGJteamLab.SuppesPCGCompatibility

namespace Geometry
namespace Suppes

universe u

variable {Point : Type u}
variable [SuppesGeometry Point]
variable [SuppesPCG Point]
variable [SuppesPCGCompatibility Point]

local notation "Mid" =>
  (SuppesGeometry.operation_midpoint (Point := Point))

omit [SuppesPCGCompatibility Point] in
theorem FinlaySuppesStep1
    (A B C : Point) :
    True := by

  let E : Point := Mid A C
  let F : Point := Mid A B

  let G : Point :=
    SuppesPCG.intersection
      (Point := Point)
      B E C F

  trivial

theorem FinlaySuppesStep2
    (A B C : Point)
    (hT : PrimTriangle A B C) :
    let E := Mid A C
    let F := Mid A B
    let G :=
      SuppesPCG.intersection
        (Point := Point)
        B E C F
    PCGCollinear B E G ∧
    PCGCollinear C F G := by

  dsimp

  let E : Point := Mid A C
  let F : Point := Mid A B

  let G : Point :=
    SuppesPCG.intersection
      (Point := Point)
      B E C F

  -- Auxiliary construction for the left median BE.
  let P : Point :=
    SuppesPCG.segmentConstruction
      (Point := Point)
      B E C F

  let Q : Point :=
    SuppesPCG.intersection
      (Point := Point)
      B P E C

  -- Auxiliary construction for the right median CF.
  let P2 : Point :=
    SuppesPCG.segmentConstruction
      (Point := Point)
      C F B E

  let Q2 : Point :=
    SuppesPCG.intersection
      (Point := Point)
      C P2 F B


  have hNLLeft :
      PCGNoncollinear4 B E C F := by

    unfold PCGNoncollinear4
    refine ⟨?_, ?_, ?_, ?_⟩

    · -- 1. ¬ PCGCollinear B E C
      intro hBEC

      have hBEC' :
          SuppesGeometry.Collinear B E C :=
        (SuppesPCGCompatibility.collinear_iff B E C).mpr hBEC

      have hECB :
          SuppesGeometry.Collinear E C B :=
        collinear_rotate hBEC'

      have hACE :
          SuppesGeometry.Collinear A C E :=
        midpoint_collinear A C

      have hECA :
          SuppesGeometry.Collinear E C A := by
        have hCAE :
            SuppesGeometry.Collinear C A E :=
          collinear_swap hACE

        have hAEC :
            SuppesGeometry.Collinear A E C :=
          collinear_rotate hCAE

        exact collinear_rotate hAEC

      have hEC : E ≠ C := by
        intro hEq

        have hMid :
            Mid C A = Mid C C := by
          calc
            Mid C A = Mid A C :=
              midpoint_commutative C A
            _ = E := by
              rfl
            _ = C :=
              hEq
            _ = Mid C C :=
              (midpoint_idempotent C).symm

        have hAC : A = C :=
          midpoint_cancellation C A C hMid

        apply hT
        apply L2
        exact Or.inr (Or.inl hAC)

      apply hT
      apply L3 E C A B C
      · exact hEC
      · exact hECA
      · exact hECB
      · apply L2
        exact Or.inr (Or.inr rfl)


    · -- 2. ¬ PCGCollinear E C F
      intro hECF

      have hECF' :
          SuppesGeometry.Collinear E C F :=
        (SuppesPCGCompatibility.collinear_iff E C F).mpr hECF

      have hEC : E ≠ C := by
        intro hEq

        have hMid :
            Mid C A = Mid C C := by
          calc
            Mid C A = Mid A C :=
              midpoint_commutative C A
            _ = E := by
              rfl
            _ = C :=
              hEq
            _ = Mid C C :=
              (midpoint_idempotent C).symm

        have hAC : A = C :=
          midpoint_cancellation C A C hMid

        apply hT
        apply L2
        exact Or.inr (Or.inl hAC)

      have hACE :
          SuppesGeometry.Collinear A C E :=
        midpoint_collinear A C

      have hECA :
          SuppesGeometry.Collinear E C A := by
        have hCAE :
            SuppesGeometry.Collinear C A E :=
          collinear_swap hACE
        have hAEC :
            SuppesGeometry.Collinear A E C :=
          collinear_rotate hCAE
        exact collinear_rotate hAEC

      have hAFC :
          SuppesGeometry.Collinear A F C := by
        apply L3 E C A F C
        · exact hEC
        · exact hECA
        · exact hECF'
        · apply L2
          exact Or.inr (Or.inr rfl)

      have hAF : A ≠ F := by
        intro hEq

        have hMid :
            Mid A B = Mid A A := by
          calc
            Mid A B = F := by
              rfl
            _ = A :=
              hEq.symm
            _ = Mid A A :=
              (midpoint_idempotent A).symm

        have hBA : B = A :=
          midpoint_cancellation A B A hMid

        apply hT
        apply L2
        exact Or.inl hBA.symm

      have hABF :
          SuppesGeometry.Collinear A B F :=
        midpoint_collinear A B

      have hAFB :
          SuppesGeometry.Collinear A F B := by
        have hBFA :
            SuppesGeometry.Collinear B F A :=
          collinear_rotate hABF
        have hFAB :
            SuppesGeometry.Collinear F A B :=
          collinear_rotate hBFA
        exact collinear_swap hFAB

      have hBCA :
          SuppesGeometry.Collinear B C A := by
        apply L3 A F B C A
        · exact hAF
        · exact hAFB
        · exact hAFC
        · apply L2
          exact Or.inr (Or.inl rfl)

      have hCAB :
          SuppesGeometry.Collinear C A B :=
        collinear_rotate hBCA

      have hABC :
          SuppesGeometry.Collinear A B C :=
        collinear_rotate hCAB

      exact hT hABC


    · -- 3. ¬ PCGCollinear B C F
      intro hBCF

      have hBCF' :
          SuppesGeometry.Collinear B C F :=
        (SuppesPCGCompatibility.collinear_iff B C F).mpr hBCF

      have hABF :
          SuppesGeometry.Collinear A B F :=
        midpoint_collinear A B

      have hBFA :
          SuppesGeometry.Collinear B F A :=
        collinear_rotate hABF

      have hBFC :
          SuppesGeometry.Collinear B F C := by
        exact collinear_rotate (collinear_swap hBCF')

      have hBF : B ≠ F := by
        intro hEq

        have hMid :
            Mid B A = Mid B B := by
          calc
            Mid B A = Mid A B :=
              midpoint_commutative B A
            _ = F := by
              rfl
            _ = B :=
              hEq.symm
            _ = Mid B B :=
              (midpoint_idempotent B).symm

        have hAB : A = B :=
          midpoint_cancellation B A B hMid

        apply hT
        apply L2
        exact Or.inl hAB

      apply hT
      apply L3 B F A B C
      · exact hBF
      · exact hBFA
      · apply L2
        exact Or.inr (Or.inl rfl)
      · exact hBFC


    · -- 4. ¬ PCGCollinear B E F
      intro hBEF

      have hBEF' :
          SuppesGeometry.Collinear B E F :=
        (SuppesPCGCompatibility.collinear_iff B E F).mpr hBEF

      have hABF :
          SuppesGeometry.Collinear A B F :=
        midpoint_collinear A B

      have hBFA :
          SuppesGeometry.Collinear B F A :=
        collinear_rotate hABF

      have hBFE :
          SuppesGeometry.Collinear B F E := by
        exact collinear_rotate (collinear_swap hBEF')

      have hBF : B ≠ F := by
        intro hEq

        have hMid :
            Mid B A = Mid B B := by
          calc
            Mid B A = Mid A B :=
              midpoint_commutative B A
            _ = F := by
              rfl
            _ = B :=
              hEq.symm
            _ = Mid B B :=
              (midpoint_idempotent B).symm

        have hAB : A = B :=
          midpoint_cancellation B A B hMid

        apply hT
        apply L2
        exact Or.inl hAB

      have hAEB :
          SuppesGeometry.Collinear A E B := by
        apply L3 B F A E B
        · exact hBF
        · exact hBFA
        · exact hBFE
        · apply L2
          exact Or.inr (Or.inl rfl)

      have hACE :
          SuppesGeometry.Collinear A C E :=
        midpoint_collinear A C

      have hAEC :
          SuppesGeometry.Collinear A E C := by
        have hCAE :
            SuppesGeometry.Collinear C A E :=
          collinear_swap hACE
        exact collinear_rotate hCAE

      have hAE : A ≠ E := by
        intro hEq

        have hMid :
            Mid A C = Mid A A := by
          calc
            Mid A C = E := by
              rfl
            _ = A :=
              hEq.symm
            _ = Mid A A :=
              (midpoint_idempotent A).symm

        have hCA : C = A :=
          midpoint_cancellation A C A hMid

        apply hT
        apply L2
        exact Or.inr (Or.inl hCA.symm)

      apply hT
      apply L3 A E A B C
      · exact hAE
      · apply L2
        exact Or.inr (Or.inl rfl)
      · exact hAEB
      · exact hAEC


  have hBetweenLeft :
      PCGBetween B Q P := by
    unfold PCGBetween
    constructor

    · intro hBP
      constructor

      · -- S(B,Q,B,P) = Q


      · -- S(P,Q,P,B) = Q
        sorry

    · intro hBP
      -- B = P -> B = Q
      sorry

  have hDirLeft :
      SuppesPCG.segmentConstruction
          (Point := Point)
          E P B C
        ≠ C := by
    sorry

  have hLeft :
      PCGCollinear B E G := by

    have hRaw :=
      euclid_intersection_collinear
        B E C F
        hNLLeft
        hBetweenLeft
        hDirLeft

    change PCGCollinear B E G at hRaw
    exact hRaw


  refine ⟨hLeft, ?_⟩


  have hNLRight :
      PCGNoncollinear4 C F B E := by
    sorry

  have hBetweenRight :
      PCGBetween C Q2 P2 := by
    sorry

  have hDirRight :
      SuppesPCG.segmentConstruction
          (Point := Point)
          F P2 C B
        ≠ B := by
    sorry

  have hRightRaw :=
    euclid_intersection_collinear
      C F B E
      hNLRight
      hBetweenRight
      hDirRight

  have hRight :
      PCGCollinear C F
        (SuppesPCG.intersection
          (Point := Point) C F B E) := by
    exact hRightRaw

  have hComm :
      SuppesPCG.intersection
          (Point := Point) B E C F =
      SuppesPCG.intersection
          (Point := Point) C F B E :=
    intersection_comm_lines B E C F

  rw [hComm]

  change PCGCollinear C F
    (SuppesPCG.intersection
      (Point := Point) C F B E)

  exact hRight

end Suppes
end Geometry
